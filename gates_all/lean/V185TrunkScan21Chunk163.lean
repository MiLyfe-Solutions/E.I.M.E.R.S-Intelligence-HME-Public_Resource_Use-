import V185TrunkScan21Chunk162

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1987459 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 4]
def baseStart_1987459 : Nat := 118140960795 + 1987459 * 2 ^ 59
def prefixEnd_1987459 : Nat := 4983230072969 + 3 ^ 40 * 1987459 * 2
def baseEnd_1987459 : Nat := 453565221379664351654377

theorem tailTrace_1987459 : CollatzResearch.WordTrace tailWord_1987459 prefixEnd_1987459 453565221379664351654377 := by
  unfold tailWord_1987459
  simp only [CollatzResearch.WordTrace]
  refine ⟨72488584906782948818829431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48325723271188632545886287 72488584906782948818829431)
  ·
    refine ⟨108732877360174423228244147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72488584906782948818829431 108732877360174423228244147)
    ·
      refine ⟨163099316040261634842366221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108732877360174423228244147 163099316040261634842366221)
      ·
        refine ⟨61162243515098113065887333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163099316040261634842366221 61162243515098113065887333)
        ·
          refine ⟨11467920659080896199853875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61162243515098113065887333 11467920659080896199853875)
          ·
            refine ⟨17201880988621344299780813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11467920659080896199853875 17201880988621344299780813)
            ·
              refine ⟨6450705370733004112417805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17201880988621344299780813 6450705370733004112417805)
              ·
                refine ⟨2419014514024876542156677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6450705370733004112417805 2419014514024876542156677)
                ·
                  refine ⟨453565221379664351654377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419014514024876542156677 453565221379664351654377)
                  ·
                    rfl

theorem cell21_1987459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 4].length) (baseStart_1987459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987459 prefixEnd_1987459 := by exact prefixLift 1987459
  have htrace : WordTrace (prefixWord ++ tailWord_1987459) baseStart_1987459 baseEnd_1987459 := by
    simpa [prefixWord, tailWord_1987459, baseEnd_1987459] using wordTrace_append hprefix tailTrace_1987459
  have hstable : (prefixWord ++ tailWord_1987459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987459).length < 2 ^ (prefixWord ++ tailWord_1987459).sum := by decide
  have hdescent : baseEnd_1987459 < baseStart_1987459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987524 : List Nat := [2, 3, 3, 3, 1, 1, 3, 5]
def baseStart_1987524 : Nat := 118140960795 + 1987524 * 2 ^ 59
def prefixEnd_1987524 : Nat := 4983230072969 + 3 ^ 40 * 1987524 * 2
def baseEnd_1987524 : Nat := 151193351755079561023637

theorem tailTrace_1987524 : CollatzResearch.WordTrace tailWord_1987524 prefixEnd_1987524 151193351755079561023637 := by
  unfold tailWord_1987524
  simp only [CollatzResearch.WordTrace]
  refine ⟨36245477825773732459972813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48327303767698309946630417 36245477825773732459972813)
  ·
    refine ⟨13592054184665149672489805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36245477825773732459972813 13592054184665149672489805)
    ·
      refine ⟨5097020319249431127183677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13592054184665149672489805 5097020319249431127183677)
      ·
        refine ⟨1911382619718536672693879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5097020319249431127183677 1911382619718536672693879)
        ·
          refine ⟨2867073929577805009040819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911382619718536672693879 2867073929577805009040819)
          ·
            refine ⟨4300610894366707513561229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867073929577805009040819 4300610894366707513561229)
            ·
              refine ⟨1612729085387515317585461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4300610894366707513561229 1612729085387515317585461)
              ·
                refine ⟨151193351755079561023637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1612729085387515317585461 151193351755079561023637)
                ·
                  rfl

theorem cell21_1987524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_1987524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987524 prefixEnd_1987524 := by exact prefixLift 1987524
  have htrace : WordTrace (prefixWord ++ tailWord_1987524) baseStart_1987524 baseEnd_1987524 := by
    simpa [prefixWord, tailWord_1987524, baseEnd_1987524] using wordTrace_append hprefix tailTrace_1987524
  have hstable : (prefixWord ++ tailWord_1987524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987524).length < 2 ^ (prefixWord ++ tailWord_1987524).sum := by decide
  have hdescent : baseEnd_1987524 < baseStart_1987524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987538 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_1987538 : Nat := 118140960795 + 1987538 * 2 ^ 59
def prefixEnd_1987538 : Nat := 4983230072969 + 3 ^ 40 * 1987538 * 2
def baseEnd_1987538 : Nat := 453583250255977769837549

theorem tailTrace_1987538 : CollatzResearch.WordTrace tailWord_1987538 prefixEnd_1987538 453583250255977769837549 := by
  unfold tailWord_1987538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18122866568374186327738817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48327644182331163540636845 18122866568374186327738817)
  ·
    refine ⟨13592149926280639745804113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18122866568374186327738817 13592149926280639745804113)
    ·
      refine ⟨10194112444710479809353085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13592149926280639745804113 10194112444710479809353085)
      ·
        refine ⟨3822792166766429928507407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10194112444710479809353085 3822792166766429928507407)
        ·
          refine ⟨5734188250149644892761111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3822792166766429928507407 5734188250149644892761111)
          ·
            refine ⟨8601282375224467339141667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734188250149644892761111 8601282375224467339141667)
            ·
              refine ⟨12901923562836701008712501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601282375224467339141667 12901923562836701008712501)
              ·
                refine ⟨1209555334015940719566797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12901923562836701008712501 1209555334015940719566797)
                ·
                  refine ⟨453583250255977769837549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209555334015940719566797 453583250255977769837549)
                  ·
                    rfl

theorem cell21_1987538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_1987538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987538 prefixEnd_1987538 := by exact prefixLift 1987538
  have htrace : WordTrace (prefixWord ++ tailWord_1987538) baseStart_1987538 baseEnd_1987538 := by
    simpa [prefixWord, tailWord_1987538, baseEnd_1987538] using wordTrace_append hprefix tailTrace_1987538
  have hstable : (prefixWord ++ tailWord_1987538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987538).length < 2 ^ (prefixWord ++ tailWord_1987538).sum := by decide
  have hdescent : baseEnd_1987538 < baseStart_1987538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987580 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1987580 : Nat := 118140960795 + 1987580 * 2 ^ 59
def prefixEnd_1987580 : Nat := 4983230072969 + 3 ^ 40 * 1987580 * 2
def baseEnd_1987580 : Nat := 453592835228195030137463

theorem tailTrace_1987580 : CollatzResearch.WordTrace tailWord_1987580 prefixEnd_1987580 453592835228195030137463 := by
  unfold tailWord_1987580
  simp only [CollatzResearch.WordTrace]
  refine ⟨36246499069672293241992097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48328665426229724322656129 36246499069672293241992097)
  ·
    refine ⟨27184874302254219931494073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36246499069672293241992097 27184874302254219931494073)
    ·
      refine ⟨20388655726690664948620555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27184874302254219931494073 20388655726690664948620555)
      ·
        refine ⟨30582983590035997422930833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20388655726690664948620555 30582983590035997422930833)
        ·
          refine ⟨22937237692526998067198125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30582983590035997422930833 22937237692526998067198125)
          ·
            refine ⟨8601464134697624275199297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22937237692526998067198125 8601464134697624275199297)
            ·
              refine ⟨6451098101023218206399473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8601464134697624275199297 6451098101023218206399473)
              ·
                refine ⟨4838323575767413654799605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451098101023218206399473 4838323575767413654799605)
                ·
                  refine ⟨453592835228195030137463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4838323575767413654799605 453592835228195030137463)
                  ·
                    rfl

theorem cell21_1987580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1987580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987580 prefixEnd_1987580 := by exact prefixLift 1987580
  have htrace : WordTrace (prefixWord ++ tailWord_1987580) baseStart_1987580 baseEnd_1987580 := by
    simpa [prefixWord, tailWord_1987580, baseEnd_1987580] using wordTrace_append hprefix tailTrace_1987580
  have hstable : (prefixWord ++ tailWord_1987580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987580).length < 2 ^ (prefixWord ++ tailWord_1987580).sum := by decide
  have hdescent : baseEnd_1987580 < baseStart_1987580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987639 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 7]
def baseStart_1987639 : Nat := 118140960795 + 1987639 * 2 ^ 59
def prefixEnd_1987639 : Nat := 4983230072969 + 3 ^ 40 * 1987639 * 2
def baseEnd_1987639 : Nat := 453606299832024038654009

theorem tailTrace_1987639 : CollatzResearch.WordTrace tailWord_1987639 prefixEnd_1987639 453606299832024038654009 := by
  unfold tailWord_1987639
  simp only [CollatzResearch.WordTrace]
  refine ⟨72495150046130839560381971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48330100030753893040254647 72495150046130839560381971)
  ·
    refine ⟨108742725069196259340572957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72495150046130839560381971 108742725069196259340572957)
    ·
      refine ⟨40778521900948597252714859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108742725069196259340572957 40778521900948597252714859)
      ·
        refine ⟨61167782851422895879072289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40778521900948597252714859 61167782851422895879072289)
        ·
          refine ⟨45875837138567171909304217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61167782851422895879072289 45875837138567171909304217)
          ·
            refine ⟨34406877853925378931978163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45875837138567171909304217 34406877853925378931978163)
            ·
              refine ⟨51610316780888068397967245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34406877853925378931978163 51610316780888068397967245)
              ·
                refine ⟨19353868792833025649237717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51610316780888068397967245 19353868792833025649237717)
                ·
                  refine ⟨453606299832024038654009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19353868792833025649237717 453606299832024038654009)
                  ·
                    rfl

theorem cell21_1987639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_1987639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987639 prefixEnd_1987639 := by exact prefixLift 1987639
  have htrace : WordTrace (prefixWord ++ tailWord_1987639) baseStart_1987639 baseEnd_1987639 := by
    simpa [prefixWord, tailWord_1987639, baseEnd_1987639] using wordTrace_append hprefix tailTrace_1987639
  have hstable : (prefixWord ++ tailWord_1987639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987639).length < 2 ^ (prefixWord ++ tailWord_1987639).sum := by decide
  have hdescent : baseEnd_1987639 < baseStart_1987639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987687 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 4]
def baseStart_1987687 : Nat := 118140960795 + 1987687 * 2 ^ 59
def prefixEnd_1987687 : Nat := 4983230072969 + 3 ^ 40 * 1987687 * 2
def baseEnd_1987687 : Nat := 453617254085986621853911

theorem tailTrace_1987687 : CollatzResearch.WordTrace tailWord_1987687 prefixEnd_1987687 453617254085986621853911 := by
  unfold tailWord_1987687
  simp only [CollatzResearch.WordTrace]
  refine ⟨72496900749956943758129315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48331267166637962505419543 72496900749956943758129315)
  ·
    refine ⟨108745351124935415637193973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72496900749956943758129315 108745351124935415637193973)
    ·
      refine ⟨10194876667962695215986935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108745351124935415637193973 10194876667962695215986935)
      ·
        refine ⟨15292315001944042823980403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10194876667962695215986935 15292315001944042823980403)
        ·
          refine ⟨22938472502916064235970605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15292315001944042823980403 22938472502916064235970605)
          ·
            refine ⟨8601927188593524088488977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22938472502916064235970605 8601927188593524088488977)
            ·
              refine ⟨6451445391445143066366733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8601927188593524088488977 6451445391445143066366733)
              ·
                refine ⟨2419292021791928649887525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6451445391445143066366733 2419292021791928649887525)
                ·
                  refine ⟨453617254085986621853911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419292021791928649887525 453617254085986621853911)
                  ·
                    rfl

theorem cell21_1987687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 4].length) (baseStart_1987687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987687 prefixEnd_1987687 := by exact prefixLift 1987687
  have htrace : WordTrace (prefixWord ++ tailWord_1987687) baseStart_1987687 baseEnd_1987687 := by
    simpa [prefixWord, tailWord_1987687, baseEnd_1987687] using wordTrace_append hprefix tailTrace_1987687
  have hstable : (prefixWord ++ tailWord_1987687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987687).length < 2 ^ (prefixWord ++ tailWord_1987687).sum := by decide
  have hdescent : baseEnd_1987687 < baseStart_1987687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987715 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 7]
def baseStart_1987715 : Nat := 118140960795 + 1987715 * 2 ^ 59
def prefixEnd_1987715 : Nat := 4983230072969 + 3 ^ 40 * 1987715 * 2
def baseEnd_1987715 : Nat := 453623644067464795387187

theorem tailTrace_1987715 : CollatzResearch.WordTrace tailWord_1987715 prefixEnd_1987715 453623644067464795387187 := by
  unfold tailWord_1987715
  simp only [CollatzResearch.WordTrace]
  refine ⟨72497921993855504540148599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48331947995903669693432399 72497921993855504540148599)
  ·
    refine ⟨108746882990783256810222899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72497921993855504540148599 108746882990783256810222899)
    ·
      refine ⟨163120324486174885215334349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108746882990783256810222899 163120324486174885215334349)
      ·
        refine ⟨61170121682315581955750381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163120324486174885215334349 61170121682315581955750381)
        ·
          refine ⟨22938795630868343233406393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61170121682315581955750381 22938795630868343233406393)
          ·
            refine ⟨17204096723151257425054795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22938795630868343233406393 17204096723151257425054795)
            ·
              refine ⟨25806145084726886137582193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17204096723151257425054795 25806145084726886137582193)
              ·
                refine ⟨19354608813545164603186645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25806145084726886137582193 19354608813545164603186645)
                ·
                  refine ⟨453623644067464795387187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19354608813545164603186645 453623644067464795387187)
                  ·
                    rfl

theorem cell21_1987715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_1987715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987715 prefixEnd_1987715 := by exact prefixLift 1987715
  have htrace : WordTrace (prefixWord ++ tailWord_1987715) baseStart_1987715 baseEnd_1987715 := by
    simpa [prefixWord, tailWord_1987715, baseEnd_1987715] using wordTrace_append hprefix tailTrace_1987715
  have hstable : (prefixWord ++ tailWord_1987715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987715).length < 2 ^ (prefixWord ++ tailWord_1987715).sum := by decide
  have hdescent : baseEnd_1987715 < baseStart_1987715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987760 : List Nat := [2, 1, 1, 1, 2, 1, 2, 11]
def baseStart_1987760 : Nat := 118140960795 + 1987760 * 2 ^ 59
def prefixEnd_1987760 : Nat := 4983230072969 + 3 ^ 40 * 1987760 * 2
def baseEnd_1987760 : Nat := 151211304560184905712365

theorem tailTrace_1987760 : CollatzResearch.WordTrace tailWord_1987760 prefixEnd_1987760 151211304560184905712365 := by
  unfold tailWord_1987760
  simp only [CollatzResearch.WordTrace]
  refine ⟨36249781639346238612768367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48333042185794984817024489 36249781639346238612768367)
  ·
    refine ⟨54374672459019357919152551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36249781639346238612768367 54374672459019357919152551)
    ·
      refine ⟨81562008688529036878728827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54374672459019357919152551 81562008688529036878728827)
      ·
        refine ⟨122343013032793555318093241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81562008688529036878728827 122343013032793555318093241)
        ·
          refine ⟨91757259774595166488569931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122343013032793555318093241 91757259774595166488569931)
          ·
            refine ⟨137635889661892749732854897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91757259774595166488569931 137635889661892749732854897)
            ·
              refine ⟨103226917246419562299641173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137635889661892749732854897 103226917246419562299641173)
              ·
                refine ⟨151211304560184905712365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103226917246419562299641173 151211304560184905712365)
                ·
                  rfl

theorem cell21_1987760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_1987760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987760 prefixEnd_1987760 := by exact prefixLift 1987760
  have htrace : WordTrace (prefixWord ++ tailWord_1987760) baseStart_1987760 baseEnd_1987760 := by
    simpa [prefixWord, tailWord_1987760, baseEnd_1987760] using wordTrace_append hprefix tailTrace_1987760
  have hstable : (prefixWord ++ tailWord_1987760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987760).length < 2 ^ (prefixWord ++ tailWord_1987760).sum := by decide
  have hdescent : baseEnd_1987760 < baseStart_1987760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987791 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_1987791 : Nat := 118140960795 + 1987791 * 2 ^ 59
def prefixEnd_1987791 : Nat := 4983230072969 + 3 ^ 40 * 1987791 * 2
def baseEnd_1987791 : Nat := 453640988302905552120365

theorem tailTrace_1987791 : CollatzResearch.WordTrace tailWord_1987791 prefixEnd_1987791 453640988302905552120365 := by
  unfold tailWord_1987791
  simp only [CollatzResearch.WordTrace]
  refine ⟨72500693941580169519915227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48333795961053446346610151 72500693941580169519915227)
  ·
    refine ⟨108751040912370254279872841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72500693941580169519915227 108751040912370254279872841)
    ·
      refine ⟨81563280684277690709904631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108751040912370254279872841 81563280684277690709904631)
      ·
        refine ⟨122344921026416536064856947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81563280684277690709904631 122344921026416536064856947)
        ·
          refine ⟨183517381539624804097285421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122344921026416536064856947 183517381539624804097285421)
          ·
            refine ⟨68819018077359301536482033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183517381539624804097285421 68819018077359301536482033)
            ·
              refine ⟨51614263558019476152361525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68819018077359301536482033 51614263558019476152361525)
              ·
                refine ⟨4838837208564325889283893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51614263558019476152361525 4838837208564325889283893)
                ·
                  refine ⟨453640988302905552120365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4838837208564325889283893 453640988302905552120365)
                  ·
                    rfl

theorem cell21_1987791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_1987791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987791 prefixEnd_1987791 := by exact prefixLift 1987791
  have htrace : WordTrace (prefixWord ++ tailWord_1987791) baseStart_1987791 baseEnd_1987791 := by
    simpa [prefixWord, tailWord_1987791, baseEnd_1987791] using wordTrace_append hprefix tailTrace_1987791
  have hstable : (prefixWord ++ tailWord_1987791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987791).length < 2 ^ (prefixWord ++ tailWord_1987791).sum := by decide
  have hdescent : baseEnd_1987791 < baseStart_1987791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987797 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 4]
def baseStart_1987797 : Nat := 118140960795 + 1987797 * 2 ^ 59
def prefixEnd_1987797 : Nat := 4983230072969 + 3 ^ 40 * 1987797 * 2
def baseEnd_1987797 : Nat := 453642357584650875020353

theorem tailTrace_1987797 : CollatzResearch.WordTrace tailWord_1987797 prefixEnd_1987797 453642357584650875020353 := by
  unfold tailWord_1987797
  simp only [CollatzResearch.WordTrace]
  refine ⟨72500912779558432544633645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48333941853038955029755763 72500912779558432544633645)
  ·
    refine ⟨27187842292334412204237617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72500912779558432544633645 27187842292334412204237617)
    ·
      refine ⟨20390881719250809153178213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27187842292334412204237617 20390881719250809153178213)
      ·
        refine ⟨3823290322359526716220915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20390881719250809153178213 3823290322359526716220915)
        ·
          refine ⟨5734935483539290074331373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823290322359526716220915 5734935483539290074331373)
          ·
            refine ⟨2150600806327233777874265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5734935483539290074331373 2150600806327233777874265)
            ·
              refine ⟨1612950604745425333405699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150600806327233777874265 1612950604745425333405699)
              ·
                refine ⟨2419425907118138000108549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612950604745425333405699 2419425907118138000108549)
                ·
                  refine ⟨453642357584650875020353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419425907118138000108549 453642357584650875020353)
                  ·
                    rfl

theorem cell21_1987797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_1987797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987797 prefixEnd_1987797 := by exact prefixLift 1987797
  have htrace : WordTrace (prefixWord ++ tailWord_1987797) baseStart_1987797 baseEnd_1987797 := by
    simpa [prefixWord, tailWord_1987797, baseEnd_1987797] using wordTrace_append hprefix tailTrace_1987797
  have hstable : (prefixWord ++ tailWord_1987797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987797).length < 2 ^ (prefixWord ++ tailWord_1987797).sum := by decide
  have hdescent : baseEnd_1987797 < baseStart_1987797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987822 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1987822 : Nat := 118140960795 + 1987822 * 2 ^ 59
def prefixEnd_1987822 : Nat := 4983230072969 + 3 ^ 40 * 1987822 * 2
def baseEnd_1987822 : Nat := 453648062925256387103635

theorem tailTrace_1987822 : CollatzResearch.WordTrace tailWord_1987822 prefixEnd_1987822 453648062925256387103635 := by
  unfold tailWord_1987822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9062728075558482726786715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48334549736311907876195813 9062728075558482726786715)
  ·
    refine ⟨13594092113337724090180073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9062728075558482726786715 13594092113337724090180073)
    ·
      refine ⟨10195569085003293067635055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13594092113337724090180073 10195569085003293067635055)
      ·
        refine ⟨15293353627504939601452583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10195569085003293067635055 15293353627504939601452583)
        ·
          refine ⟨22940030441257409402178875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15293353627504939601452583 22940030441257409402178875)
          ·
            refine ⟨34410045661886114103268313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22940030441257409402178875 34410045661886114103268313)
            ·
              refine ⟨25807534246414585577451235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34410045661886114103268313 25807534246414585577451235)
              ·
                refine ⟨38711301369621878366176853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25807534246414585577451235 38711301369621878366176853)
                ·
                  refine ⟨453648062925256387103635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38711301369621878366176853 453648062925256387103635)
                  ·
                    rfl

theorem cell21_1987822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1987822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987822 prefixEnd_1987822 := by exact prefixLift 1987822
  have htrace : WordTrace (prefixWord ++ tailWord_1987822) baseStart_1987822 baseEnd_1987822 := by
    simpa [prefixWord, tailWord_1987822, baseEnd_1987822] using wordTrace_append hprefix tailTrace_1987822
  have hstable : (prefixWord ++ tailWord_1987822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987822).length < 2 ^ (prefixWord ++ tailWord_1987822).sum := by decide
  have hdescent : baseEnd_1987822 < baseStart_1987822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987828 : List Nat := [2, 6, 1, 2, 2, 8]
def baseStart_1987828 : Nat := 118140960795 + 1987828 * 2 ^ 59
def prefixEnd_1987828 : Nat := 4983230072969 + 3 ^ 40 * 1987828 * 2
def baseEnd_1987828 : Nat := 16801830822481544814949

theorem tailTrace_1987828 : CollatzResearch.WordTrace tailWord_1987828 prefixEnd_1987828 16801830822481544814949 := by
  unfold tailWord_1987828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36251021721223062419506069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48334695628297416559341425 36251021721223062419506069)
  ·
    refine ⟨1699266643182331050914347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36251021721223062419506069 1699266643182331050914347)
    ·
      refine ⟨2548899964773496576371521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699266643182331050914347 2548899964773496576371521)
      ·
        refine ⟨1911674973580122432278641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2548899964773496576371521 1911674973580122432278641)
        ·
          refine ⟨1433756230185091824208981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1911674973580122432278641 1433756230185091824208981)
          ·
            refine ⟨16801830822481544814949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1433756230185091824208981 16801830822481544814949)
            ·
              rfl

theorem cell21_1987828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 8].length) (baseStart_1987828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987828 prefixEnd_1987828 := by exact prefixLift 1987828
  have htrace : WordTrace (prefixWord ++ tailWord_1987828) baseStart_1987828 baseEnd_1987828 := by
    simpa [prefixWord, tailWord_1987828, baseEnd_1987828] using wordTrace_append hprefix tailTrace_1987828
  have hstable : (prefixWord ++ tailWord_1987828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987828).length < 2 ^ (prefixWord ++ tailWord_1987828).sum := by decide
  have hdescent : baseEnd_1987828 < baseStart_1987828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987836 : List Nat := [2, 2, 2, 1, 14]
def baseStart_1987836 : Nat := 118140960795 + 1987836 * 2 ^ 59
def prefixEnd_1987836 : Nat := 4983230072969 + 3 ^ 40 * 1987836 * 2
def baseEnd_1987836 : Nat := 5600632813777721899633

theorem tailTrace_1987836 : CollatzResearch.WordTrace tailWord_1987836 prefixEnd_1987836 5600632813777721899633 := by
  unfold tailWord_1987836
  simp only [CollatzResearch.WordTrace]
  refine ⟨36251167613208571102651681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48334890150944761470202241 36251167613208571102651681)
  ·
    refine ⟨27188375709906428326988761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36251167613208571102651681 27188375709906428326988761)
    ·
      refine ⟨20391281782429821245241571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27188375709906428326988761 20391281782429821245241571)
      ·
        refine ⟨30586922673644731867862357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20391281782429821245241571 30586922673644731867862357)
        ·
          refine ⟨5600632813777721899633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 30586922673644731867862357 5600632813777721899633)
          ·
            rfl

theorem cell21_1987836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 14].length) (baseStart_1987836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987836 prefixEnd_1987836 := by exact prefixLift 1987836
  have htrace : WordTrace (prefixWord ++ tailWord_1987836) baseStart_1987836 baseEnd_1987836 := by
    simpa [prefixWord, tailWord_1987836, baseEnd_1987836] using wordTrace_append hprefix tailTrace_1987836
  have hstable : (prefixWord ++ tailWord_1987836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987836).length < 2 ^ (prefixWord ++ tailWord_1987836).sum := by decide
  have hdescent : baseEnd_1987836 < baseStart_1987836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987839 : List Nat := [1, 1, 2, 2, 1, 6, 2, 2, 4]
def baseStart_1987839 : Nat := 118140960795 + 1987839 * 2 ^ 59
def prefixEnd_1987839 : Nat := 4983230072969 + 3 ^ 40 * 1987839 * 2
def baseEnd_1987839 : Nat := 453651942556868135320267

theorem tailTrace_1987839 : CollatzResearch.WordTrace tailWord_1987839 prefixEnd_1987839 453651942556868135320267 := by
  unfold tailWord_1987839
  simp only [CollatzResearch.WordTrace]
  refine ⟨72502444645406273717662571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48334963096937515811775047 72502444645406273717662571)
  ·
    refine ⟨108753666968109410576493857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72502444645406273717662571 108753666968109410576493857)
    ·
      refine ⟨81565250226082057932370393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108753666968109410576493857 81565250226082057932370393)
      ·
        refine ⟨61173937669561543449277795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81565250226082057932370393 61173937669561543449277795)
        ·
          refine ⟨91760906504342315173916693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61173937669561543449277795 91760906504342315173916693)
          ·
            refine ⟨4301292492391046023777345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91760906504342315173916693 4301292492391046023777345)
            ·
              refine ⟨3225969369293284517833009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301292492391046023777345 3225969369293284517833009)
              ·
                refine ⟨2419477026969963388374757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225969369293284517833009 2419477026969963388374757)
                ·
                  refine ⟨453651942556868135320267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419477026969963388374757 453651942556868135320267)
                  ·
                    rfl

theorem cell21_1987839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_1987839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987839 prefixEnd_1987839 := by exact prefixLift 1987839
  have htrace : WordTrace (prefixWord ++ tailWord_1987839) baseStart_1987839 baseEnd_1987839 := by
    simpa [prefixWord, tailWord_1987839, baseEnd_1987839] using wordTrace_append hprefix tailTrace_1987839
  have hstable : (prefixWord ++ tailWord_1987839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987839).length < 2 ^ (prefixWord ++ tailWord_1987839).sum := by decide
  have hdescent : baseEnd_1987839 < baseStart_1987839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987898 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_1987898 : Nat := 118140960795 + 1987898 * 2 ^ 59
def prefixEnd_1987898 : Nat := 4983230072969 + 3 ^ 40 * 1987898 * 2
def baseEnd_1987898 : Nat := 453665407160697143836813

theorem tailTrace_1987898 : CollatzResearch.WordTrace tailWord_1987898 prefixEnd_1987898 453665407160697143836813 := by
  unfold tailWord_1987898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126149138048131698515087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48336397701461684529373565 18126149138048131698515087)
  ·
    refine ⟨27189223707072197547772631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18126149138048131698515087 27189223707072197547772631)
    ·
      refine ⟨40783835560608296321658947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27189223707072197547772631 40783835560608296321658947)
      ·
        refine ⟨61175753340912444482488421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40783835560608296321658947 61175753340912444482488421)
        ·
          refine ⟨11470453751421083340466579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61175753340912444482488421 11470453751421083340466579)
          ·
            refine ⟨17205680627131625010699869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470453751421083340466579 17205680627131625010699869)
            ·
              refine ⟨6452130235174359379012451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17205680627131625010699869 6452130235174359379012451)
              ·
                refine ⟨9678195352761539068518677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452130235174359379012451 9678195352761539068518677)
                ·
                  refine ⟨453665407160697143836813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9678195352761539068518677 453665407160697143836813)
                  ·
                    rfl

theorem cell21_1987898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_1987898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987898 prefixEnd_1987898 := by exact prefixLift 1987898
  have htrace : WordTrace (prefixWord ++ tailWord_1987898) baseStart_1987898 baseEnd_1987898 := by
    simpa [prefixWord, tailWord_1987898, baseEnd_1987898] using wordTrace_append hprefix tailTrace_1987898
  have hstable : (prefixWord ++ tailWord_1987898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987898).length < 2 ^ (prefixWord ++ tailWord_1987898).sum := by decide
  have hdescent : baseEnd_1987898 < baseStart_1987898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987912 : List Nat := [2, 1, 3, 1, 1, 2, 1, 10]
def baseStart_1987912 : Nat := 118140960795 + 1987912 * 2 ^ 59
def prefixEnd_1987912 : Nat := 4983230072969 + 3 ^ 40 * 1987912 * 2
def baseEnd_1987912 : Nat := 151222867383812076867817

theorem tailTrace_1987912 : CollatzResearch.WordTrace tailWord_1987912 prefixEnd_1987912 151222867383812076867817 := by
  unfold tailWord_1987912
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252553587070903592534995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48336738116094538123379993 36252553587070903592534995)
  ·
    refine ⟨54378830380606355388802493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36252553587070903592534995 54378830380606355388802493)
    ·
      refine ⟨20392061392727383270800935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54378830380606355388802493 20392061392727383270800935)
      ·
        refine ⟨30588092089091074906201403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20392061392727383270800935 30588092089091074906201403)
        ·
          refine ⟨45882138133636612359302105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30588092089091074906201403 45882138133636612359302105)
          ·
            refine ⟨34411603600227459269476579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45882138133636612359302105 34411603600227459269476579)
            ·
              refine ⟨51617405400341188904214869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34411603600227459269476579 51617405400341188904214869)
              ·
                refine ⟨151222867383812076867817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51617405400341188904214869 151222867383812076867817)
                ·
                  rfl

theorem cell21_1987912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_1987912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987912 prefixEnd_1987912 := by exact prefixLift 1987912
  have htrace : WordTrace (prefixWord ++ tailWord_1987912) baseStart_1987912 baseEnd_1987912 := by
    simpa [prefixWord, tailWord_1987912, baseEnd_1987912] using wordTrace_append hprefix tailTrace_1987912
  have hstable : (prefixWord ++ tailWord_1987912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987912).length < 2 ^ (prefixWord ++ tailWord_1987912).sum := by decide
  have hdescent : baseEnd_1987912 < baseStart_1987912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987929 : List Nat := [1, 2, 1, 2, 2, 2, 6, 5]
def baseStart_1987929 : Nat := 118140960795 + 1987929 * 2 ^ 59
def prefixEnd_1987929 : Nat := 4983230072969 + 3 ^ 40 * 1987929 * 2
def baseEnd_1987929 : Nat := 151224160594349326273361

theorem tailTrace_1987929 : CollatzResearch.WordTrace tailWord_1987929 prefixEnd_1987929 151224160594349326273361 := by
  unfold tailWord_1987929
  simp only [CollatzResearch.WordTrace]
  refine ⟨72505727215080219088438841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48337151476720146058959227 72505727215080219088438841)
  ·
    refine ⟨54379295411310164316329131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72505727215080219088438841 54379295411310164316329131)
    ·
      refine ⟨81568943116965246474493697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54379295411310164316329131 81568943116965246474493697)
      ·
        refine ⟨61176707337723934855870273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81568943116965246474493697 61176707337723934855870273)
        ·
          refine ⟨45882530503292951141902705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61176707337723934855870273 45882530503292951141902705)
          ·
            refine ⟨34411897877469713356427029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45882530503292951141902705 34411897877469713356427029)
            ·
              refine ⟨1613057713006392813582517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34411897877469713356427029 1613057713006392813582517)
              ·
                refine ⟨151224160594349326273361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613057713006392813582517 151224160594349326273361)
                ·
                  rfl

theorem cell21_1987929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 5].length) (baseStart_1987929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987929 prefixEnd_1987929 := by exact prefixLift 1987929
  have htrace : WordTrace (prefixWord ++ tailWord_1987929) baseStart_1987929 baseEnd_1987929 := by
    simpa [prefixWord, tailWord_1987929, baseEnd_1987929] using wordTrace_append hprefix tailTrace_1987929
  have hstable : (prefixWord ++ tailWord_1987929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987929).length < 2 ^ (prefixWord ++ tailWord_1987929).sum := by decide
  have hdescent : baseEnd_1987929 < baseStart_1987929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987946 : List Nat := [3, 1, 3, 3, 2, 2, 7]
def baseStart_1987946 : Nat := 118140960795 + 1987946 * 2 ^ 59
def prefixEnd_1987946 : Nat := 4983230072969 + 3 ^ 40 * 1987946 * 2
def baseEnd_1987946 : Nat := 50408484601628858559635

theorem tailTrace_1987946 : CollatzResearch.WordTrace tailWord_1987946 prefixEnd_1987946 50408484601628858559635 := by
  unfold tailWord_1987946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126586814004657747951923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48337564837345753994538461 18126586814004657747951923)
  ·
    refine ⟨27189880221006986621927885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18126586814004657747951923 27189880221006986621927885)
    ·
      refine ⟨10196205082877619983222957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27189880221006986621927885 10196205082877619983222957)
      ·
        refine ⟨3823576906079107493708609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10196205082877619983222957 3823576906079107493708609)
        ·
          refine ⟨2867682679559330620281457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3823576906079107493708609 2867682679559330620281457)
          ·
            refine ⟨2150762009669497965211093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867682679559330620281457 2150762009669497965211093)
            ·
              refine ⟨50408484601628858559635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2150762009669497965211093 50408484601628858559635)
              ·
                rfl

theorem cell21_1987946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 7].length) (baseStart_1987946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1987946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1987946 prefixEnd_1987946 := by exact prefixLift 1987946
  have htrace : WordTrace (prefixWord ++ tailWord_1987946) baseStart_1987946 baseEnd_1987946 := by
    simpa [prefixWord, tailWord_1987946, baseEnd_1987946] using wordTrace_append hprefix tailTrace_1987946
  have hstable : (prefixWord ++ tailWord_1987946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987946).length < 2 ^ (prefixWord ++ tailWord_1987946).sum := by decide
  have hdescent : baseEnd_1987946 < baseStart_1987946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988036 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1988036 : Nat := 118140960795 + 1988036 * 2 ^ 59
def prefixEnd_1988036 : Nat := 4983230072969 + 3 ^ 40 * 1988036 * 2
def baseEnd_1988036 : Nat := 453696900640839570536531

theorem tailTrace_1988036 : CollatzResearch.WordTrace tailWord_1988036 prefixEnd_1988036 453696900640839570536531 := by
  unfold tailWord_1988036
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254814912846288181291981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48339753217128384241722641 36254814912846288181291981)
  ·
    refine ⟨13595555592317358067984493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36254814912846288181291981 13595555592317358067984493)
    ·
      refine ⟨5098333347119009275494185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13595555592317358067984493 5098333347119009275494185)
      ·
        refine ⟨3823750010339256956620639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5098333347119009275494185 3823750010339256956620639)
        ·
          refine ⟨5735625015508885434930959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823750010339256956620639 5735625015508885434930959)
          ·
            refine ⟨8603437523263328152396439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735625015508885434930959 8603437523263328152396439)
            ·
              refine ⟨12905156284894992228594659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603437523263328152396439 12905156284894992228594659)
              ·
                refine ⟨19357734427342488342891989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12905156284894992228594659 19357734427342488342891989)
                ·
                  refine ⟨453696900640839570536531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19357734427342488342891989 453696900640839570536531)
                  ·
                    rfl

theorem cell21_1988036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1988036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988036 prefixEnd_1988036 := by exact prefixLift 1988036
  have htrace : WordTrace (prefixWord ++ tailWord_1988036) baseStart_1988036 baseEnd_1988036 := by
    simpa [prefixWord, tailWord_1988036, baseEnd_1988036] using wordTrace_append hprefix tailTrace_1988036
  have hstable : (prefixWord ++ tailWord_1988036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988036).length < 2 ^ (prefixWord ++ tailWord_1988036).sum := by decide
  have hdescent : baseEnd_1988036 < baseStart_1988036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988053 : List Nat := [1, 3, 2, 3, 1, 1, 4, 3, 3]
def baseStart_1988053 : Nat := 118140960795 + 1988053 * 2 ^ 59
def prefixEnd_1988053 : Nat := 4983230072969 + 3 ^ 40 * 1988053 * 2
def baseEnd_1988053 : Nat := 453700780272451318753163

theorem tailTrace_1988053 : CollatzResearch.WordTrace tailWord_1988053 prefixEnd_1988053 453700780272451318753163 := by
  unfold tailWord_1988053
  simp only [CollatzResearch.WordTrace]
  refine ⟨72510249866630988265952813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48340166577753992177301875 72510249866630988265952813)
  ·
    refine ⟨27191343699986620599732305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72510249866630988265952813 27191343699986620599732305)
    ·
      refine ⟨20393507774989965449799229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27191343699986620599732305 20393507774989965449799229)
      ·
        refine ⟨7647565415621237043674711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20393507774989965449799229 7647565415621237043674711)
        ·
          refine ⟨11471348123431855565512067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7647565415621237043674711 11471348123431855565512067)
          ·
            refine ⟨17207022185147783348268101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11471348123431855565512067 17207022185147783348268101)
            ·
              refine ⟨3226316659715209377800269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17207022185147783348268101 3226316659715209377800269)
              ·
                refine ⟨1209868747393203516675101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226316659715209377800269 1209868747393203516675101)
                ·
                  refine ⟨453700780272451318753163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209868747393203516675101 453700780272451318753163)
                  ·
                    rfl

theorem cell21_1988053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_1988053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988053 prefixEnd_1988053 := by exact prefixLift 1988053
  have htrace : WordTrace (prefixWord ++ tailWord_1988053) baseStart_1988053 baseEnd_1988053 := by
    simpa [prefixWord, tailWord_1988053, baseEnd_1988053] using wordTrace_append hprefix tailTrace_1988053
  have hstable : (prefixWord ++ tailWord_1988053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988053).length < 2 ^ (prefixWord ++ tailWord_1988053).sum := by decide
  have hdescent : baseEnd_1988053 < baseStart_1988053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988067 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 4]
def baseStart_1988067 : Nat := 118140960795 + 1988067 * 2 ^ 59
def prefixEnd_1988067 : Nat := 4983230072969 + 3 ^ 40 * 1988067 * 2
def baseEnd_1988067 : Nat := 453703975263190405519801

theorem tailTrace_1988067 : CollatzResearch.WordTrace tailWord_1988067 prefixEnd_1988067 453703975263190405519801 := by
  unfold tailWord_1988067
  simp only [CollatzResearch.WordTrace]
  refine ⟨72510760488580268656962455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48340506992386845771308303 72510760488580268656962455)
  ·
    refine ⟨108766140732870402985443683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72510760488580268656962455 108766140732870402985443683)
    ·
      refine ⟨163149211099305604478165525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108766140732870402985443683 163149211099305604478165525)
      ·
        refine ⟨7647619270279950209914009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163149211099305604478165525 7647619270279950209914009)
        ·
          refine ⟨5735714452709962657435507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7647619270279950209914009 5735714452709962657435507)
          ·
            refine ⟨8603571679064943986153261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735714452709962657435507 8603571679064943986153261)
            ·
              refine ⟨3226339379649353994807473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8603571679064943986153261 3226339379649353994807473)
              ·
                refine ⟨2419754534737015496105605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226339379649353994807473 2419754534737015496105605)
                ·
                  refine ⟨453703975263190405519801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419754534737015496105605 453703975263190405519801)
                  ·
                    rfl

theorem cell21_1988067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 4].length) (baseStart_1988067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988067 prefixEnd_1988067 := by exact prefixLift 1988067
  have htrace : WordTrace (prefixWord ++ tailWord_1988067) baseStart_1988067 baseEnd_1988067 := by
    simpa [prefixWord, tailWord_1988067, baseEnd_1988067] using wordTrace_append hprefix tailTrace_1988067
  have hstable : (prefixWord ++ tailWord_1988067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988067).length < 2 ^ (prefixWord ++ tailWord_1988067).sum := by decide
  have hdescent : baseEnd_1988067 < baseStart_1988067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988098 : List Nat := [3, 4, 1, 2, 1, 2, 1, 7]
def baseStart_1988098 : Nat := 118140960795 + 1988098 * 2 ^ 59
def prefixEnd_1988098 : Nat := 4983230072969 + 3 ^ 40 * 1988098 * 2
def baseEnd_1988098 : Nat := 151237016628513746834357

theorem tailTrace_1988098 : CollatzResearch.WordTrace tailWord_1988098 prefixEnd_1988098 151237016628513746834357 := by
  unfold tailWord_1988098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127972787866990237835237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48341260767645307300893965 18127972787866990237835237)
  ·
    refine ⟨3398994897725060669594107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18127972787866990237835237 3398994897725060669594107)
    ·
      refine ⟨5098492346587591004391161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398994897725060669594107 5098492346587591004391161)
      ·
        refine ⟨3823869259940693253293371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5098492346587591004391161 3823869259940693253293371)
        ·
          refine ⟨5735803889911039879940057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823869259940693253293371 5735803889911039879940057)
          ·
            refine ⟨4301852917433279909955043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5735803889911039879940057 4301852917433279909955043)
            ·
              refine ⟨6452779376149919864932565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301852917433279909955043 6452779376149919864932565)
              ·
                refine ⟨151237016628513746834357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6452779376149919864932565 151237016628513746834357)
                ·
                  rfl

theorem cell21_1988098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_1988098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988098 prefixEnd_1988098 := by exact prefixLift 1988098
  have htrace : WordTrace (prefixWord ++ tailWord_1988098) baseStart_1988098 baseEnd_1988098 := by
    simpa [prefixWord, tailWord_1988098, baseEnd_1988098] using wordTrace_append hprefix tailTrace_1988098
  have hstable : (prefixWord ++ tailWord_1988098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988098).length < 2 ^ (prefixWord ++ tailWord_1988098).sum := by decide
  have hdescent : baseEnd_1988098 < baseStart_1988098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988185 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 6]
def baseStart_1988185 : Nat := 118140960795 + 1988185 * 2 ^ 59
def prefixEnd_1988185 : Nat := 4983230072969 + 3 ^ 40 * 1988185 * 2
def baseEnd_1988185 : Nat := 453730904470848422552893

theorem tailTrace_1988185 : CollatzResearch.WordTrace tailWord_1988185 prefixEnd_1988185 453730904470848422552893 := by
  unfold tailWord_1988185
  simp only [CollatzResearch.WordTrace]
  refine ⟨72515064302152774809758009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48343376201435183206505339 72515064302152774809758009)
  ·
    refine ⟨54386298226614581107318507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72515064302152774809758009 54386298226614581107318507)
    ·
      refine ⟨81579447339921871660977761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54386298226614581107318507 81579447339921871660977761)
      ·
        refine ⟨61184585504941403745733321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81579447339921871660977761 61184585504941403745733321)
        ·
          refine ⟨45888439128706052809299991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61184585504941403745733321 45888439128706052809299991)
          ·
            refine ⟨68832658693059079213949987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45888439128706052809299991 68832658693059079213949987)
            ·
              refine ⟨103248988039588618820924981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68832658693059079213949987 103248988039588618820924981)
              ·
                refine ⟨9679592628711433014461717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103248988039588618820924981 9679592628711433014461717)
                ·
                  refine ⟨453730904470848422552893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9679592628711433014461717 453730904470848422552893)
                  ·
                    rfl

theorem cell21_1988185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_1988185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988185 prefixEnd_1988185 := by exact prefixLift 1988185
  have htrace : WordTrace (prefixWord ++ tailWord_1988185) baseStart_1988185 baseEnd_1988185 := by
    simpa [prefixWord, tailWord_1988185, baseEnd_1988185] using wordTrace_append hprefix tailTrace_1988185
  have hstable : (prefixWord ++ tailWord_1988185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988185).length < 2 ^ (prefixWord ++ tailWord_1988185).sum := by decide
  have hdescent : baseEnd_1988185 < baseStart_1988185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988247 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 5]
def baseStart_1988247 : Nat := 118140960795 + 1988247 * 2 ^ 59
def prefixEnd_1988247 : Nat := 4983230072969 + 3 ^ 40 * 1988247 * 2
def baseEnd_1988247 : Nat := 453745053715550092519433

theorem tailTrace_1988247 : CollatzResearch.WordTrace tailWord_1988247 prefixEnd_1988247 453745053715550092519433 := by
  unfold tailWord_1988247
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517325627928159398514995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48344883751952106265676663 72517325627928159398514995)
  ·
    refine ⟨108775988441892239097772493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72517325627928159398514995 108775988441892239097772493)
    ·
      refine ⟨40790995665709589661664685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108775988441892239097772493 40790995665709589661664685)
      ·
        refine ⟨15296623374641096123124257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40790995665709589661664685 15296623374641096123124257)
        ·
          refine ⟨11472467530980822092343193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15296623374641096123124257 11472467530980822092343193)
          ·
            refine ⟨8604350648235616569257395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11472467530980822092343193 8604350648235616569257395)
            ·
              refine ⟨12906525972353424853886093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604350648235616569257395 12906525972353424853886093)
              ·
                refine ⟨4839947239632534320207285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12906525972353424853886093 4839947239632534320207285)
                ·
                  refine ⟨453745053715550092519433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4839947239632534320207285 453745053715550092519433)
                  ·
                    rfl

theorem cell21_1988247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_1988247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988247 prefixEnd_1988247 := by exact prefixLift 1988247
  have htrace : WordTrace (prefixWord ++ tailWord_1988247) baseStart_1988247 baseEnd_1988247 := by
    simpa [prefixWord, tailWord_1988247, baseEnd_1988247] using wordTrace_append hprefix tailTrace_1988247
  have hstable : (prefixWord ++ tailWord_1988247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988247).length < 2 ^ (prefixWord ++ tailWord_1988247).sum := by decide
  have hdescent : baseEnd_1988247 < baseStart_1988247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988298 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_1988298 : Nat := 118140960795 + 1988298 * 2 ^ 59
def prefixEnd_1988298 : Nat := 4983230072969 + 3 ^ 40 * 1988298 * 2
def baseEnd_1988298 : Nat := 453756692610385337169329

theorem tailTrace_1988298 : CollatzResearch.WordTrace tailWord_1988298 prefixEnd_1988298 453756692610385337169329 := by
  unfold tailWord_1988298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129796437685848777155387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48346123833828930072414365 18129796437685848777155387)
  ·
    refine ⟨27194694656528773165733081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18129796437685848777155387 27194694656528773165733081)
    ·
      refine ⟨20396020992396579874299811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27194694656528773165733081 20396020992396579874299811)
      ·
        refine ⟨30594031488594869811449717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20396020992396579874299811 30594031488594869811449717)
        ·
          refine ⟨2868190452055769044823411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30594031488594869811449717 2868190452055769044823411)
          ·
            refine ⟨4302285678083653567235117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868190452055769044823411 4302285678083653567235117)
            ·
              refine ⟨1613357129281370087713169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4302285678083653567235117 1613357129281370087713169)
              ·
                refine ⟨1210017846961027565784877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613357129281370087713169 1210017846961027565784877)
                ·
                  refine ⟨453756692610385337169329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210017846961027565784877 453756692610385337169329)
                  ·
                    rfl

theorem cell21_1988298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_1988298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988298 prefixEnd_1988298 := by exact prefixLift 1988298
  have htrace : WordTrace (prefixWord ++ tailWord_1988298) baseStart_1988298 baseEnd_1988298 := by
    simpa [prefixWord, tailWord_1988298, baseEnd_1988298] using wordTrace_append hprefix tailTrace_1988298
  have hstable : (prefixWord ++ tailWord_1988298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988298).length < 2 ^ (prefixWord ++ tailWord_1988298).sum := by decide
  have hdescent : baseEnd_1988298 < baseStart_1988298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988385 : List Nat := [1, 2, 3, 2, 1, 4, 3, 5]
def baseStart_1988385 : Nat := 118140960795 + 1988385 * 2 ^ 59
def prefixEnd_1988385 : Nat := 4983230072969 + 3 ^ 40 * 1988385 * 2
def baseEnd_1988385 : Nat := 151258849065230839739717

theorem tailTrace_1988385 : CollatzResearch.WordTrace tailWord_1988385 prefixEnd_1988385 151258849065230839739717 := by
  unfold tailWord_1988385
  simp only [CollatzResearch.WordTrace]
  refine ⟨72522358901428208967038609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48348239267618805978025739 72522358901428208967038609)
  ·
    refine ⟨54391769176071156725278957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72522358901428208967038609 54391769176071156725278957)
    ·
      refine ⟨20396913441026683771979609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54391769176071156725278957 20396913441026683771979609)
      ·
        refine ⟨15297685080770012828984707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20396913441026683771979609 15297685080770012828984707)
        ·
          refine ⟨22946527621155019243477061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297685080770012828984707 22946527621155019243477061)
          ·
            refine ⟨4302473928966566108151949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22946527621155019243477061 4302473928966566108151949)
            ·
              refine ⟨1613427723362462290556981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4302473928966566108151949 1613427723362462290556981)
              ·
                refine ⟨151258849065230839739717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613427723362462290556981 151258849065230839739717)
                ·
                  rfl

theorem cell21_1988385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 5].length) (baseStart_1988385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988385 prefixEnd_1988385 := by exact prefixLift 1988385
  have htrace : WordTrace (prefixWord ++ tailWord_1988385) baseStart_1988385 baseEnd_1988385 := by
    simpa [prefixWord, tailWord_1988385, baseEnd_1988385] using wordTrace_append hprefix tailTrace_1988385
  have hstable : (prefixWord ++ tailWord_1988385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988385).length < 2 ^ (prefixWord ++ tailWord_1988385).sum := by decide
  have hdescent : baseEnd_1988385 < baseStart_1988385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988450 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1988450 : Nat := 118140960795 + 1988450 * 2 ^ 59
def prefixEnd_1988450 : Nat := 4983230072969 + 3 ^ 40 * 1988450 * 2
def baseEnd_1988450 : Nat := 453791381081266850635685

theorem tailTrace_1988450 : CollatzResearch.WordTrace tailWord_1988450 prefixEnd_1988450 453791381081266850635685 := by
  unfold tailWord_1988450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131182411548181267038701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48349819764128483378769869 18131182411548181267038701)
  ·
    refine ⟨6799193404330567975139513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18131182411548181267038701 6799193404330567975139513)
    ·
      refine ⟨5099395053247925981354635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6799193404330567975139513 5099395053247925981354635)
      ·
        refine ⟨7649092579871888972031953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099395053247925981354635 7649092579871888972031953)
        ·
          refine ⟨5736819434903916729023965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7649092579871888972031953 5736819434903916729023965)
          ·
            refine ⟨2151307288088968773383987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5736819434903916729023965 2151307288088968773383987)
            ·
              refine ⟨3226960932133453160075981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151307288088968773383987 3226960932133453160075981)
              ·
                refine ⟨1210110349550044935028493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226960932133453160075981 1210110349550044935028493)
                ·
                  refine ⟨453791381081266850635685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210110349550044935028493 453791381081266850635685)
                  ·
                    rfl

theorem cell21_1988450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1988450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988450 prefixEnd_1988450 := by exact prefixLift 1988450
  have htrace : WordTrace (prefixWord ++ tailWord_1988450) baseStart_1988450 baseEnd_1988450 := by
    simpa [prefixWord, tailWord_1988450, baseEnd_1988450] using wordTrace_append hprefix tailTrace_1988450
  have hstable : (prefixWord ++ tailWord_1988450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988450).length < 2 ^ (prefixWord ++ tailWord_1988450).sum := by decide
  have hdescent : baseEnd_1988450 < baseStart_1988450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988478 : List Nat := [4, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1988478 : Nat := 118140960795 + 1988478 * 2 ^ 59
def prefixEnd_1988478 : Nat := 4983230072969 + 3 ^ 40 * 1988478 * 2
def baseEnd_1988478 : Nat := 151265923687581674722987

theorem tailTrace_1988478 : CollatzResearch.WordTrace tailWord_1988478 prefixEnd_1988478 151265923687581674722987 := by
  unfold tailWord_1988478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065718861261410731271761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48350500593394190566782725 9065718861261410731271761)
  ·
    refine ⟨6799289145946058048453821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9065718861261410731271761 6799289145946058048453821)
    ·
      refine ⟨2549733429729771768170183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6799289145946058048453821 2549733429729771768170183)
      ·
        refine ⟨3824600144594657652255275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549733429729771768170183 3824600144594657652255275)
        ·
          refine ⟨5736900216891986478382913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3824600144594657652255275 5736900216891986478382913)
          ·
            refine ⟨4302675162668989858787185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5736900216891986478382913 4302675162668989858787185)
            ·
              refine ⟨3227006372001742394090389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302675162668989858787185 3227006372001742394090389)
              ·
                refine ⟨151265923687581674722987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3227006372001742394090389 151265923687581674722987)
                ·
                  rfl

theorem cell21_1988478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1988478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988478 prefixEnd_1988478 := by exact prefixLift 1988478
  have htrace : WordTrace (prefixWord ++ tailWord_1988478) baseStart_1988478 baseEnd_1988478 := by
    simpa [prefixWord, tailWord_1988478, baseEnd_1988478] using wordTrace_append hprefix tailTrace_1988478
  have hstable : (prefixWord ++ tailWord_1988478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988478).length < 2 ^ (prefixWord ++ tailWord_1988478).sum := by decide
  have hdescent : baseEnd_1988478 < baseStart_1988478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988481 : List Nat := [1, 2, 4, 4, 1, 2, 2, 1, 4]
def baseStart_1988481 : Nat := 118140960795 + 1988481 * 2 ^ 59
def prefixEnd_1988481 : Nat := 4983230072969 + 3 ^ 40 * 1988481 * 2
def baseEnd_1988481 : Nat := 453798455703617685618955

theorem tailTrace_1988481 : CollatzResearch.WordTrace tailWord_1988481 prefixEnd_1988481 453798455703617685618955 := by
  unfold tailWord_1988481
  simp only [CollatzResearch.WordTrace]
  refine ⟨72525860309080417362533297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48350573539386944908355531 72525860309080417362533297)
  ·
    refine ⟨54394395231810313021899973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72525860309080417362533297 54394395231810313021899973)
    ·
      refine ⟨10198949105964433691606245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54394395231810313021899973 10198949105964433691606245)
      ·
        refine ⟨1912302957368331317176171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10198949105964433691606245 1912302957368331317176171)
        ·
          refine ⟨2868454436052496975764257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912302957368331317176171 2868454436052496975764257)
          ·
            refine ⟨2151340827039372731823193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868454436052496975764257 2151340827039372731823193)
            ·
              refine ⟨1613505620279529548867395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151340827039372731823193 1613505620279529548867395)
              ·
                refine ⟨2420258430419294323301093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613505620279529548867395 2420258430419294323301093)
                ·
                  refine ⟨453798455703617685618955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2420258430419294323301093 453798455703617685618955)
                  ·
                    rfl

theorem cell21_1988481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_1988481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988481 prefixEnd_1988481 := by exact prefixLift 1988481
  have htrace : WordTrace (prefixWord ++ tailWord_1988481) baseStart_1988481 baseEnd_1988481 := by
    simpa [prefixWord, tailWord_1988481, baseEnd_1988481] using wordTrace_append hprefix tailTrace_1988481
  have hstable : (prefixWord ++ tailWord_1988481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988481).length < 2 ^ (prefixWord ++ tailWord_1988481).sum := by decide
  have hdescent : baseEnd_1988481 < baseStart_1988481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988568 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_1988568 : Nat := 118140960795 + 1988568 * 2 ^ 59
def prefixEnd_1988568 : Nat := 4983230072969 + 3 ^ 40 * 1988568 * 2
def baseEnd_1988568 : Nat := 453818310288924867668777

theorem tailTrace_1988568 : CollatzResearch.WordTrace tailWord_1988568 prefixEnd_1988568 453818310288924867668777 := by
  unfold tailWord_1988568
  simp only [CollatzResearch.WordTrace]
  refine ⟨36264516729882615610475179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48352688973176820813966905 36264516729882615610475179)
  ·
    refine ⟨54396775094823923415712769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36264516729882615610475179 54396775094823923415712769)
    ·
      refine ⟨40797581321117942561784577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54396775094823923415712769 40797581321117942561784577)
      ·
        refine ⟨30598185990838456921338433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40797581321117942561784577 30598185990838456921338433)
        ·
          refine ⟨22948639493128842691003825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30598185990838456921338433 22948639493128842691003825)
          ·
            refine ⟨17211479619846632018252869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22948639493128842691003825 17211479619846632018252869)
            ·
              refine ⟨3227152428721243503422413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17211479619846632018252869 3227152428721243503422413)
              ·
                refine ⟨1210182160770466313783405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3227152428721243503422413 1210182160770466313783405)
                ·
                  refine ⟨453818310288924867668777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210182160770466313783405 453818310288924867668777)
                  ·
                    rfl

theorem cell21_1988568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_1988568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988568 prefixEnd_1988568 := by exact prefixLift 1988568
  have htrace : WordTrace (prefixWord ++ tailWord_1988568) baseStart_1988568 baseEnd_1988568 := by
    simpa [prefixWord, tailWord_1988568, baseEnd_1988568] using wordTrace_append hprefix tailTrace_1988568
  have hstable : (prefixWord ++ tailWord_1988568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988568).length < 2 ^ (prefixWord ++ tailWord_1988568).sum := by decide
  have hdescent : baseEnd_1988568 < baseStart_1988568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988613 : List Nat := [1, 3, 1, 1, 2, 6, 2, 5]
def baseStart_1988613 : Nat := 118140960795 + 1988613 * 2 ^ 59
def prefixEnd_1988613 : Nat := 4983230072969 + 3 ^ 40 * 1988613 * 2
def baseEnd_1988613 : Nat := 151276193300671596472895

theorem tailTrace_1988613 : CollatzResearch.WordTrace tailWord_1988613 prefixEnd_1988613 151276193300671596472895 := by
  unfold tailWord_1988613
  simp only [CollatzResearch.WordTrace]
  refine ⟨72530674744602203906338493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48353783163068135937558995 72530674744602203906338493)
  ·
    refine ⟨27199003029225826464876935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72530674744602203906338493 27199003029225826464876935)
    ·
      refine ⟨40798504543838739697315403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27199003029225826464876935 40798504543838739697315403)
      ·
        refine ⟨61197756815758109545973105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40798504543838739697315403 61197756815758109545973105)
        ·
          refine ⟨45898317611818582159479829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61197756815758109545973105 45898317611818582159479829)
          ·
            refine ⟨2151483638053996038725617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45898317611818582159479829 2151483638053996038725617)
            ·
              refine ⟨1613612728540497029044213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151483638053996038725617 1613612728540497029044213)
              ·
                refine ⟨151276193300671596472895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1613612728540497029044213 151276193300671596472895)
                ·
                  rfl

theorem cell21_1988613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 5].length) (baseStart_1988613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988613 prefixEnd_1988613 := by exact prefixLift 1988613
  have htrace : WordTrace (prefixWord ++ tailWord_1988613) baseStart_1988613 baseEnd_1988613 := by
    simpa [prefixWord, tailWord_1988613, baseEnd_1988613] using wordTrace_append hprefix tailTrace_1988613
  have hstable : (prefixWord ++ tailWord_1988613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988613).length < 2 ^ (prefixWord ++ tailWord_1988613).sum := by decide
  have hdescent : baseEnd_1988613 < baseStart_1988613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988658 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1988658 : Nat := 118140960795 + 1988658 * 2 ^ 59
def prefixEnd_1988658 : Nat := 4983230072969 + 3 ^ 40 * 1988658 * 2
def baseEnd_1988658 : Nat := 453838849515104711168593

theorem tailTrace_1988658 : CollatzResearch.WordTrace tailWord_1988658 prefixEnd_1988658 453838849515104711168593 := by
  unfold tailWord_1988658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18133079007359794147931657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48354877352959451061151085 18133079007359794147931657)
  ·
    refine ⟨13599809255519845610948743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18133079007359794147931657 13599809255519845610948743)
    ·
      refine ⟨20399713883279768416423115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13599809255519845610948743 20399713883279768416423115)
      ·
        refine ⟨30599570824919652624634673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20399713883279768416423115 30599570824919652624634673)
        ·
          refine ⟨22949678118689739468476005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30599570824919652624634673 22949678118689739468476005)
          ·
            refine ⟨4303064647254326150339251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22949678118689739468476005 4303064647254326150339251)
            ·
              refine ⟨6454596970881489225508877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303064647254326150339251 6454596970881489225508877)
              ·
                refine ⟨2420473864080558459565829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6454596970881489225508877 2420473864080558459565829)
                ·
                  refine ⟨453838849515104711168593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2420473864080558459565829 453838849515104711168593)
                  ·
                    rfl

theorem cell21_1988658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1988658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988658 prefixEnd_1988658 := by exact prefixLift 1988658
  have htrace : WordTrace (prefixWord ++ tailWord_1988658) baseStart_1988658 baseEnd_1988658 := by
    simpa [prefixWord, tailWord_1988658, baseEnd_1988658] using wordTrace_append hprefix tailTrace_1988658
  have hstable : (prefixWord ++ tailWord_1988658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988658).length < 2 ^ (prefixWord ++ tailWord_1988658).sum := by decide
  have hdescent : baseEnd_1988658 < baseStart_1988658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988706 : List Nat := [3, 3, 2, 2, 2, 2, 1, 6]
def baseStart_1988706 : Nat := 118140960795 + 1988706 * 2 ^ 59
def prefixEnd_1988706 : Nat := 4983230072969 + 3 ^ 40 * 1988706 * 2
def baseEnd_1988706 : Nat := 151283267923022431456165

theorem tailTrace_1988706 : CollatzResearch.WordTrace tailWord_1988706 prefixEnd_1988706 151283267923022431456165 := by
  unfold tailWord_1988706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18133516683316320197368493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48356044488843520526315981 18133516683316320197368493)
  ·
    refine ⟨6800068756243620074013185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18133516683316320197368493 6800068756243620074013185)
    ·
      refine ⟨5100051567182715055509889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6800068756243620074013185 5100051567182715055509889)
      ·
        refine ⟨3825038675387036291632417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5100051567182715055509889 3825038675387036291632417)
        ·
          refine ⟨2868779006540277218724313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3825038675387036291632417 2868779006540277218724313)
          ·
            refine ⟨2151584254905207914043235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868779006540277218724313 2151584254905207914043235)
            ·
              refine ⟨3227376382357811871064853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151584254905207914043235 3227376382357811871064853)
              ·
                refine ⟨151283267923022431456165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3227376382357811871064853 151283267923022431456165)
                ·
                  rfl

theorem cell21_1988706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_1988706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988706 prefixEnd_1988706 := by exact prefixLift 1988706
  have htrace : WordTrace (prefixWord ++ tailWord_1988706) baseStart_1988706 baseEnd_1988706 := by
    simpa [prefixWord, tailWord_1988706, baseEnd_1988706] using wordTrace_append hprefix tailTrace_1988706
  have hstable : (prefixWord ++ tailWord_1988706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988706).length < 2 ^ (prefixWord ++ tailWord_1988706).sum := by decide
  have hdescent : baseEnd_1988706 < baseStart_1988706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988737 : List Nat := [1, 2, 4, 2, 3, 1, 2, 3, 3]
def baseStart_1988737 : Nat := 118140960795 + 1988737 * 2 ^ 59
def prefixEnd_1988737 : Nat := 4983230072969 + 3 ^ 40 * 1988737 * 2
def baseEnd_1988737 : Nat := 453856878391418129351765

theorem tailTrace_1988737 : CollatzResearch.WordTrace tailWord_1988737 prefixEnd_1988737 453856878391418129351765 := by
  unfold tailWord_1988737
  simp only [CollatzResearch.WordTrace]
  refine ⟨72535197396152973083852465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48356798264101982055901643 72535197396152973083852465)
  ·
    refine ⟨54401398047114729812889349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72535197396152973083852465 54401398047114729812889349)
    ·
      refine ⟨10200262133834011839916753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54401398047114729812889349 10200262133834011839916753)
      ·
        refine ⟨7650196600375508879937565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10200262133834011839916753 7650196600375508879937565)
        ·
          refine ⟨2868823725140815829976587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7650196600375508879937565 2868823725140815829976587)
          ·
            refine ⟨4303235587711223744964881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868823725140815829976587 4303235587711223744964881)
            ·
              refine ⟨3227426690783417808723661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303235587711223744964881 3227426690783417808723661)
              ·
                refine ⟨1210285009043781678271373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3227426690783417808723661 1210285009043781678271373)
                ·
                  refine ⟨453856878391418129351765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210285009043781678271373 453856878391418129351765)
                  ·
                    rfl

theorem cell21_1988737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_1988737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988737 prefixEnd_1988737 := by exact prefixLift 1988737
  have htrace : WordTrace (prefixWord ++ tailWord_1988737) baseStart_1988737 baseEnd_1988737 := by
    simpa [prefixWord, tailWord_1988737, baseEnd_1988737] using wordTrace_append hprefix tailTrace_1988737
  have hstable : (prefixWord ++ tailWord_1988737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988737).length < 2 ^ (prefixWord ++ tailWord_1988737).sum := by decide
  have hdescent : baseEnd_1988737 < baseStart_1988737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988782 : List Nat := [4, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1988782 : Nat := 118140960795 + 1988782 * 2 ^ 59
def prefixEnd_1988782 : Nat := 4983230072969 + 3 ^ 40 * 1988782 * 2
def baseEnd_1988782 : Nat := 151289049334836017033891

theorem tailTrace_1988782 : CollatzResearch.WordTrace tailWord_1988782 prefixEnd_1988782 151289049334836017033891 := by
  unfold tailWord_1988782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067104835123743221155075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48357892453993297179493733 9067104835123743221155075)
  ·
    refine ⟨13600657252685614831732613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9067104835123743221155075 13600657252685614831732613)
    ·
      refine ⟨2550123234878552780949865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13600657252685614831732613 2550123234878552780949865)
      ·
        refine ⟨1912592426158914585712399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2550123234878552780949865 1912592426158914585712399)
        ·
          refine ⟨2868888639238371878568599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912592426158914585712399 2868888639238371878568599)
          ·
            refine ⟨4303332958857557817852899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868888639238371878568599 4303332958857557817852899)
            ·
              refine ⟨6454999438286336726779349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303332958857557817852899 6454999438286336726779349)
              ·
                refine ⟨151289049334836017033891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6454999438286336726779349 151289049334836017033891)
                ·
                  rfl

theorem cell21_1988782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1988782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988782 prefixEnd_1988782 := by exact prefixLift 1988782
  have htrace : WordTrace (prefixWord ++ tailWord_1988782) baseStart_1988782 baseEnd_1988782 := by
    simpa [prefixWord, tailWord_1988782, baseEnd_1988782] using wordTrace_append hprefix tailTrace_1988782
  have hstable : (prefixWord ++ tailWord_1988782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988782).length < 2 ^ (prefixWord ++ tailWord_1988782).sum := by decide
  have hdescent : baseEnd_1988782 < baseStart_1988782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988788 : List Nat := [2, 5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1988788 : Nat := 118140960795 + 1988788 * 2 ^ 59
def prefixEnd_1988788 : Nat := 4983230072969 + 3 ^ 40 * 1988788 * 2
def baseEnd_1988788 : Nat := 453868517286253374001661

theorem tailTrace_1988788 : CollatzResearch.WordTrace tailWord_1988788 prefixEnd_1988788 453868517286253374001661 := by
  unfold tailWord_1988788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36268528759484104396979509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48358038345978805862639345 36268528759484104396979509)
  ·
    refine ⟨3400174571201634787216829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36268528759484104396979509 3400174571201634787216829)
    ·
      refine ⟨1275065464200613045206311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3400174571201634787216829 1275065464200613045206311)
      ·
        refine ⟨1912598196300919567809467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275065464200613045206311 1912598196300919567809467)
        ·
          refine ⟨2868897294451379351714201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912598196300919567809467 2868897294451379351714201)
          ·
            refine ⟨2151672970838534513785651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868897294451379351714201 2151672970838534513785651)
            ·
              refine ⟨3227509456257801770678477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151672970838534513785651 3227509456257801770678477)
              ·
                refine ⟨1210316046096675664004429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3227509456257801770678477 1210316046096675664004429)
                ·
                  refine ⟨453868517286253374001661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210316046096675664004429 453868517286253374001661)
                  ·
                    rfl

theorem cell21_1988788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1988788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988788 prefixEnd_1988788 := by exact prefixLift 1988788
  have htrace : WordTrace (prefixWord ++ tailWord_1988788) baseStart_1988788 baseEnd_1988788 := by
    simpa [prefixWord, tailWord_1988788, baseEnd_1988788] using wordTrace_append hprefix tailTrace_1988788
  have hstable : (prefixWord ++ tailWord_1988788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988788).length < 2 ^ (prefixWord ++ tailWord_1988788).sum := by decide
  have hdescent : baseEnd_1988788 < baseStart_1988788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988824 : List Nat := [2, 1, 2, 2, 4, 2, 2, 6]
def baseStart_1988824 : Nat := 118140960795 + 1988824 * 2 ^ 59
def prefixEnd_1988824 : Nat := 4983230072969 + 3 ^ 40 * 1988824 * 2
def baseEnd_1988824 : Nat := 151292244325575103800529

theorem tailTrace_1988824 : CollatzResearch.WordTrace tailWord_1988824 prefixEnd_1988824 151292244325575103800529 := by
  unfold tailWord_1988824
  simp only [CollatzResearch.WordTrace]
  refine ⟨36269185273418893471134763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48358913697891857961513017 36269185273418893471134763)
  ·
    refine ⟨54403777910128340206702145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36269185273418893471134763 54403777910128340206702145)
    ·
      refine ⟨40802833432596255155026609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54403777910128340206702145 40802833432596255155026609)
      ·
        refine ⟨30602125074447191366269957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40802833432596255155026609 30602125074447191366269957)
        ·
          refine ⟨5737898451458848381175617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30602125074447191366269957 5737898451458848381175617)
          ·
            refine ⟨4303423838594136285881713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5737898451458848381175617 4303423838594136285881713)
            ·
              refine ⟨3227567878945602214411285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4303423838594136285881713 3227567878945602214411285)
              ·
                refine ⟨151292244325575103800529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3227567878945602214411285 151292244325575103800529)
                ·
                  rfl

theorem cell21_1988824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_1988824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988824 prefixEnd_1988824 := by exact prefixLift 1988824
  have htrace : WordTrace (prefixWord ++ tailWord_1988824) baseStart_1988824 baseEnd_1988824 := by
    simpa [prefixWord, tailWord_1988824, baseEnd_1988824] using wordTrace_append hprefix tailTrace_1988824
  have hstable : (prefixWord ++ tailWord_1988824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988824).length < 2 ^ (prefixWord ++ tailWord_1988824).sum := by decide
  have hdescent : baseEnd_1988824 < baseStart_1988824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988872 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_1988872 : Nat := 118140960795 + 1988872 * 2 ^ 59
def prefixEnd_1988872 : Nat := 4983230072969 + 3 ^ 40 * 1988872 * 2
def baseEnd_1988872 : Nat := 453887687230687894601489

theorem tailTrace_1988872 : CollatzResearch.WordTrace tailWord_1988872 prefixEnd_1988872 453887687230687894601489 := by
  unfold tailWord_1988872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36270060625331945570008435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48360080833775927426677913 36270060625331945570008435)
  ·
    refine ⟨54405090937997918355012653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36270060625331945570008435 54405090937997918355012653)
    ·
      refine ⟨20401909101749219383129745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54405090937997918355012653 20401909101749219383129745)
      ·
        refine ⟨15301431826311914537347309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20401909101749219383129745 15301431826311914537347309)
        ·
          refine ⟨5738036934866967951505241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15301431826311914537347309 5738036934866967951505241)
          ·
            refine ⟨4303527701150225963628931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5738036934866967951505241 4303527701150225963628931)
            ·
              refine ⟨6455291551725338945443397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4303527701150225963628931 6455291551725338945443397)
              ·
                refine ⟨1210367165948501052270637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6455291551725338945443397 1210367165948501052270637)
                ·
                  refine ⟨453887687230687894601489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210367165948501052270637 453887687230687894601489)
                  ·
                    rfl

theorem cell21_1988872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_1988872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988872 prefixEnd_1988872 := by exact prefixLift 1988872
  have htrace : WordTrace (prefixWord ++ tailWord_1988872) baseStart_1988872 baseEnd_1988872 := by
    simpa [prefixWord, tailWord_1988872, baseEnd_1988872] using wordTrace_append hprefix tailTrace_1988872
  have hstable : (prefixWord ++ tailWord_1988872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988872).length < 2 ^ (prefixWord ++ tailWord_1988872).sum := by decide
  have hdescent : baseEnd_1988872 < baseStart_1988872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988931 : List Nat := [1, 1, 1, 3, 1, 3, 4, 4, 3]
def baseStart_1988931 : Nat := 118140960795 + 1988931 * 2 ^ 59
def prefixEnd_1988931 : Nat := 4983230072969 + 3 ^ 40 * 1988931 * 2
def baseEnd_1988931 : Nat := 453901151834516903118035

theorem tailTrace_1988931 : CollatzResearch.WordTrace tailWord_1988931 prefixEnd_1988931 453901151834516903118035 := by
  unfold tailWord_1988931
  simp only [CollatzResearch.WordTrace]
  refine ⟨72542273157450144216414647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48361515438300096144276431 72542273157450144216414647)
  ·
    refine ⟨108813409736175216324621971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72542273157450144216414647 108813409736175216324621971)
    ·
      refine ⟨163220114604262824486932957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108813409736175216324621971 163220114604262824486932957)
      ·
        refine ⟨61207542976598559182599859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163220114604262824486932957 61207542976598559182599859)
        ·
          refine ⟨91811314464897838773899789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61207542976598559182599859 91811314464897838773899789)
          ·
            refine ⟨34429242924336689540212421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91811314464897838773899789 34429242924336689540212421)
            ·
              refine ⟨6455483048313129288789829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34429242924336689540212421 6455483048313129288789829)
              ·
                refine ⟨1210403071558711741648093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6455483048313129288789829 1210403071558711741648093)
                ·
                  refine ⟨453901151834516903118035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210403071558711741648093 453901151834516903118035)
                  ·
                    rfl

theorem cell21_1988931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 4, 3].length) (baseStart_1988931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988931 prefixEnd_1988931 := by exact prefixLift 1988931
  have htrace : WordTrace (prefixWord ++ tailWord_1988931) baseStart_1988931 baseEnd_1988931 := by
    simpa [prefixWord, tailWord_1988931, baseEnd_1988931] using wordTrace_append hprefix tailTrace_1988931
  have hstable : (prefixWord ++ tailWord_1988931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988931).length < 2 ^ (prefixWord ++ tailWord_1988931).sum := by decide
  have hdescent : baseEnd_1988931 < baseStart_1988931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988982 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1988982 : Nat := 118140960795 + 1988982 * 2 ^ 59
def prefixEnd_1988982 : Nat := 4983230072969 + 3 ^ 40 * 1988982 * 2
def baseEnd_1988982 : Nat := 453912790729352147767931

theorem tailTrace_1988982 : CollatzResearch.WordTrace tailWord_1988982 prefixEnd_1988982 453912790729352147767931 := by
  unfold tailWord_1988982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534008330016586245407575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48362755520176919951014133 4534008330016586245407575)
  ·
    refine ⟨6801012495024879368111363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534008330016586245407575 6801012495024879368111363)
    ·
      refine ⟨10201518742537319052167045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6801012495024879368111363 10201518742537319052167045)
      ·
        refine ⟨1912784764225747322281321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10201518742537319052167045 1912784764225747322281321)
        ·
          refine ⟨1434588573169310491710991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912784764225747322281321 1434588573169310491710991)
          ·
            refine ⟨2151882859753965737566487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434588573169310491710991 2151882859753965737566487)
            ·
              refine ⟨3227824289630948606349731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151882859753965737566487 3227824289630948606349731)
              ·
                refine ⟨4841736434446422909524597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227824289630948606349731 4841736434446422909524597)
                ·
                  refine ⟨453912790729352147767931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4841736434446422909524597 453912790729352147767931)
                  ·
                    rfl

theorem cell21_1988982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1988982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1988982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1988982 prefixEnd_1988982 := by exact prefixLift 1988982
  have htrace : WordTrace (prefixWord ++ tailWord_1988982) baseStart_1988982 baseEnd_1988982 := by
    simpa [prefixWord, tailWord_1988982, baseEnd_1988982] using wordTrace_append hprefix tailTrace_1988982
  have hstable : (prefixWord ++ tailWord_1988982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988982).length < 2 ^ (prefixWord ++ tailWord_1988982).sum := by decide
  have hdescent : baseEnd_1988982 < baseStart_1988982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989041 : List Nat := [1, 2, 2, 4, 1, 4, 2, 2, 3]
def baseStart_1989041 : Nat := 118140960795 + 1989041 * 2 ^ 59
def prefixEnd_1989041 : Nat := 4983230072969 + 3 ^ 40 * 1989041 * 2
def baseEnd_1989041 : Nat := 453926255333181156284477

theorem tailTrace_1989041 : CollatzResearch.WordTrace tailWord_1989041 prefixEnd_1989041 453926255333181156284477 := by
  unfold tailWord_1989041
  simp only [CollatzResearch.WordTrace]
  refine ⟨72546285187051633002918977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48364190124701088668612651 72546285187051633002918977)
  ·
    refine ⟨54409713890288724752189233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72546285187051633002918977 54409713890288724752189233)
    ·
      refine ⟨40807285417716543564141925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54409713890288724752189233 40807285417716543564141925)
      ·
        refine ⟨7651366015821851918276611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40807285417716543564141925 7651366015821851918276611)
        ·
          refine ⟨11477049023732777877414917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7651366015821851918276611 11477049023732777877414917)
          ·
            refine ⟨2151946691949895852015297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11477049023732777877414917 2151946691949895852015297)
            ·
              refine ⟨1613960018962421889011473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2151946691949895852015297 1613960018962421889011473)
              ·
                refine ⟨1210470014221816416758605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613960018962421889011473 1210470014221816416758605)
                ·
                  refine ⟨453926255333181156284477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210470014221816416758605 453926255333181156284477)
                  ·
                    rfl

theorem cell21_1989041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_1989041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989041 prefixEnd_1989041 := by exact prefixLift 1989041
  have htrace : WordTrace (prefixWord ++ tailWord_1989041) baseStart_1989041 baseEnd_1989041 := by
    simpa [prefixWord, tailWord_1989041, baseEnd_1989041] using wordTrace_append hprefix tailTrace_1989041
  have hstable : (prefixWord ++ tailWord_1989041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989041).length < 2 ^ (prefixWord ++ tailWord_1989041).sum := by decide
  have hdescent : baseEnd_1989041 < baseStart_1989041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989052 : List Nat := [2, 2, 2, 4, 1, 1, 3, 6]
def baseStart_1989052 : Nat := 118140960795 + 1989052 * 2 ^ 59
def prefixEnd_1989052 : Nat := 4983230072969 + 3 ^ 40 * 1989052 * 2
def baseEnd_1989052 : Nat := 151309588561015860533707

theorem tailTrace_1989052 : CollatzResearch.WordTrace tailWord_1989052 prefixEnd_1989052 151309588561015860533707 := by
  unfold tailWord_1989052
  simp only [CollatzResearch.WordTrace]
  refine ⟨36273343195005890940784705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48364457593341187921046273 36273343195005890940784705)
  ·
    refine ⟨27205007396254418205588529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36273343195005890940784705 27205007396254418205588529)
    ·
      refine ⟨20403755547190813654191397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27205007396254418205588529 20403755547190813654191397)
      ·
        refine ⟨3825704165098277560160887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20403755547190813654191397 3825704165098277560160887)
        ·
          refine ⟨5738556247647416340241331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825704165098277560160887 5738556247647416340241331)
          ·
            refine ⟨8607834371471124510361997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5738556247647416340241331 8607834371471124510361997)
            ·
              refine ⟨3227937889301671691385749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8607834371471124510361997 3227937889301671691385749)
              ·
                refine ⟨151309588561015860533707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3227937889301671691385749 151309588561015860533707)
                ·
                  rfl

theorem cell21_1989052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_1989052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989052 prefixEnd_1989052 := by exact prefixLift 1989052
  have htrace : WordTrace (prefixWord ++ tailWord_1989052) baseStart_1989052 baseEnd_1989052 := by
    simpa [prefixWord, tailWord_1989052, baseEnd_1989052] using wordTrace_append hprefix tailTrace_1989052
  have hstable : (prefixWord ++ tailWord_1989052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989052).length < 2 ^ (prefixWord ++ tailWord_1989052).sum := by decide
  have hdescent : baseEnd_1989052 < baseStart_1989052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989066 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1989066 : Nat := 118140960795 + 1989066 * 2 ^ 59
def prefixEnd_1989066 : Nat := 4983230072969 + 3 ^ 40 * 1989066 * 2
def baseEnd_1989066 : Nat := 453931960673786668367759

theorem tailTrace_1989066 : CollatzResearch.WordTrace tailWord_1989066 prefixEnd_1989066 453931960673786668367759 := by
  unfold tailWord_1989066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18136799252990265568144763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48364798007974041515052701 18136799252990265568144763)
  ·
    refine ⟨27205198879485398352217145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18136799252990265568144763 27205198879485398352217145)
    ·
      refine ⟨20403899159614048764162859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27205198879485398352217145 20403899159614048764162859)
      ·
        refine ⟨30605848739421073146244289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20403899159614048764162859 30605848739421073146244289)
        ·
          refine ⟨22954386554565804859683217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30605848739421073146244289 22954386554565804859683217)
          ·
            refine ⟨17215789915924353644762413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22954386554565804859683217 17215789915924353644762413)
            ·
              refine ⟨6455921218471632616785905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17215789915924353644762413 6455921218471632616785905)
              ·
                refine ⟨4841940913853724462589429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6455921218471632616785905 4841940913853724462589429)
                ·
                  refine ⟨453931960673786668367759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4841940913853724462589429 453931960673786668367759)
                  ·
                    rfl

theorem cell21_1989066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1989066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989066 prefixEnd_1989066 := by exact prefixLift 1989066
  have htrace : WordTrace (prefixWord ++ tailWord_1989066) baseStart_1989066 baseEnd_1989066 := by
    simpa [prefixWord, tailWord_1989066, baseEnd_1989066] using wordTrace_append hprefix tailTrace_1989066
  have hstable : (prefixWord ++ tailWord_1989066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989066).length < 2 ^ (prefixWord ++ tailWord_1989066).sum := by decide
  have hdescent : baseEnd_1989066 < baseStart_1989066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989080 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_1989080 : Nat := 118140960795 + 1989080 * 2 ^ 59
def prefixEnd_1989080 : Nat := 4983230072969 + 3 ^ 40 * 1989080 * 2
def baseEnd_1989080 : Nat := 453935155664525755134397

theorem tailTrace_1989080 : CollatzResearch.WordTrace tailWord_1989080 prefixEnd_1989080 453935155664525755134397 := by
  unfold tailWord_1989080
  simp only [CollatzResearch.WordTrace]
  refine ⟨36273853816955171331794347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48365138422606895109059129 36273853816955171331794347)
  ·
    refine ⟨54410780725432756997691521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36273853816955171331794347 54410780725432756997691521)
    ·
      refine ⟨40808085544074567748268641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54410780725432756997691521 40808085544074567748268641)
      ·
        refine ⟨30606064158055925811201481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40808085544074567748268641 30606064158055925811201481)
        ·
          refine ⟨22954548118541944358401111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30606064158055925811201481 22954548118541944358401111)
          ·
            refine ⟨34431822177812916537601667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22954548118541944358401111 34431822177812916537601667)
            ·
              refine ⟨51647733266719374806402501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34431822177812916537601667 51647733266719374806402501)
              ·
                refine ⟨9683949987509882776200469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51647733266719374806402501 9683949987509882776200469)
                ·
                  refine ⟨453935155664525755134397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9683949987509882776200469 453935155664525755134397)
                  ·
                    rfl

theorem cell21_1989080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_1989080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989080 prefixEnd_1989080 := by exact prefixLift 1989080
  have htrace : WordTrace (prefixWord ++ tailWord_1989080) baseStart_1989080 baseEnd_1989080 := by
    simpa [prefixWord, tailWord_1989080, baseEnd_1989080] using wordTrace_append hprefix tailTrace_1989080
  have hstable : (prefixWord ++ tailWord_1989080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989080).length < 2 ^ (prefixWord ++ tailWord_1989080).sum := by decide
  have hdescent : baseEnd_1989080 < baseStart_1989080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989173 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 4]
def baseStart_1989173 : Nat := 118140960795 + 1989173 * 2 ^ 59
def prefixEnd_1989173 : Nat := 4983230072969 + 3 ^ 40 * 1989173 * 2
def baseEnd_1989173 : Nat := 453956379531578260084207

theorem tailTrace_1989173 : CollatzResearch.WordTrace tailWord_1989173 prefixEnd_1989173 453956379531578260084207 := by
  unfold tailWord_1989173
  simp only [CollatzResearch.WordTrace]
  refine ⟨72551099622573419546724173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48367399748382279697816115 72551099622573419546724173)
  ·
    refine ⟨27206662358465032330021565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72551099622573419546724173 27206662358465032330021565)
    ·
      refine ⟨10202498384424387123758087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27206662358465032330021565 10202498384424387123758087)
      ·
        refine ⟨15303747576636580685637131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10202498384424387123758087 15303747576636580685637131)
        ·
          refine ⟨22955621364954871028455697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15303747576636580685637131 22955621364954871028455697)
          ·
            refine ⟨17216716023716153271341773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22955621364954871028455697 17216716023716153271341773)
            ·
              refine ⟨6456268508893557476753165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17216716023716153271341773 6456268508893557476753165)
              ·
                refine ⟨2421100690835084053782437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6456268508893557476753165 2421100690835084053782437)
                ·
                  refine ⟨453956379531578260084207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421100690835084053782437 453956379531578260084207)
                  ·
                    rfl

theorem cell21_1989173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_1989173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989173 prefixEnd_1989173 := by exact prefixLift 1989173
  have htrace : WordTrace (prefixWord ++ tailWord_1989173) baseStart_1989173 baseEnd_1989173 := by
    simpa [prefixWord, tailWord_1989173, baseEnd_1989173] using wordTrace_append hprefix tailTrace_1989173
  have hstable : (prefixWord ++ tailWord_1989173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989173).length < 2 ^ (prefixWord ++ tailWord_1989173).sum := by decide
  have hdescent : baseEnd_1989173 < baseStart_1989173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989221 : List Nat := [1, 3, 1, 3, 5, 1, 1, 6]
def baseStart_1989221 : Nat := 118140960795 + 1989221 * 2 ^ 59
def prefixEnd_1989221 : Nat := 4983230072969 + 3 ^ 40 * 1989221 * 2
def baseEnd_1989221 : Nat := 151322444595180281094703

theorem tailTrace_1989221 : CollatzResearch.WordTrace tailWord_1989221 prefixEnd_1989221 151322444595180281094703 := by
  unfold tailWord_1989221
  simp only [CollatzResearch.WordTrace]
  refine ⟨72552850326399523744471517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48368566884266349162981011 72552850326399523744471517)
  ·
    refine ⟨27207318872399821404176819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72552850326399523744471517 27207318872399821404176819)
    ·
      refine ⟨40810978308599732106265229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27207318872399821404176819 40810978308599732106265229)
      ·
        refine ⟨15304116865724899539849461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40810978308599732106265229 15304116865724899539849461)
        ·
          refine ⟨1434760956161709331860887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15304116865724899539849461 1434760956161709331860887)
          ·
            refine ⟨2152141434242563997791331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1434760956161709331860887 2152141434242563997791331)
            ·
              refine ⟨3228212151363845996686997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152141434242563997791331 3228212151363845996686997)
              ·
                refine ⟨151322444595180281094703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3228212151363845996686997 151322444595180281094703)
                ·
                  rfl

theorem cell21_1989221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 6].length) (baseStart_1989221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989221 prefixEnd_1989221 := by exact prefixLift 1989221
  have htrace : WordTrace (prefixWord ++ tailWord_1989221) baseStart_1989221 baseEnd_1989221 := by
    simpa [prefixWord, tailWord_1989221, baseEnd_1989221] using wordTrace_append hprefix tailTrace_1989221
  have hstable : (prefixWord ++ tailWord_1989221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989221).length < 2 ^ (prefixWord ++ tailWord_1989221).sum := by decide
  have hdescent : baseEnd_1989221 < baseStart_1989221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989252 : List Nat := [2, 3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_1989252 : Nat := 118140960795 + 1989252 * 2 ^ 59
def prefixEnd_1989252 : Nat := 4983230072969 + 3 ^ 40 * 1989252 * 2
def baseEnd_1989252 : Nat := 453974408407891678267379

theorem tailTrace_1989252 : CollatzResearch.WordTrace tailWord_1989252 prefixEnd_1989252 453974408407891678267379 := by
  unfold tailWord_1989252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36276990494643608019425005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48369320659524810692566673 36276990494643608019425005)
  ·
    refine ⟨13603871435491353007284377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36276990494643608019425005 13603871435491353007284377)
    ·
      refine ⟨10202903576618514755463283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13603871435491353007284377 10202903576618514755463283)
      ·
        refine ⟨15304355364927772133194925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10202903576618514755463283 15304355364927772133194925)
        ·
          refine ⟨5739133261847914549948097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15304355364927772133194925 5739133261847914549948097)
          ·
            refine ⟨4304349946385935912461073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5739133261847914549948097 4304349946385935912461073)
            ·
              refine ⟨3228262459789451934345805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4304349946385935912461073 3228262459789451934345805)
              ·
                refine ⟨1210598422421044475379677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3228262459789451934345805 1210598422421044475379677)
                ·
                  refine ⟨453974408407891678267379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210598422421044475379677 453974408407891678267379)
                  ·
                    rfl

theorem cell21_1989252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_1989252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989252 prefixEnd_1989252 := by exact prefixLift 1989252
  have htrace : WordTrace (prefixWord ++ tailWord_1989252) baseStart_1989252 baseEnd_1989252 := by
    simpa [prefixWord, tailWord_1989252, baseEnd_1989252] using wordTrace_append hprefix tailTrace_1989252
  have hstable : (prefixWord ++ tailWord_1989252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989252).length < 2 ^ (prefixWord ++ tailWord_1989252).sum := by decide
  have hdescent : baseEnd_1989252 < baseStart_1989252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989266 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_1989266 : Nat := 118140960795 + 1989266 * 2 ^ 59
def prefixEnd_1989266 : Nat := 4983230072969 + 3 ^ 40 * 1989266 * 2
def baseEnd_1989266 : Nat := 453977603398630765034017

theorem tailTrace_1989266 : CollatzResearch.WordTrace tailWord_1989266 prefixEnd_1989266 453977603398630765034017 := by
  unfold tailWord_1989266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18138622902809124107464913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48369661074157664286573101 18138622902809124107464913)
  ·
    refine ⟨13603967177106843080598685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18138622902809124107464913 13603967177106843080598685)
    ·
      refine ⟨5101487691415066155224507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13603967177106843080598685 5101487691415066155224507)
      ·
        refine ⟨7652231537122599232836761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5101487691415066155224507 7652231537122599232836761)
        ·
          refine ⟨5739173652841949424627571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7652231537122599232836761 5739173652841949424627571)
          ·
            refine ⟨8608760479262924136941357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5739173652841949424627571 8608760479262924136941357)
            ·
              refine ⟨3228285179723596551353009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8608760479262924136941357 3228285179723596551353009)
              ·
                refine ⟨2421213884792697413514757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3228285179723596551353009 2421213884792697413514757)
                ·
                  refine ⟨453977603398630765034017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421213884792697413514757 453977603398630765034017)
                  ·
                    rfl

theorem cell21_1989266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_1989266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989266 prefixEnd_1989266 := by exact prefixLift 1989266
  have htrace : WordTrace (prefixWord ++ tailWord_1989266) baseStart_1989266 baseEnd_1989266 := by
    simpa [prefixWord, tailWord_1989266, baseEnd_1989266] using wordTrace_append hprefix tailTrace_1989266
  have hstable : (prefixWord ++ tailWord_1989266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989266).length < 2 ^ (prefixWord ++ tailWord_1989266).sum := by decide
  have hdescent : baseEnd_1989266 < baseStart_1989266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989308 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1989308 : Nat := 118140960795 + 1989308 * 2 ^ 59
def prefixEnd_1989308 : Nat := 4983230072969 + 3 ^ 40 * 1989308 * 2
def baseEnd_1989308 : Nat := 453987188370848025333931

theorem tailTrace_1989308 : CollatzResearch.WordTrace tailWord_1989308 prefixEnd_1989308 453987188370848025333931 := by
  unfold tailWord_1989308
  simp only [CollatzResearch.WordTrace]
  refine ⟨36278011738542168801444289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48370682318056225068592385 36278011738542168801444289)
  ·
    refine ⟨27208508803906626601083217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36278011738542168801444289 27208508803906626601083217)
    ·
      refine ⟨20406381602929969950812413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27208508803906626601083217 20406381602929969950812413)
      ·
        refine ⟨7652393101098738731554655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20406381602929969950812413 7652393101098738731554655)
        ·
          refine ⟨11478589651648108097331983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7652393101098738731554655 11478589651648108097331983)
          ·
            refine ⟨17217884477472162145997975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11478589651648108097331983 17217884477472162145997975)
            ·
              refine ⟨25826826716208243218996963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17217884477472162145997975 25826826716208243218996963)
              ·
                refine ⟨38740240074312364828495445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25826826716208243218996963 38740240074312364828495445)
                ·
                  refine ⟨453987188370848025333931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38740240074312364828495445 453987188370848025333931)
                  ·
                    rfl

theorem cell21_1989308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1989308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989308 prefixEnd_1989308 := by exact prefixLift 1989308
  have htrace : WordTrace (prefixWord ++ tailWord_1989308) baseStart_1989308 baseEnd_1989308 := by
    simpa [prefixWord, tailWord_1989308, baseEnd_1989308] using wordTrace_append hprefix tailTrace_1989308
  have hstable : (prefixWord ++ tailWord_1989308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989308).length < 2 ^ (prefixWord ++ tailWord_1989308).sum := by decide
  have hdescent : baseEnd_1989308 < baseStart_1989308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989311 : List Nat := [1, 1, 2, 2, 2, 4, 3, 3, 3]
def baseStart_1989311 : Nat := 118140960795 + 1989311 * 2 ^ 59
def prefixEnd_1989311 : Nat := 4983230072969 + 3 ^ 40 * 1989311 * 2
def baseEnd_1989311 : Nat := 453987873011720686783925

theorem tailTrace_1989311 : CollatzResearch.WordTrace tailWord_1989311 prefixEnd_1989311 453987873011720686783925 := by
  unfold tailWord_1989311
  simp only [CollatzResearch.WordTrace]
  refine ⟨72556132896073469115247787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48370755264048979410165191 72556132896073469115247787)
  ·
    refine ⟨108834199344110203672871681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72556132896073469115247787 108834199344110203672871681)
    ·
      refine ⟨81625649508082652754653761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108834199344110203672871681 81625649508082652754653761)
      ·
        refine ⟨61219237131061989565990321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81625649508082652754653761 61219237131061989565990321)
        ·
          refine ⟨45914427848296492174492741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61219237131061989565990321 45914427848296492174492741)
          ·
            refine ⟨8608955221555592282717389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45914427848296492174492741 8608955221555592282717389)
            ·
              refine ⟨3228358208083347106019021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8608955221555592282717389 3228358208083347106019021)
              ·
                refine ⟨1210634328031255164757133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3228358208083347106019021 1210634328031255164757133)
                ·
                  refine ⟨453987873011720686783925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210634328031255164757133 453987873011720686783925)
                  ·
                    rfl

theorem cell21_1989311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 3].length) (baseStart_1989311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989311 prefixEnd_1989311 := by exact prefixLift 1989311
  have htrace : WordTrace (prefixWord ++ tailWord_1989311) baseStart_1989311 baseEnd_1989311 := by
    simpa [prefixWord, tailWord_1989311, baseEnd_1989311] using wordTrace_append hprefix tailTrace_1989311
  have hstable : (prefixWord ++ tailWord_1989311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989311).length < 2 ^ (prefixWord ++ tailWord_1989311).sum := by decide
  have hdescent : baseEnd_1989311 < baseStart_1989311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989353 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_1989353 : Nat := 118140960795 + 1989353 * 2 ^ 59
def prefixEnd_1989353 : Nat := 4983230072969 + 3 ^ 40 * 1989353 * 2
def baseEnd_1989353 : Nat := 453997457983937947083839

theorem tailTrace_1989353 : CollatzResearch.WordTrace tailWord_1989353 prefixEnd_1989353 453997457983937947083839 := by
  unfold tailWord_1989353
  simp only [CollatzResearch.WordTrace]
  refine ⟨72557664761921310288276713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48371776507947540192184475 72557664761921310288276713)
  ·
    refine ⟨54418248571440982716207535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72557664761921310288276713 54418248571440982716207535)
    ·
      refine ⟨81627372857161474074311303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54418248571440982716207535 81627372857161474074311303)
      ·
        refine ⟨122441059285742211111466955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81627372857161474074311303 122441059285742211111466955)
        ·
          refine ⟨183661588928613316667200433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122441059285742211111466955 183661588928613316667200433)
          ·
            refine ⟨137746191696459987500400325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183661588928613316667200433 137746191696459987500400325)
            ·
              refine ⟨25827410943086247656325061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137746191696459987500400325 25827410943086247656325061)
              ·
                refine ⟨4842639551828671435560949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25827410943086247656325061 4842639551828671435560949)
                ·
                  refine ⟨453997457983937947083839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4842639551828671435560949 453997457983937947083839)
                  ·
                    rfl

theorem cell21_1989353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_1989353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989353 prefixEnd_1989353 := by exact prefixLift 1989353
  have htrace : WordTrace (prefixWord ++ tailWord_1989353) baseStart_1989353 baseEnd_1989353 := by
    simpa [prefixWord, tailWord_1989353, baseEnd_1989353] using wordTrace_append hprefix tailTrace_1989353
  have hstable : (prefixWord ++ tailWord_1989353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989353).length < 2 ^ (prefixWord ++ tailWord_1989353).sum := by decide
  have hdescent : baseEnd_1989353 < baseStart_1989353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989480 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_1989480 : Nat := 118140960795 + 1989480 * 2 ^ 59
def prefixEnd_1989480 : Nat := 4983230072969 + 3 ^ 40 * 1989480 * 2
def baseEnd_1989480 : Nat := 454026441114213948466913

theorem tailTrace_1989480 : CollatzResearch.WordTrace tailWord_1989480 prefixEnd_1989480 454026441114213948466913 := by
  unfold tailWord_1989480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36281148416230605489074947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48374864554974140652099929 36281148416230605489074947)
  ·
    refine ⟨54421722624345908233612421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36281148416230605489074947 54421722624345908233612421)
    ·
      refine ⟨10204072992064857793802329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54421722624345908233612421 10204072992064857793802329)
      ·
        refine ⟨7653054744048643345351747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10204072992064857793802329 7653054744048643345351747)
        ·
          refine ⟨11479582116072965018027621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7653054744048643345351747 11479582116072965018027621)
          ·
            refine ⟨2152421646763680940880179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11479582116072965018027621 2152421646763680940880179)
            ·
              refine ⟨3228632470145521411320269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152421646763680940880179 3228632470145521411320269)
              ·
                refine ⟨1210737176304570529245101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3228632470145521411320269 1210737176304570529245101)
                ·
                  refine ⟨454026441114213948466913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1210737176304570529245101 454026441114213948466913)
                  ·
                    rfl

theorem cell21_1989480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_1989480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989480 prefixEnd_1989480 := by exact prefixLift 1989480
  have htrace : WordTrace (prefixWord ++ tailWord_1989480) baseStart_1989480 baseEnd_1989480 := by
    simpa [prefixWord, tailWord_1989480, baseEnd_1989480] using wordTrace_append hprefix tailTrace_1989480
  have hstable : (prefixWord ++ tailWord_1989480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989480).length < 2 ^ (prefixWord ++ tailWord_1989480).sum := by decide
  have hdescent : baseEnd_1989480 < baseStart_1989480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989643 : List Nat := [1, 1, 1, 1, 6, 2, 4, 5]
def baseStart_1989643 : Nat := 118140960795 + 1989643 * 2 ^ 59
def prefixEnd_1989643 : Nat := 4983230072969 + 3 ^ 40 * 1989643 * 2
def baseEnd_1989643 : Nat := 151354546644987295749971

theorem tailTrace_1989643 : CollatzResearch.WordTrace tailWord_1989643 prefixEnd_1989643 151354546644987295749971 := by
  unfold tailWord_1989643
  simp only [CollatzResearch.WordTrace]
  refine ⟨72568241930870689816333583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48378827953913793210889055 72568241930870689816333583)
  ·
    refine ⟨108852362896306034724500375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72568241930870689816333583 108852362896306034724500375)
    ·
      refine ⟨163278544344459052086750563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108852362896306034724500375 163278544344459052086750563)
      ·
        refine ⟨244917816516688578130125845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163278544344459052086750563 244917816516688578130125845)
        ·
          refine ⟨11480522649219777099849649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244917816516688578130125845 11480522649219777099849649)
          ·
            refine ⟨8610391986914832824887237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11480522649219777099849649 8610391986914832824887237)
            ·
              refine ⟨1614448497546531154666357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8610391986914832824887237 1614448497546531154666357)
              ·
                refine ⟨151354546644987295749971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1614448497546531154666357 151354546644987295749971)
                ·
                  rfl

theorem cell21_1989643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 5].length) (baseStart_1989643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989643 prefixEnd_1989643 := by exact prefixLift 1989643
  have htrace : WordTrace (prefixWord ++ tailWord_1989643) baseStart_1989643 baseEnd_1989643 := by
    simpa [prefixWord, tailWord_1989643, baseEnd_1989643] using wordTrace_append hprefix tailTrace_1989643
  have hstable : (prefixWord ++ tailWord_1989643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989643).length < 2 ^ (prefixWord ++ tailWord_1989643).sum := by decide
  have hdescent : baseEnd_1989643 < baseStart_1989643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989660 : List Nat := [2, 2, 3, 1, 5, 1, 7]
def baseStart_1989660 : Nat := 118140960795 + 1989660 * 2 ^ 59
def prefixEnd_1989660 : Nat := 4983230072969 + 3 ^ 40 * 1989660 * 2
def baseEnd_1989660 : Nat := 50451946618508181718505

theorem tailTrace_1989660 : CollatzResearch.WordTrace tailWord_1989660 prefixEnd_1989660 50451946618508181718505 := by
  unfold tailWord_1989660
  simp only [CollatzResearch.WordTrace]
  refine ⟨36284430985904550859851217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48379241314539401146468289 36284430985904550859851217)
  ·
    refine ⟨27213323239428413144888413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36284430985904550859851217 27213323239428413144888413)
    ·
      refine ⟨10204996214785654929333155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27213323239428413144888413 10204996214785654929333155)
      ·
        refine ⟨15307494322178482393999733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10204996214785654929333155 15307494322178482393999733)
        ·
          refine ⟨1435077592704232724437475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15307494322178482393999733 1435077592704232724437475)
          ·
            refine ⟨2152616389056349086656213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435077592704232724437475 2152616389056349086656213)
            ·
              refine ⟨50451946618508181718505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2152616389056349086656213 50451946618508181718505)
              ·
                rfl

theorem cell21_1989660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 7].length) (baseStart_1989660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989660 prefixEnd_1989660 := by exact prefixLift 1989660
  have htrace : WordTrace (prefixWord ++ tailWord_1989660) baseStart_1989660 baseEnd_1989660 := by
    simpa [prefixWord, tailWord_1989660, baseEnd_1989660] using wordTrace_append hprefix tailTrace_1989660
  have hstable : (prefixWord ++ tailWord_1989660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989660).length < 2 ^ (prefixWord ++ tailWord_1989660).sum := by decide
  have hdescent : baseEnd_1989660 < baseStart_1989660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989733 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_1989733 : Nat := 118140960795 + 1989733 * 2 ^ 59
def prefixEnd_1989733 : Nat := 4983230072969 + 3 ^ 40 * 1989733 * 2
def baseEnd_1989733 : Nat := 454084179161141730749729

theorem tailTrace_1989733 : CollatzResearch.WordTrace tailWord_1989733 prefixEnd_1989733 454084179161141730749729 := by
  unfold tailWord_1989733
  simp only [CollatzResearch.WordTrace]
  refine ⟨72571524500544635187109853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48381016333696423458073235 72571524500544635187109853)
  ·
    refine ⟨27214321687704238195166195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72571524500544635187109853 27214321687704238195166195)
    ·
      refine ⟨40821482531556357292749293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27214321687704238195166195 40821482531556357292749293)
      ·
        refine ⟨15308055949333633984780985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40821482531556357292749293 15308055949333633984780985)
        ·
          refine ⟨11481041962000225488585739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15308055949333633984780985 11481041962000225488585739)
          ·
            refine ⟨17221562943000338232878609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481041962000225488585739 17221562943000338232878609)
            ·
              refine ⟨12916172207250253674658957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17221562943000338232878609 12916172207250253674658957)
              ·
                refine ⟨4843564577718845127997109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12916172207250253674658957 4843564577718845127997109)
                ·
                  refine ⟨454084179161141730749729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4843564577718845127997109 454084179161141730749729)
                  ·
                    rfl

theorem cell21_1989733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_1989733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989733 prefixEnd_1989733 := by exact prefixLift 1989733
  have htrace : WordTrace (prefixWord ++ tailWord_1989733) baseStart_1989733 baseEnd_1989733 := by
    simpa [prefixWord, tailWord_1989733, baseEnd_1989733] using wordTrace_append hprefix tailTrace_1989733
  have hstable : (prefixWord ++ tailWord_1989733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989733).length < 2 ^ (prefixWord ++ tailWord_1989733).sum := by decide
  have hdescent : baseEnd_1989733 < baseStart_1989733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989750 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1989750 : Nat := 118140960795 + 1989750 * 2 ^ 59
def prefixEnd_1989750 : Nat := 4983230072969 + 3 ^ 40 * 1989750 * 2
def baseEnd_1989750 : Nat := 454088058792753478966361

theorem tailTrace_1989750 : CollatzResearch.WordTrace tailWord_1989750 prefixEnd_1989750 454088058792753478966361 := by
  unfold tailWord_1989750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4535759033842690443154919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48381429694322031393652469 4535759033842690443154919)
  ·
    refine ⟨6803638550764035664732379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4535759033842690443154919 6803638550764035664732379)
    ·
      refine ⟨10205457826146053497098569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803638550764035664732379 10205457826146053497098569)
      ·
        refine ⟨7654093369609540122823927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10205457826146053497098569 7654093369609540122823927)
        ·
          refine ⟨11481140054414310184235891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654093369609540122823927 11481140054414310184235891)
          ·
            refine ⟨17221710081621465276353837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11481140054414310184235891 17221710081621465276353837)
            ·
              refine ⟨6458141280608049478632689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17221710081621465276353837 6458141280608049478632689)
              ·
                refine ⟨4843605960456037108974517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6458141280608049478632689 4843605960456037108974517)
                ·
                  refine ⟨454088058792753478966361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4843605960456037108974517 454088058792753478966361)
                  ·
                    rfl

theorem cell21_1989750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1989750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989750 prefixEnd_1989750 := by exact prefixLift 1989750
  have htrace : WordTrace (prefixWord ++ tailWord_1989750) baseStart_1989750 baseEnd_1989750 := by
    simpa [prefixWord, tailWord_1989750, baseEnd_1989750] using wordTrace_append hprefix tailTrace_1989750
  have hstable : (prefixWord ++ tailWord_1989750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989750).length < 2 ^ (prefixWord ++ tailWord_1989750).sum := by decide
  have hdescent : baseEnd_1989750 < baseStart_1989750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989823 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_1989823 : Nat := 118140960795 + 1989823 * 2 ^ 59
def prefixEnd_1989823 : Nat := 4983230072969 + 3 ^ 40 * 1989823 * 2
def baseEnd_1989823 : Nat := 454104718387321574249545

theorem tailTrace_1989823 : CollatzResearch.WordTrace tailWord_1989823 prefixEnd_1989823 454104718387321574249545 := by
  unfold tailWord_1989823
  simp only [CollatzResearch.WordTrace]
  refine ⟨72574807070218580557886123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48383204713479053705257415 72574807070218580557886123)
  ·
    refine ⟨108862210605327870836829185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72574807070218580557886123 108862210605327870836829185)
    ·
      refine ⟨81646657953995903127621889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108862210605327870836829185 81646657953995903127621889)
      ·
        refine ⟨61234993465496927345716417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81646657953995903127621889 61234993465496927345716417)
        ·
          refine ⟨45926245099122695509287313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61234993465496927345716417 45926245099122695509287313)
          ·
            refine ⟨34444683824342021631965485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45926245099122695509287313 34444683824342021631965485)
            ·
              refine ⟨12916756434128258111987057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34444683824342021631965485 12916756434128258111987057)
              ·
                refine ⟨9687567325596193583990293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12916756434128258111987057 9687567325596193583990293)
                ·
                  refine ⟨454104718387321574249545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9687567325596193583990293 454104718387321574249545)
                  ·
                    rfl

theorem cell21_1989823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_1989823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989823 prefixEnd_1989823 := by exact prefixLift 1989823
  have htrace : WordTrace (prefixWord ++ tailWord_1989823) baseStart_1989823 baseEnd_1989823 := by
    simpa [prefixWord, tailWord_1989823, baseEnd_1989823] using wordTrace_append hprefix tailTrace_1989823
  have hstable : (prefixWord ++ tailWord_1989823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989823).length < 2 ^ (prefixWord ++ tailWord_1989823).sum := by decide
  have hdescent : baseEnd_1989823 < baseStart_1989823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989857 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 4]
def baseStart_1989857 : Nat := 118140960795 + 1989857 * 2 ^ 59
def prefixEnd_1989857 : Nat := 4983230072969 + 3 ^ 40 * 1989857 * 2
def baseEnd_1989857 : Nat := 454112477650545070682809

theorem tailTrace_1989857 : CollatzResearch.WordTrace tailWord_1989857 prefixEnd_1989857 454112477650545070682809 := by
  unfold tailWord_1989857
  simp only [CollatzResearch.WordTrace]
  refine ⟨72576047152095404364623825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48384031434730269576415883 72576047152095404364623825)
  ·
    refine ⟨54432035364071553273467869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72576047152095404364623825 54432035364071553273467869)
    ·
      refine ⟨20412013261526832477550451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54432035364071553273467869 20412013261526832477550451)
      ·
        refine ⟨30618019892290248716325677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20412013261526832477550451 30618019892290248716325677)
        ·
          refine ⟨11481757459608843268622129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30618019892290248716325677 11481757459608843268622129)
          ·
            refine ⟨8611318094706632451466597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11481757459608843268622129 8611318094706632451466597)
            ·
              refine ⟨1614622142757493584649987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8611318094706632451466597 1614622142757493584649987)
              ·
                refine ⟨2421933214136240376974981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614622142757493584649987 2421933214136240376974981)
                ·
                  refine ⟨454112477650545070682809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2421933214136240376974981 454112477650545070682809)
                  ·
                    rfl

theorem cell21_1989857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_1989857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989857 prefixEnd_1989857 := by exact prefixLift 1989857
  have htrace : WordTrace (prefixWord ++ tailWord_1989857) baseStart_1989857 baseEnd_1989857 := by
    simpa [prefixWord, tailWord_1989857, baseEnd_1989857] using wordTrace_append hprefix tailTrace_1989857
  have hstable : (prefixWord ++ tailWord_1989857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989857).length < 2 ^ (prefixWord ++ tailWord_1989857).sum := by decide
  have hdescent : baseEnd_1989857 < baseStart_1989857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989916 : List Nat := [2, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_1989916 : Nat := 118140960795 + 1989916 * 2 ^ 59
def prefixEnd_1989916 : Nat := 4983230072969 + 3 ^ 40 * 1989916 * 2
def baseEnd_1989916 : Nat := 454125942254374079199355

theorem tailTrace_1989916 : CollatzResearch.WordTrace tailWord_1989916 prefixEnd_1989916 454125942254374079199355 := by
  unfold tailWord_1989916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36289099529440828720510801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48385466039254438294014401 36289099529440828720510801)
  ·
    refine ⟨27216824647080621540383101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36289099529440828720510801 27216824647080621540383101)
    ·
      refine ⟨10206309242655233077643663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27216824647080621540383101 10206309242655233077643663)
      ·
        refine ⟨15309463863982849616465495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10206309242655233077643663 15309463863982849616465495)
        ·
          refine ⟨22964195795974274424698243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15309463863982849616465495 22964195795974274424698243)
          ·
            refine ⟨34446293693961411637047365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22964195795974274424698243 34446293693961411637047365)
            ·
              refine ⟨6458680067617764681946381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34446293693961411637047365 6458680067617764681946381)
              ·
                refine ⟨2422005025356661755729893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6458680067617764681946381 2422005025356661755729893)
                ·
                  refine ⟨454125942254374079199355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422005025356661755729893 454125942254374079199355)
                  ·
                    rfl

theorem cell21_1989916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_1989916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989916 prefixEnd_1989916 := by exact prefixLift 1989916
  have htrace : WordTrace (prefixWord ++ tailWord_1989916) baseStart_1989916 baseEnd_1989916 := by
    simpa [prefixWord, tailWord_1989916, baseEnd_1989916] using wordTrace_append hprefix tailTrace_1989916
  have hstable : (prefixWord ++ tailWord_1989916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989916).length < 2 ^ (prefixWord ++ tailWord_1989916).sum := by decide
  have hdescent : baseEnd_1989916 < baseStart_1989916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989944 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_1989944 : Nat := 118140960795 + 1989944 * 2 ^ 59
def prefixEnd_1989944 : Nat := 4983230072969 + 3 ^ 40 * 1989944 * 2
def baseEnd_1989944 : Nat := 454132332235852252732631

theorem tailTrace_1989944 : CollatzResearch.WordTrace tailWord_1989944 prefixEnd_1989944 454132332235852252732631 := by
  unfold tailWord_1989944
  simp only [CollatzResearch.WordTrace]
  refine ⟨36289610151390109111520443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48386146868520145482027257 36289610151390109111520443)
  ·
    refine ⟨54434415227085163667280665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36289610151390109111520443 54434415227085163667280665)
    ·
      refine ⟨40825811420313872750460499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54434415227085163667280665 40825811420313872750460499)
      ·
        refine ⟨61238717130470809125690749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40825811420313872750460499 61238717130470809125690749)
        ·
          refine ⟨22964518923926553422134031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61238717130470809125690749 22964518923926553422134031)
          ·
            refine ⟨34446778385889830133201047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22964518923926553422134031 34446778385889830133201047)
            ·
              refine ⟨51670167578834745199801571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34446778385889830133201047 51670167578834745199801571)
              ·
                refine ⟨77505251368252117799702357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51670167578834745199801571 77505251368252117799702357)
                ·
                  refine ⟨454132332235852252732631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77505251368252117799702357 454132332235852252732631)
                  ·
                    rfl

theorem cell21_1989944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_1989944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989944 prefixEnd_1989944 := by exact prefixLift 1989944
  have htrace : WordTrace (prefixWord ++ tailWord_1989944) baseStart_1989944 baseEnd_1989944 := by
    simpa [prefixWord, tailWord_1989944, baseEnd_1989944] using wordTrace_append hprefix tailTrace_1989944
  have hstable : (prefixWord ++ tailWord_1989944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989944).length < 2 ^ (prefixWord ++ tailWord_1989944).sum := by decide
  have hdescent : baseEnd_1989944 < baseStart_1989944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1989981 : List Nat := [1, 4, 5, 1, 1, 1, 1, 7]
def baseStart_1989981 : Nat := 118140960795 + 1989981 * 2 ^ 59
def prefixEnd_1989981 : Nat := 4983230072969 + 3 ^ 40 * 1989981 * 2
def baseEnd_1989981 : Nat := 151380258713316136871963

theorem tailTrace_1989981 : CollatzResearch.WordTrace tailWord_1989981 prefixEnd_1989981 151380258713316136871963 := by
  unfold tailWord_1989981
  simp only [CollatzResearch.WordTrace]
  refine ⟨72580569803646173542137797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48387046535764115694758531 72580569803646173542137797)
  ·
    refine ⟨13608856838183657539150837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72580569803646173542137797 13608856838183657539150837)
    ·
      refine ⟨1275830328579717894295391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13608856838183657539150837 1275830328579717894295391)
      ·
        refine ⟨1913745492869576841443087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275830328579717894295391 1913745492869576841443087)
        ·
          refine ⟨2870618239304365262164631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913745492869576841443087 2870618239304365262164631)
          ·
            refine ⟨4305927358956547893246947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870618239304365262164631 4305927358956547893246947)
            ·
              refine ⟨6458891038434821839870421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305927358956547893246947 6458891038434821839870421)
              ·
                refine ⟨151380258713316136871963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6458891038434821839870421 151380258713316136871963)
                ·
                  rfl

theorem cell21_1989981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 7].length) (baseStart_1989981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1989981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1989981 prefixEnd_1989981 := by exact prefixLift 1989981
  have htrace : WordTrace (prefixWord ++ tailWord_1989981) baseStart_1989981 baseEnd_1989981 := by
    simpa [prefixWord, tailWord_1989981, baseEnd_1989981] using wordTrace_append hprefix tailTrace_1989981
  have hstable : (prefixWord ++ tailWord_1989981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1989981).length < 2 ^ (prefixWord ++ tailWord_1989981).sum := by decide
  have hdescent : baseEnd_1989981 < baseStart_1989981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1989981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990096 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_1990096 : Nat := 118140960795 + 1990096 * 2 ^ 59
def prefixEnd_1990096 : Nat := 4983230072969 + 3 ^ 40 * 1990096 * 2
def baseEnd_1990096 : Nat := 454167020706733766198987

theorem tailTrace_1990096 : CollatzResearch.WordTrace tailWord_1990096 prefixEnd_1990096 454167020706733766198987 := by
  unfold tailWord_1990096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36292382099114774091287071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48389842798819698788382761 36292382099114774091287071)
  ·
    refine ⟨54438573148672161136930607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36292382099114774091287071 54438573148672161136930607)
    ·
      refine ⟨81657859723008241705395911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54438573148672161136930607 81657859723008241705395911)
      ·
        refine ⟨122486789584512362558093867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81657859723008241705395911 122486789584512362558093867)
        ·
          refine ⟨183730184376768543837140801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122486789584512362558093867 183730184376768543837140801)
          ·
            refine ⟨137797638282576407877855601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183730184376768543837140801 137797638282576407877855601)
            ·
              refine ⟨103348228711932305908391701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137797638282576407877855601 103348228711932305908391701)
              ·
                refine ⟨4844448220871826839455861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103348228711932305908391701 4844448220871826839455861)
                ·
                  refine ⟨454167020706733766198987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4844448220871826839455861 454167020706733766198987)
                  ·
                    rfl

theorem cell21_1990096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_1990096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990096 prefixEnd_1990096 := by exact prefixLift 1990096
  have htrace : WordTrace (prefixWord ++ tailWord_1990096) baseStart_1990096 baseEnd_1990096 := by
    simpa [prefixWord, tailWord_1990096, baseEnd_1990096] using wordTrace_append hprefix tailTrace_1990096
  have hstable : (prefixWord ++ tailWord_1990096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990096).length < 2 ^ (prefixWord ++ tailWord_1990096).sum := by decide
  have hdescent : baseEnd_1990096 < baseStart_1990096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990130 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1990130 : Nat := 118140960795 + 1990130 * 2 ^ 59
def prefixEnd_1990130 : Nat := 4983230072969 + 3 ^ 40 * 1990130 * 2
def baseEnd_1990130 : Nat := 454174779969957262632251

theorem tailTrace_1990130 : CollatzResearch.WordTrace tailWord_1990130 prefixEnd_1990130 454174779969957262632251 := by
  unfold tailWord_1990130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18146501070026592997327961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48390669520070914659541229 18146501070026592997327961)
  ·
    refine ⟨13609875802519944747995971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18146501070026592997327961 13609875802519944747995971)
    ·
      refine ⟨20414813703779917121993957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13609875802519944747995971 20414813703779917121993957)
      ·
        refine ⟨3827777569458734460373867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20414813703779917121993957 3827777569458734460373867)
        ·
          refine ⟨5741666354188101690560801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827777569458734460373867 5741666354188101690560801)
          ·
            refine ⟨4306249765641076267920601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5741666354188101690560801 4306249765641076267920601)
            ·
              refine ⟨3229687324230807200940451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306249765641076267920601 3229687324230807200940451)
              ·
                refine ⟨4844530986346210801410677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3229687324230807200940451 4844530986346210801410677)
                ·
                  refine ⟨454174779969957262632251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4844530986346210801410677 454174779969957262632251)
                  ·
                    rfl

theorem cell21_1990130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1990130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990130 prefixEnd_1990130 := by exact prefixLift 1990130
  have htrace : WordTrace (prefixWord ++ tailWord_1990130) baseStart_1990130 baseEnd_1990130 := by
    simpa [prefixWord, tailWord_1990130, baseEnd_1990130] using wordTrace_append hprefix tailTrace_1990130
  have hstable : (prefixWord ++ tailWord_1990130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990130).length < 2 ^ (prefixWord ++ tailWord_1990130).sum := by decide
  have hdescent : baseEnd_1990130 < baseStart_1990130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990282 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_1990282 : Nat := 118140960795 + 1990282 * 2 ^ 59
def prefixEnd_1990282 : Nat := 4983230072969 + 3 ^ 40 * 1990282 * 2
def baseEnd_1990282 : Nat := 454209468440838776098607

theorem tailTrace_1990282 : CollatzResearch.WordTrace tailWord_1990282 prefixEnd_1990282 454209468440838776098607 := by
  unfold tailWord_1990282
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147887043888925487211275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48394365450370467965896733 18147887043888925487211275)
  ·
    refine ⟨27221830565833388230816913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18147887043888925487211275 27221830565833388230816913)
    ·
      refine ⟨20416372924375041173112685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27221830565833388230816913 20416372924375041173112685)
      ·
        refine ⟨7656139846640640439917257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20416372924375041173112685 7656139846640640439917257)
        ·
          refine ⟨5742104884980480329937943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7656139846640640439917257 5742104884980480329937943)
          ·
            refine ⟨8613157327470720494906915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742104884980480329937943 8613157327470720494906915)
            ·
              refine ⟨12919735991206080742360373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8613157327470720494906915 12919735991206080742360373)
              ·
                refine ⟨1211225249175570069596285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12919735991206080742360373 1211225249175570069596285)
                ·
                  refine ⟨454209468440838776098607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211225249175570069596285 454209468440838776098607)
                  ·
                    rfl

theorem cell21_1990282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_1990282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990282 prefixEnd_1990282 := by exact prefixLift 1990282
  have htrace : WordTrace (prefixWord ++ tailWord_1990282) baseStart_1990282 baseEnd_1990282 := by
    simpa [prefixWord, tailWord_1990282, baseEnd_1990282] using wordTrace_append hprefix tailTrace_1990282
  have hstable : (prefixWord ++ tailWord_1990282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990282).length < 2 ^ (prefixWord ++ tailWord_1990282).sum := by decide
  have hdescent : baseEnd_1990282 < baseStart_1990282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990296 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_1990296 : Nat := 118140960795 + 1990296 * 2 ^ 59
def prefixEnd_1990296 : Nat := 4983230072969 + 3 ^ 40 * 1990296 * 2
def baseEnd_1990296 : Nat := 454212663431577862865245

theorem tailTrace_1990296 : CollatzResearch.WordTrace tailWord_1990296 prefixEnd_1990296 454212663431577862865245 := by
  unfold tailWord_1990296
  simp only [CollatzResearch.WordTrace]
  refine ⟨36296029398752491169927371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48394705865003321559903161 36296029398752491169927371)
  ·
    refine ⟨54444044098128736754891057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36296029398752491169927371 54444044098128736754891057)
    ·
      refine ⟨40833033073596552566168293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54444044098128736754891057 40833033073596552566168293)
      ·
        refine ⟨7656193701299353606156555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40833033073596552566168293 7656193701299353606156555)
        ·
          refine ⟨11484290551949030409234833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7656193701299353606156555 11484290551949030409234833)
          ·
            refine ⟨8613217913961772806926125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11484290551949030409234833 8613217913961772806926125)
            ·
              refine ⟨3229956717735664802597297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8613217913961772806926125 3229956717735664802597297)
              ·
                refine ⟨2422467538301748601947973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229956717735664802597297 2422467538301748601947973)
                ·
                  refine ⟨454212663431577862865245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422467538301748601947973 454212663431577862865245)
                  ·
                    rfl

theorem cell21_1990296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_1990296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990296 prefixEnd_1990296 := by exact prefixLift 1990296
  have htrace : WordTrace (prefixWord ++ tailWord_1990296) baseStart_1990296 baseEnd_1990296 := by
    simpa [prefixWord, tailWord_1990296, baseEnd_1990296] using wordTrace_append hprefix tailTrace_1990296
  have hstable : (prefixWord ++ tailWord_1990296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990296).length < 2 ^ (prefixWord ++ tailWord_1990296).sum := by decide
  have hdescent : baseEnd_1990296 < baseStart_1990296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990327 : List Nat := [1, 1, 3, 1, 5, 3, 2, 5]
def baseStart_1990327 : Nat := 118140960795 + 1990327 * 2 ^ 59
def prefixEnd_1990327 : Nat := 4983230072969 + 3 ^ 40 * 1990327 * 2
def baseEnd_1990327 : Nat := 151406579351309565949505

theorem tailTrace_1990327 : CollatzResearch.WordTrace tailWord_1990327 prefixEnd_1990327 151406579351309565949505 := by
  unfold tailWord_1990327
  simp only [CollatzResearch.WordTrace]
  refine ⟨72593189460392674634233235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48395459640261783089488823 72593189460392674634233235)
  ·
    refine ⟨108889784190589011951349853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72593189460392674634233235 108889784190589011951349853)
    ·
      refine ⟨40833669071470879481756195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108889784190589011951349853 40833669071470879481756195)
      ·
        refine ⟨61250503607206319222634293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40833669071470879481756195 61250503607206319222634293)
        ·
          refine ⟨5742234713175592427121965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61250503607206319222634293 5742234713175592427121965)
          ·
            refine ⟨2153338017440847160170737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5742234713175592427121965 2153338017440847160170737)
            ·
              refine ⟨1615003513080635370128053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153338017440847160170737 1615003513080635370128053)
              ·
                refine ⟨151406579351309565949505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1615003513080635370128053 151406579351309565949505)
                ·
                  rfl

theorem cell21_1990327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 5].length) (baseStart_1990327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990327 prefixEnd_1990327 := by exact prefixLift 1990327
  have htrace : WordTrace (prefixWord ++ tailWord_1990327) baseStart_1990327 baseEnd_1990327 := by
    simpa [prefixWord, tailWord_1990327, baseEnd_1990327] using wordTrace_append hprefix tailTrace_1990327
  have hstable : (prefixWord ++ tailWord_1990327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990327).length < 2 ^ (prefixWord ++ tailWord_1990327).sum := by decide
  have hdescent : baseEnd_1990327 < baseStart_1990327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990431 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 4]
def baseStart_1990431 : Nat := 118140960795 + 1990431 * 2 ^ 59
def prefixEnd_1990431 : Nat := 4983230072969 + 3 ^ 40 * 1990431 * 2
def baseEnd_1990431 : Nat := 454243472270847628114969

theorem tailTrace_1990431 : CollatzResearch.WordTrace tailWord_1990431 prefixEnd_1990431 454243472270847628114969 := by
  unfold tailWord_1990431
  simp only [CollatzResearch.WordTrace]
  refine ⟨72596982652015900396019147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48397988434677266930679431 72596982652015900396019147)
  ·
    refine ⟨108895473978023850594028721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72596982652015900396019147 108895473978023850594028721)
    ·
      refine ⟨81671605483517887945521541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108895473978023850594028721 81671605483517887945521541)
      ·
        refine ⟨15313426028159603989785289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81671605483517887945521541 15313426028159603989785289)
        ·
          refine ⟨11485069521119702992338967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15313426028159603989785289 11485069521119702992338967)
          ·
            refine ⟨17227604281679554488508451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11485069521119702992338967 17227604281679554488508451)
            ·
              refine ⟨25841406422519331732762677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17227604281679554488508451 25841406422519331732762677)
              ·
                refine ⟨2422631852111187349946501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25841406422519331732762677 2422631852111187349946501)
                ·
                  refine ⟨454243472270847628114969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422631852111187349946501 454243472270847628114969)
                  ·
                    rfl

theorem cell21_1990431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 4].length) (baseStart_1990431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990431 prefixEnd_1990431 := by exact prefixLift 1990431
  have htrace : WordTrace (prefixWord ++ tailWord_1990431) baseStart_1990431 baseEnd_1990431 := by
    simpa [prefixWord, tailWord_1990431, baseEnd_1990431] using wordTrace_append hprefix tailTrace_1990431
  have hstable : (prefixWord ++ tailWord_1990431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990431).length < 2 ^ (prefixWord ++ tailWord_1990431).sum := by decide
  have hdescent : baseEnd_1990431 < baseStart_1990431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990462 : List Nat := [4, 2, 1, 2, 2, 2, 8]
def baseStart_1990462 : Nat := 118140960795 + 1990462 * 2 ^ 59
def prefixEnd_1990462 : Nat := 4983230072969 + 3 ^ 40 * 1990462 * 2
def baseEnd_1990462 : Nat := 50472282988133162566471

theorem tailTrace_1990462 : CollatzResearch.WordTrace tailWord_1990462 prefixEnd_1990462 50472282988133162566471 := by
  unfold tailWord_1990462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074764164362949086299705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48398742209935728460265093 9074764164362949086299705)
  ·
    refine ⟨6806073123272211814724779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9074764164362949086299705 6806073123272211814724779)
    ·
      refine ⟨10209109684908317722087169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6806073123272211814724779 10209109684908317722087169)
      ·
        refine ⟨7656832263681238291565377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10209109684908317722087169 7656832263681238291565377)
        ·
          refine ⟨5742624197760928718674033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7656832263681238291565377 5742624197760928718674033)
          ·
            refine ⟨4306968148320696539005525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5742624197760928718674033 4306968148320696539005525)
            ·
              refine ⟨50472282988133162566471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4306968148320696539005525 50472282988133162566471)
              ·
                rfl

theorem cell21_1990462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 8].length) (baseStart_1990462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990462 prefixEnd_1990462 := by exact prefixLift 1990462
  have htrace : WordTrace (prefixWord ++ tailWord_1990462) baseStart_1990462 baseEnd_1990462 := by
    simpa [prefixWord, tailWord_1990462, baseEnd_1990462] using wordTrace_append hprefix tailTrace_1990462
  have hstable : (prefixWord ++ tailWord_1990462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990462).length < 2 ^ (prefixWord ++ tailWord_1990462).sum := by decide
  have hdescent : baseEnd_1990462 < baseStart_1990462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990679 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 3]
def baseStart_1990679 : Nat := 118140960795 + 1990679 * 2 ^ 59
def prefixEnd_1990679 : Nat := 4983230072969 + 3 ^ 40 * 1990679 * 2
def baseEnd_1990679 : Nat := 454300069249654307981129

theorem tailTrace_1990679 : CollatzResearch.WordTrace tailWord_1990679 prefixEnd_1990679 454300069249654307981129 := by
  unfold tailWord_1990679
  simp only [CollatzResearch.WordTrace]
  refine ⟨72606027955117438751047091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48404018636744959167364727 72606027955117438751047091)
  ·
    refine ⟨108909041932676158126570637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72606027955117438751047091 108909041932676158126570637)
    ·
      refine ⟨40840890724753559297463989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108909041932676158126570637 40840890724753559297463989)
      ·
        refine ⟨3828833505445646184137249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40840890724753559297463989 3828833505445646184137249)
        ·
          refine ⟨2871625129084234638102937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3828833505445646184137249 2871625129084234638102937)
          ·
            refine ⟨2153718846813175978577203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871625129084234638102937 2153718846813175978577203)
            ·
              refine ⟨3230578270219763967865805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153718846813175978577203 3230578270219763967865805)
              ·
                refine ⟨1211466851332411487949677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3230578270219763967865805 1211466851332411487949677)
                ·
                  refine ⟨454300069249654307981129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211466851332411487949677 454300069249654307981129)
                  ·
                    rfl

theorem cell21_1990679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 3].length) (baseStart_1990679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990679 prefixEnd_1990679 := by exact prefixLift 1990679
  have htrace : WordTrace (prefixWord ++ tailWord_1990679) baseStart_1990679 baseEnd_1990679 := by
    simpa [prefixWord, tailWord_1990679, baseEnd_1990679] using wordTrace_append hprefix tailTrace_1990679
  have hstable : (prefixWord ++ tailWord_1990679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990679).length < 2 ^ (prefixWord ++ tailWord_1990679).sum := by decide
  have hdescent : baseEnd_1990679 < baseStart_1990679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990696 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_1990696 : Nat := 118140960795 + 1990696 * 2 ^ 59
def prefixEnd_1990696 : Nat := 4983230072969 + 3 ^ 40 * 1990696 * 2
def baseEnd_1990696 : Nat := 454303948881266056197761

theorem tailTrace_1990696 : CollatzResearch.WordTrace tailWord_1990696 prefixEnd_1990696 454303948881266056197761 := by
  unfold tailWord_1990696
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303323998027925327207971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48404431997370567102943961 36303323998027925327207971)
  ·
    refine ⟨54454985997041887990811957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36303323998027925327207971 54454985997041887990811957)
    ·
      refine ⟨5105154937222676999138621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54454985997041887990811957 5105154937222676999138621)
      ·
        refine ⟨1914433101458503874676983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5105154937222676999138621 1914433101458503874676983)
        ·
          refine ⟨2871649652187755812015475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914433101458503874676983 2871649652187755812015475)
          ·
            refine ⟨4307474478281633718023213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871649652187755812015475 4307474478281633718023213)
            ·
              refine ⟨1615302929355612644258705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4307474478281633718023213 1615302929355612644258705)
              ·
                refine ⟨1211477197016709483194029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615302929355612644258705 1211477197016709483194029)
                ·
                  refine ⟨454303948881266056197761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211477197016709483194029 454303948881266056197761)
                  ·
                    rfl

theorem cell21_1990696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_1990696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990696 prefixEnd_1990696 := by exact prefixLift 1990696
  have htrace : WordTrace (prefixWord ++ tailWord_1990696) baseStart_1990696 baseEnd_1990696 := by
    simpa [prefixWord, tailWord_1990696, baseEnd_1990696] using wordTrace_append hprefix tailTrace_1990696
  have hstable : (prefixWord ++ tailWord_1990696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990696).length < 2 ^ (prefixWord ++ tailWord_1990696).sum := by decide
  have hdescent : baseEnd_1990696 < baseStart_1990696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990704 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_1990704 : Nat := 118140960795 + 1990704 * 2 ^ 59
def prefixEnd_1990704 : Nat := 4983230072969 + 3 ^ 40 * 1990704 * 2
def baseEnd_1990704 : Nat := 454305774590259820064411

theorem tailTrace_1990704 : CollatzResearch.WordTrace tailWord_1990704 prefixEnd_1990704 454305774590259820064411 := by
  unfold tailWord_1990704
  simp only [CollatzResearch.WordTrace]
  refine ⟨36303469890013434010353583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48404626520017912013804777 36303469890013434010353583)
  ·
    refine ⟨54455204835020151015530375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36303469890013434010353583 54455204835020151015530375)
    ·
      refine ⟨81682807252530226523295563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54455204835020151015530375 81682807252530226523295563)
      ·
        refine ⟨122524210878795339784943345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81682807252530226523295563 122524210878795339784943345)
        ·
          refine ⟨91893158159096504838707509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122524210878795339784943345 91893158159096504838707509)
          ·
            refine ⟨8614983577415297328628829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91893158159096504838707509 8614983577415297328628829)
            ·
              refine ⟨3230618841530736498235811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8614983577415297328628829 3230618841530736498235811)
              ·
                refine ⟨4845928262296104747353717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230618841530736498235811 4845928262296104747353717)
                ·
                  refine ⟨454305774590259820064411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4845928262296104747353717 454305774590259820064411)
                  ·
                    rfl

theorem cell21_1990704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_1990704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990704 prefixEnd_1990704 := by exact prefixLift 1990704
  have htrace : WordTrace (prefixWord ++ tailWord_1990704) baseStart_1990704 baseEnd_1990704 := by
    simpa [prefixWord, tailWord_1990704, baseEnd_1990704] using wordTrace_append hprefix tailTrace_1990704
  have hstable : (prefixWord ++ tailWord_1990704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990704).length < 2 ^ (prefixWord ++ tailWord_1990704).sum := by decide
  have hdescent : baseEnd_1990704 < baseStart_1990704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990780 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_1990780 : Nat := 118140960795 + 1990780 * 2 ^ 59
def prefixEnd_1990780 : Nat := 4983230072969 + 3 ^ 40 * 1990780 * 2
def baseEnd_1990780 : Nat := 454323118825700576797589

theorem tailTrace_1990780 : CollatzResearch.WordTrace tailWord_1990780 prefixEnd_1990780 454323118825700576797589 := by
  unfold tailWord_1990780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36304855863875766500236897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48406474485167688666982529 36304855863875766500236897)
  ·
    refine ⟨27228641897906824875177673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36304855863875766500236897 27228641897906824875177673)
    ·
      refine ⟨20421481423430118656383255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27228641897906824875177673 20421481423430118656383255)
      ·
        refine ⟨30632222135145177984574883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20421481423430118656383255 30632222135145177984574883)
        ·
          refine ⟨45948333202717766976862325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30632222135145177984574883 45948333202717766976862325)
          ·
            refine ⟨4307656237754790654080843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45948333202717766976862325 4307656237754790654080843)
            ·
              refine ⟨6461484356632185981121265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307656237754790654080843 6461484356632185981121265)
              ·
                refine ⟨4846113267474139485840949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461484356632185981121265 4846113267474139485840949)
                ·
                  refine ⟨454323118825700576797589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846113267474139485840949 454323118825700576797589)
                  ·
                    rfl

theorem cell21_1990780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_1990780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990780 prefixEnd_1990780 := by exact prefixLift 1990780
  have htrace : WordTrace (prefixWord ++ tailWord_1990780) baseStart_1990780 baseEnd_1990780 := by
    simpa [prefixWord, tailWord_1990780, baseEnd_1990780] using wordTrace_append hprefix tailTrace_1990780
  have hstable : (prefixWord ++ tailWord_1990780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990780).length < 2 ^ (prefixWord ++ tailWord_1990780).sum := by decide
  have hdescent : baseEnd_1990780 < baseStart_1990780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990814 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1990814 : Nat := 118140960795 + 1990814 * 2 ^ 59
def prefixEnd_1990814 : Nat := 4983230072969 + 3 ^ 40 * 1990814 * 2
def baseEnd_1990814 : Nat := 454330878088924073230853

theorem tailTrace_1990814 : CollatzResearch.WordTrace tailWord_1990814 prefixEnd_1990814 454330878088924073230853 := by
  unfold tailWord_1990814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076368976203544600901437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48407301206418904538140997 9076368976203544600901437)
  ·
    refine ⟨3403638366076329225338039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9076368976203544600901437 3403638366076329225338039)
    ·
      refine ⟨5105457549114493838007059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3403638366076329225338039 5105457549114493838007059)
      ·
        refine ⟨7658186323671740757010589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105457549114493838007059 7658186323671740757010589)
        ·
          refine ⟨2871819871376902783878971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7658186323671740757010589 2871819871376902783878971)
          ·
            refine ⟨4307729807065354175818457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871819871376902783878971 4307729807065354175818457)
            ·
              refine ⟨3230797355299015631863843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307729807065354175818457 3230797355299015631863843)
              ·
                refine ⟨4846196032948523447795765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230797355299015631863843 4846196032948523447795765)
                ·
                  refine ⟨454330878088924073230853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4846196032948523447795765 454330878088924073230853)
                  ·
                    rfl

theorem cell21_1990814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1990814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990814 prefixEnd_1990814 := by exact prefixLift 1990814
  have htrace : WordTrace (prefixWord ++ tailWord_1990814) baseStart_1990814 baseEnd_1990814 := by
    simpa [prefixWord, tailWord_1990814, baseEnd_1990814] using wordTrace_append hprefix tailTrace_1990814
  have hstable : (prefixWord ++ tailWord_1990814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990814).length < 2 ^ (prefixWord ++ tailWord_1990814).sum := by decide
  have hdescent : baseEnd_1990814 < baseStart_1990814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1990980 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1990980 : Nat := 118140960795 + 1990980 * 2 ^ 59
def prefixEnd_1990980 : Nat := 4983230072969 + 3 ^ 40 * 1990980 * 2
def baseEnd_1990980 : Nat := 454368761550544673463847

theorem tailTrace_1990980 : CollatzResearch.WordTrace tailWord_1990980 prefixEnd_1990980 454368761550544673463847 := by
  unfold tailWord_1990980
  simp only [CollatzResearch.WordTrace]
  refine ⟨36308503163513483578877197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48411337551351311438502929 36308503163513483578877197)
  ·
    refine ⟨13615688686317556342078949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36308503163513483578877197 13615688686317556342078949)
    ·
      refine ⟨2552941628684541814139803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13615688686317556342078949 2552941628684541814139803)
      ·
        refine ⟨3829412443026812721209705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552941628684541814139803 3829412443026812721209705)
        ·
          refine ⟨2872059332270109540907279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3829412443026812721209705 2872059332270109540907279)
          ·
            refine ⟨4308088998405164311360919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872059332270109540907279 4308088998405164311360919)
            ·
              refine ⟨6462133497607746467041379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308088998405164311360919 6462133497607746467041379)
              ·
                refine ⟨9693200246411619700562069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6462133497607746467041379 9693200246411619700562069)
                ·
                  refine ⟨454368761550544673463847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9693200246411619700562069 454368761550544673463847)
                  ·
                    rfl

theorem cell21_1990980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1990980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1990980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1990980 prefixEnd_1990980 := by exact prefixLift 1990980
  have htrace : WordTrace (prefixWord ++ tailWord_1990980) baseStart_1990980 baseEnd_1990980 := by
    simpa [prefixWord, tailWord_1990980, baseEnd_1990980] using wordTrace_append hprefix tailTrace_1990980
  have hstable : (prefixWord ++ tailWord_1990980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1990980).length < 2 ^ (prefixWord ++ tailWord_1990980).sum := by decide
  have hdescent : baseEnd_1990980 < baseStart_1990980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1990980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991070 : List Nat := [4, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1991070 : Nat := 118140960795 + 1991070 * 2 ^ 59
def prefixEnd_1991070 : Nat := 4983230072969 + 3 ^ 40 * 1991070 * 2
def baseEnd_1991070 : Nat := 151463100258908172321221

theorem tailTrace_1991070 : CollatzResearch.WordTrace tailWord_1991070 prefixEnd_1991070 151463100258908172321221 := by
  unfold tailWord_1991070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077536112087614066066333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48413525931133941685687109 9077536112087614066066333)
  ·
    refine ⟨3404076042032855274774875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9077536112087614066066333 3404076042032855274774875)
    ·
      refine ⟨5106114063049282912162313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404076042032855274774875 5106114063049282912162313)
      ·
        refine ⟨3829585547286962184121735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5106114063049282912162313 3829585547286962184121735)
        ·
          refine ⟨5744378320930443276182603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829585547286962184121735 5744378320930443276182603)
          ·
            refine ⟨8616567481395664914273905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744378320930443276182603 8616567481395664914273905)
            ·
              refine ⟨6462425611046748685705429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8616567481395664914273905 6462425611046748685705429)
              ·
                refine ⟨151463100258908172321221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6462425611046748685705429 151463100258908172321221)
                ·
                  rfl

theorem cell21_1991070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1991070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991070 prefixEnd_1991070 := by exact prefixLift 1991070
  have htrace : WordTrace (prefixWord ++ tailWord_1991070) baseStart_1991070 baseEnd_1991070 := by
    simpa [prefixWord, tailWord_1991070, baseEnd_1991070] using wordTrace_append hprefix tailTrace_1991070
  have hstable : (prefixWord ++ tailWord_1991070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991070).length < 2 ^ (prefixWord ++ tailWord_1991070).sum := by decide
  have hdescent : baseEnd_1991070 < baseStart_1991070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991081 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_1991081 : Nat := 118140960795 + 1991081 * 2 ^ 59
def prefixEnd_1991081 : Nat := 4983230072969 + 3 ^ 40 * 1991081 * 2
def baseEnd_1991081 : Nat := 454391811126590942280307

theorem tailTrace_1991081 : CollatzResearch.WordTrace tailWord_1991081 prefixEnd_1991081 454391811126590942280307 := by
  unfold tailWord_1991081
  simp only [CollatzResearch.WordTrace]
  refine ⟨72620690099661061407181097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48413793399774040938120731 72620690099661061407181097)
  ·
    refine ⟨54465517574745796055385823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72620690099661061407181097 54465517574745796055385823)
    ·
      refine ⟨81698276362118694083078735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54465517574745796055385823 81698276362118694083078735)
      ·
        refine ⟨122547414543178041124618103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81698276362118694083078735 122547414543178041124618103)
        ·
          refine ⟨183821121814767061686927155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122547414543178041124618103 183821121814767061686927155)
          ·
            refine ⟨275731682722150592530390733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183821121814767061686927155 275731682722150592530390733)
            ·
              refine ⟨103399381020806472198896525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275731682722150592530390733 103399381020806472198896525)
              ·
                refine ⟨38774767882802427074586197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103399381020806472198896525 38774767882802427074586197)
                ·
                  refine ⟨454391811126590942280307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38774767882802427074586197 454391811126590942280307)
                  ·
                    rfl

theorem cell21_1991081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_1991081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991081 prefixEnd_1991081 := by exact prefixLift 1991081
  have htrace : WordTrace (prefixWord ++ tailWord_1991081) baseStart_1991081 baseEnd_1991081 := by
    simpa [prefixWord, tailWord_1991081, baseEnd_1991081] using wordTrace_append hprefix tailTrace_1991081
  have hstable : (prefixWord ++ tailWord_1991081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991081).length < 2 ^ (prefixWord ++ tailWord_1991081).sum := by decide
  have hdescent : baseEnd_1991081 < baseStart_1991081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991084 : List Nat := [2, 2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_1991084 : Nat := 118140960795 + 1991084 * 2 ^ 59
def prefixEnd_1991084 : Nat := 4983230072969 + 3 ^ 40 * 1991084 * 2
def baseEnd_1991084 : Nat := 454392495767463603730301

theorem tailTrace_1991084 : CollatzResearch.WordTrace tailWord_1991084 prefixEnd_1991084 454392495767463603730301 := by
  unfold tailWord_1991084
  simp only [CollatzResearch.WordTrace]
  refine ⟨36310399759325096459770153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48413866345766795279693537 36310399759325096459770153)
  ·
    refine ⟨27232799819493822344827615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36310399759325096459770153 27232799819493822344827615)
    ·
      refine ⟨40849199729240733517241423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27232799819493822344827615 40849199729240733517241423)
      ·
        refine ⟨61273799593861100275862135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40849199729240733517241423 61273799593861100275862135)
        ·
          refine ⟨91910699390791650413793203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61273799593861100275862135 91910699390791650413793203)
          ·
            refine ⟨137866049086187475620689805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91910699390791650413793203 137866049086187475620689805)
            ·
              refine ⟨51699768407320303357758677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137866049086187475620689805 51699768407320303357758677)
              ·
                refine ⟨1211713322046569609947469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51699768407320303357758677 1211713322046569609947469)
                ·
                  refine ⟨454392495767463603730301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211713322046569609947469 454392495767463603730301)
                  ·
                    rfl

theorem cell21_1991084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_1991084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991084 prefixEnd_1991084 := by exact prefixLift 1991084
  have htrace : WordTrace (prefixWord ++ tailWord_1991084) baseStart_1991084 baseEnd_1991084 := by
    simpa [prefixWord, tailWord_1991084, baseEnd_1991084] using wordTrace_append hprefix tailTrace_1991084
  have hstable : (prefixWord ++ tailWord_1991084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991084).length < 2 ^ (prefixWord ++ tailWord_1991084).sum := by decide
  have hdescent : baseEnd_1991084 < baseStart_1991084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991101 : List Nat := [1, 4, 1, 2, 2, 3, 1, 4, 3]
def baseStart_1991101 : Nat := 118140960795 + 1991101 * 2 ^ 59
def prefixEnd_1991101 : Nat := 4983230072969 + 3 ^ 40 * 1991101 * 2
def baseEnd_1991101 : Nat := 454396375399075351946933

theorem tailTrace_1991101 : CollatzResearch.WordTrace tailWord_1991101 prefixEnd_1991101 454396375399075351946933 := by
  unfold tailWord_1991101
  simp only [CollatzResearch.WordTrace]
  refine ⟨72621419559588604822909157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48414279706392403215272771 72621419559588604822909157)
  ·
    refine ⟨13616516167422863404295467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72621419559588604822909157 13616516167422863404295467)
    ·
      refine ⟨20424774251134295106443201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13616516167422863404295467 20424774251134295106443201)
      ·
        refine ⟨15318580688350721329832401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20424774251134295106443201 15318580688350721329832401)
        ·
          refine ⟨11488935516263040997374301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15318580688350721329832401 11488935516263040997374301)
          ·
            refine ⟨4308350818598640374015363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11488935516263040997374301 4308350818598640374015363)
            ·
              refine ⟨6462526227897960561023045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4308350818598640374015363 6462526227897960561023045)
              ·
                refine ⟨1211723667730867605191821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6462526227897960561023045 1211723667730867605191821)
                ·
                  refine ⟨454396375399075351946933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211723667730867605191821 454396375399075351946933)
                  ·
                    rfl

theorem cell21_1991101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_1991101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991101 prefixEnd_1991101 := by exact prefixLift 1991101
  have htrace : WordTrace (prefixWord ++ tailWord_1991101) baseStart_1991101 baseEnd_1991101 := by
    simpa [prefixWord, tailWord_1991101, baseEnd_1991101] using wordTrace_append hprefix tailTrace_1991101
  have hstable : (prefixWord ++ tailWord_1991101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991101).length < 2 ^ (prefixWord ++ tailWord_1991101).sum := by decide
  have hdescent : baseEnd_1991101 < baseStart_1991101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991129 : List Nat := [1, 2, 1, 2, 4, 1, 5, 5]
def baseStart_1991129 : Nat := 118140960795 + 1991129 * 2 ^ 59
def prefixEnd_1991129 : Nat := 4983230072969 + 3 ^ 40 * 1991129 * 2
def baseEnd_1991129 : Nat := 151467588460184508493403

theorem tailTrace_1991129 : CollatzResearch.WordTrace tailWord_1991129 prefixEnd_1991129 151467588460184508493403 := by
  unfold tailWord_1991129
  simp only [CollatzResearch.WordTrace]
  refine ⟨72622440803487165604928441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48414960535658110403285627 72622440803487165604928441)
  ·
    refine ⟨54466830602615374203696331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72622440803487165604928441 54466830602615374203696331)
    ·
      refine ⟨81700245903923061305544497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54466830602615374203696331 81700245903923061305544497)
      ·
        refine ⟨61275184427942295979158373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81700245903923061305544497 61275184427942295979158373)
        ·
          refine ⟨11489097080239180496092195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61275184427942295979158373 11489097080239180496092195)
          ·
            refine ⟨17233645620358770744138293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489097080239180496092195 17233645620358770744138293)
            ·
              refine ⟨1615654276908634757262965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17233645620358770744138293 1615654276908634757262965)
              ·
                refine ⟨151467588460184508493403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1615654276908634757262965 151467588460184508493403)
                ·
                  rfl

theorem cell21_1991129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 5].length) (baseStart_1991129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991129 prefixEnd_1991129 := by exact prefixLift 1991129
  have htrace : WordTrace (prefixWord ++ tailWord_1991129) baseStart_1991129 baseEnd_1991129 := by
    simpa [prefixWord, tailWord_1991129, baseEnd_1991129] using wordTrace_append hprefix tailTrace_1991129
  have hstable : (prefixWord ++ tailWord_1991129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991129).length < 2 ^ (prefixWord ++ tailWord_1991129).sum := by decide
  have hdescent : baseEnd_1991129 < baseStart_1991129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991143 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_1991143 : Nat := 118140960795 + 1991143 * 2 ^ 59
def prefixEnd_1991143 : Nat := 4983230072969 + 3 ^ 40 * 1991143 * 2
def baseEnd_1991143 : Nat := 454405960371292612246847

theorem tailTrace_1991143 : CollatzResearch.WordTrace tailWord_1991143 prefixEnd_1991143 454405960371292612246847 := by
  unfold tailWord_1991143
  simp only [CollatzResearch.WordTrace]
  refine ⟨72622951425436445995938083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48415300950290963997292055 72622951425436445995938083)
  ·
    refine ⟨108934427138154668993907125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72622951425436445995938083 108934427138154668993907125)
    ·
      refine ⟨10212602544202000218178793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108934427138154668993907125 10212602544202000218178793)
      ·
        refine ⟨7659451908151500163634095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10212602544202000218178793 7659451908151500163634095)
        ·
          refine ⟨11489177862227250245451143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7659451908151500163634095 11489177862227250245451143)
          ·
            refine ⟨17233766793340875368176715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11489177862227250245451143 17233766793340875368176715)
            ·
              refine ⟨25850650190011313052265073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17233766793340875368176715 25850650190011313052265073)
              ·
                refine ⟨19387987642508484789198805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25850650190011313052265073 19387987642508484789198805)
                ·
                  refine ⟨454405960371292612246847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19387987642508484789198805 454405960371292612246847)
                  ·
                    rfl

theorem cell21_1991143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_1991143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991143 prefixEnd_1991143 := by exact prefixLift 1991143
  have htrace : WordTrace (prefixWord ++ tailWord_1991143) baseStart_1991143 baseEnd_1991143 := by
    simpa [prefixWord, tailWord_1991143, baseEnd_1991143] using wordTrace_append hprefix tailTrace_1991143
  have hstable : (prefixWord ++ tailWord_1991143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991143).length < 2 ^ (prefixWord ++ tailWord_1991143).sum := by decide
  have hdescent : baseEnd_1991143 < baseStart_1991143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991160 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_1991160 : Nat := 118140960795 + 1991160 * 2 ^ 59
def prefixEnd_1991160 : Nat := 4983230072969 + 3 ^ 40 * 1991160 * 2
def baseEnd_1991160 : Nat := 454409840002904360463479

theorem tailTrace_1991160 : CollatzResearch.WordTrace tailWord_1991160 prefixEnd_1991160 454409840002904360463479 := by
  unfold tailWord_1991160
  simp only [CollatzResearch.WordTrace]
  refine ⟨36311785733187428949653467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48415714310916571932871289 36311785733187428949653467)
  ·
    refine ⟨54467678599781143424480201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36311785733187428949653467 54467678599781143424480201)
    ·
      refine ⟨40850758949835857568360151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54467678599781143424480201 40850758949835857568360151)
      ·
        refine ⟨61276138424753786352540227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40850758949835857568360151 61276138424753786352540227)
        ·
          refine ⟨91914207637130679528810341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61276138424753786352540227 91914207637130679528810341)
          ·
            refine ⟨17233913931962002411651939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91914207637130679528810341 17233913931962002411651939)
            ·
              refine ⟨25850870897943003617477909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17233913931962002411651939 25850870897943003617477909)
              ·
                refine ⟨1211759573341078294569277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25850870897943003617477909 1211759573341078294569277)
                ·
                  refine ⟨454409840002904360463479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211759573341078294569277 454409840002904360463479)
                  ·
                    rfl

theorem cell21_1991160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_1991160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991160 prefixEnd_1991160 := by exact prefixLift 1991160
  have htrace : WordTrace (prefixWord ++ tailWord_1991160) baseStart_1991160 baseEnd_1991160 := by
    simpa [prefixWord, tailWord_1991160, baseEnd_1991160] using wordTrace_append hprefix tailTrace_1991160
  have hstable : (prefixWord ++ tailWord_1991160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991160).length < 2 ^ (prefixWord ++ tailWord_1991160).sum := by decide
  have hdescent : baseEnd_1991160 < baseStart_1991160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991222 : List Nat := [5, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1991222 : Nat := 118140960795 + 1991222 * 2 ^ 59
def prefixEnd_1991222 : Nat := 4983230072969 + 3 ^ 40 * 1991222 * 2
def baseEnd_1991222 : Nat := 151474663082535343476673

theorem tailTrace_1991222 : CollatzResearch.WordTrace tailWord_1991222 prefixEnd_1991222 151474663082535343476673 := by
  unfold tailWord_1991222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539114549509390155503995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48417221861433494992042613 4539114549509390155503995)
  ·
    refine ⟨6808671824264085233255993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539114549509390155503995 6808671824264085233255993)
    ·
      refine ⟨5106503868198063924941995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6808671824264085233255993 5106503868198063924941995)
      ·
        refine ⟨7659755802297095887412993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106503868198063924941995 7659755802297095887412993)
        ·
          refine ⟨5744816851722821915559745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7659755802297095887412993 5744816851722821915559745)
          ·
            refine ⟨4308612638792116436669809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5744816851722821915559745 4308612638792116436669809)
            ·
              refine ⟨3231459479094087327502357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4308612638792116436669809 3231459479094087327502357)
              ·
                refine ⟨151474663082535343476673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3231459479094087327502357 151474663082535343476673)
                ·
                  rfl

theorem cell21_1991222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1991222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991222 prefixEnd_1991222 := by exact prefixLift 1991222
  have htrace : WordTrace (prefixWord ++ tailWord_1991222) baseStart_1991222 baseEnd_1991222 := by
    simpa [prefixWord, tailWord_1991222, baseEnd_1991222] using wordTrace_append hprefix tailTrace_1991222
  have hstable : (prefixWord ++ tailWord_1991222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991222).length < 2 ^ (prefixWord ++ tailWord_1991222).sum := by decide
  have hdescent : baseEnd_1991222 < baseStart_1991222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991262 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1991262 : Nat := 118140960795 + 1991262 * 2 ^ 59
def prefixEnd_1991262 : Nat := 4983230072969 + 3 ^ 40 * 1991262 * 2
def baseEnd_1991262 : Nat := 454433117792574849763271

theorem tailTrace_1991262 : CollatzResearch.WordTrace tailWord_1991262 prefixEnd_1991262 454433117792574849763271 := by
  unfold tailWord_1991262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9078411464000666164940005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48418194474670219546346693 9078411464000666164940005)
  ·
    refine ⟨1702202149500124905926251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9078411464000666164940005 1702202149500124905926251)
    ·
      refine ⟨2553303224250187358889377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702202149500124905926251 2553303224250187358889377)
      ·
        refine ⟨1914977418187640519167033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553303224250187358889377 1914977418187640519167033)
        ·
          refine ⟨1436233063640730389375275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914977418187640519167033 1436233063640730389375275)
          ·
            refine ⟨2154349595461095584062913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436233063640730389375275 2154349595461095584062913)
            ·
              refine ⟨1615762196595821688047185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154349595461095584062913 1615762196595821688047185)
              ·
                refine ⟨1211821647446866266035389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615762196595821688047185 1211821647446866266035389)
                ·
                  refine ⟨454433117792574849763271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211821647446866266035389 454433117792574849763271)
                  ·
                    rfl

theorem cell21_1991262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1991262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991262 prefixEnd_1991262 := by exact prefixLift 1991262
  have htrace : WordTrace (prefixWord ++ tailWord_1991262) baseStart_1991262 baseEnd_1991262 := by
    simpa [prefixWord, tailWord_1991262, baseEnd_1991262] using wordTrace_append hprefix tailTrace_1991262
  have hstable : (prefixWord ++ tailWord_1991262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991262).length < 2 ^ (prefixWord ++ tailWord_1991262).sum := by decide
  have hdescent : baseEnd_1991262 < baseStart_1991262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991343 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 4]
def baseStart_1991343 : Nat := 118140960795 + 1991343 * 2 ^ 59
def prefixEnd_1991343 : Nat := 4983230072969 + 3 ^ 40 * 1991343 * 2
def baseEnd_1991343 : Nat := 454451603096136708913105

theorem tailTrace_1991343 : CollatzResearch.WordTrace tailWord_1991343 prefixEnd_1991343 454451603096136708913105 := by
  unfold tailWord_1991343
  simp only [CollatzResearch.WordTrace]
  refine ⟨72630246024711880153218683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48420164016474586768812455 72630246024711880153218683)
  ·
    refine ⟨108945369037067820229828025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72630246024711880153218683 108945369037067820229828025)
    ·
      refine ⟨81709026777800865172371019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108945369037067820229828025 81709026777800865172371019)
      ·
        refine ⟨122563540166701297758556529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81709026777800865172371019 122563540166701297758556529)
        ·
          refine ⟨91922655125025973318917397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122563540166701297758556529 91922655125025973318917397)
          ·
            refine ⟨4308874458985592499324253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91922655125025973318917397 4308874458985592499324253)
            ·
              refine ⟨1615827922119597187246595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4308874458985592499324253 1615827922119597187246595)
              ·
                refine ⟨2423741883179395780869893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615827922119597187246595 2423741883179395780869893)
                ·
                  refine ⟨454451603096136708913105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423741883179395780869893 454451603096136708913105)
                  ·
                    rfl

theorem cell21_1991343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 4].length) (baseStart_1991343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991343 prefixEnd_1991343 := by exact prefixLift 1991343
  have htrace : WordTrace (prefixWord ++ tailWord_1991343) baseStart_1991343 baseEnd_1991343 := by
    simpa [prefixWord, tailWord_1991343, baseEnd_1991343] using wordTrace_append hprefix tailTrace_1991343
  have hstable : (prefixWord ++ tailWord_1991343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991343).length < 2 ^ (prefixWord ++ tailWord_1991343).sum := by decide
  have hdescent : baseEnd_1991343 < baseStart_1991343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991357 : List Nat := [1, 4, 1, 2, 1, 3, 4, 5]
def baseStart_1991357 : Nat := 118140960795 + 1991357 * 2 ^ 59
def prefixEnd_1991357 : Nat := 4983230072969 + 3 ^ 40 * 1991357 * 2
def baseEnd_1991357 : Nat := 151484932695625265226581

theorem tailTrace_1991357 : CollatzResearch.WordTrace tailWord_1991357 prefixEnd_1991357 151484932695625265226581 := by
  unfold tailWord_1991357
  simp only [CollatzResearch.WordTrace]
  refine ⟨72630756646661160544228325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48420504431107440362818883 72630756646661160544228325)
  ·
    refine ⟨13618266871248967602042811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72630756646661160544228325 13618266871248967602042811)
    ·
      refine ⟨20427400306873451403064217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13618266871248967602042811 20427400306873451403064217)
      ·
        refine ⟨15320550230155088552298163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20427400306873451403064217 15320550230155088552298163)
        ·
          refine ⟨22980825345232632828447245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15320550230155088552298163 22980825345232632828447245)
          ·
            refine ⟨8617809504462237310667717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22980825345232632828447245 8617809504462237310667717)
            ·
              refine ⟨1615839282086669495750197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8617809504462237310667717 1615839282086669495750197)
              ·
                refine ⟨151484932695625265226581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1615839282086669495750197 151484932695625265226581)
                ·
                  rfl

theorem cell21_1991357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 5].length) (baseStart_1991357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991357 prefixEnd_1991357 := by exact prefixLift 1991357
  have htrace : WordTrace (prefixWord ++ tailWord_1991357) baseStart_1991357 baseEnd_1991357 := by
    simpa [prefixWord, tailWord_1991357, baseEnd_1991357] using wordTrace_append hprefix tailTrace_1991357
  have hstable : (prefixWord ++ tailWord_1991357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991357).length < 2 ^ (prefixWord ++ tailWord_1991357).sum := by decide
  have hdescent : baseEnd_1991357 < baseStart_1991357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991385 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_1991385 : Nat := 118140960795 + 1991385 * 2 ^ 59
def prefixEnd_1991385 : Nat := 4983230072969 + 3 ^ 40 * 1991385 * 2
def baseEnd_1991385 : Nat := 454461188068353969213019

theorem tailTrace_1991385 : CollatzResearch.WordTrace tailWord_1991385 prefixEnd_1991385 454461188068353969213019 := by
  unfold tailWord_1991385
  simp only [CollatzResearch.WordTrace]
  refine ⟨72631777890559721326247609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48421185260373147550831739 72631777890559721326247609)
  ·
    refine ⟨54473833417919790994685707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72631777890559721326247609 54473833417919790994685707)
    ·
      refine ⟨81710750126879686492028561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54473833417919790994685707 81710750126879686492028561)
      ·
        refine ⟨61283062595159764869021421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81710750126879686492028561 61283062595159764869021421)
        ·
          refine ⟨22981148473184911825883033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61283062595159764869021421 22981148473184911825883033)
          ·
            refine ⟨17235861354888683869412275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22981148473184911825883033 17235861354888683869412275)
            ·
              refine ⟨25853792032333025804118413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17235861354888683869412275 25853792032333025804118413)
              ·
                refine ⟨9695172012124884676544405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25853792032333025804118413 9695172012124884676544405)
                ·
                  refine ⟨454461188068353969213019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9695172012124884676544405 454461188068353969213019)
                  ·
                    rfl

theorem cell21_1991385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_1991385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991385 prefixEnd_1991385 := by exact prefixLift 1991385
  have htrace : WordTrace (prefixWord ++ tailWord_1991385) baseStart_1991385 baseEnd_1991385 := by
    simpa [prefixWord, tailWord_1991385, baseEnd_1991385] using wordTrace_append hprefix tailTrace_1991385
  have hstable : (prefixWord ++ tailWord_1991385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991385).length < 2 ^ (prefixWord ++ tailWord_1991385).sum := by decide
  have hdescent : baseEnd_1991385 < baseStart_1991385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991523 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_1991523 : Nat := 118140960795 + 1991523 * 2 ^ 59
def prefixEnd_1991523 : Nat := 4983230072969 + 3 ^ 40 * 1991523 * 2
def baseEnd_1991523 : Nat := 454492681548496395912737

theorem tailTrace_1991523 : CollatzResearch.WordTrace tailWord_1991523 prefixEnd_1991523 454492681548496395912737 := by
  unfold tailWord_1991523
  simp only [CollatzResearch.WordTrace]
  refine ⟨72636811164059770894771223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48424540776039847263180815 72636811164059770894771223)
  ·
    refine ⟨108955216746089656342156835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72636811164059770894771223 108955216746089656342156835)
    ·
      refine ⟨163432825119134484513235253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108955216746089656342156835 163432825119134484513235253)
      ·
        refine ⟨15321827354918857923115805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163432825119134484513235253 15321827354918857923115805)
        ·
          refine ⟨5745685258094571721168427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15321827354918857923115805 5745685258094571721168427)
          ·
            refine ⟨8618527887141857581752641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745685258094571721168427 8618527887141857581752641)
            ·
              refine ⟨6463895915356393186314481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618527887141857581752641 6463895915356393186314481)
              ·
                refine ⟨4847921936517294889735861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6463895915356393186314481 4847921936517294889735861)
                ·
                  refine ⟨454492681548496395912737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4847921936517294889735861 454492681548496395912737)
                  ·
                    rfl

theorem cell21_1991523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_1991523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991523 prefixEnd_1991523 := by exact prefixLift 1991523
  have htrace : WordTrace (prefixWord ++ tailWord_1991523) baseStart_1991523 baseEnd_1991523 := by
    simpa [prefixWord, tailWord_1991523, baseEnd_1991523] using wordTrace_append hprefix tailTrace_1991523
  have hstable : (prefixWord ++ tailWord_1991523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991523).length < 2 ^ (prefixWord ++ tailWord_1991523).sum := by decide
  have hdescent : baseEnd_1991523 < baseStart_1991523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991537 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_1991537 : Nat := 118140960795 + 1991537 * 2 ^ 59
def prefixEnd_1991537 : Nat := 4983230072969 + 3 ^ 40 * 1991537 * 2
def baseEnd_1991537 : Nat := 454495876539235482679375

theorem tailTrace_1991537 : CollatzResearch.WordTrace tailWord_1991537 prefixEnd_1991537 454495876539235482679375 := by
  unfold tailWord_1991537
  simp only [CollatzResearch.WordTrace]
  refine ⟨72637321786009051285780865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48424881190672700857187243 72637321786009051285780865)
  ·
    refine ⟨54477991339506788464335649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72637321786009051285780865 54477991339506788464335649)
    ·
      refine ⟨40858493504630091348251737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54477991339506788464335649 40858493504630091348251737)
      ·
        refine ⟨30643870128472568511188803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40858493504630091348251737 30643870128472568511188803)
        ·
          refine ⟨45965805192708852766783205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30643870128472568511188803 45965805192708852766783205)
          ·
            refine ⟨8618588473632909893771851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45965805192708852766783205 8618588473632909893771851)
            ·
              refine ⟨12927882710449364840657777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618588473632909893771851 12927882710449364840657777)
              ·
                refine ⟨9695912032837023630493333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12927882710449364840657777 9695912032837023630493333)
                ·
                  refine ⟨454495876539235482679375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9695912032837023630493333 454495876539235482679375)
                  ·
                    rfl

theorem cell21_1991537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_1991537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991537 prefixEnd_1991537 := by exact prefixLift 1991537
  have htrace : WordTrace (prefixWord ++ tailWord_1991537) baseStart_1991537 baseEnd_1991537 := by
    simpa [prefixWord, tailWord_1991537, baseEnd_1991537] using wordTrace_append hprefix tailTrace_1991537
  have hstable : (prefixWord ++ tailWord_1991537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991537).length < 2 ^ (prefixWord ++ tailWord_1991537).sum := by decide
  have hdescent : baseEnd_1991537 < baseStart_1991537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991551 : List Nat := [1, 1, 2, 2, 1, 1, 13]
def baseStart_1991551 : Nat := 118140960795 + 1991551 * 2 ^ 59
def prefixEnd_1991551 : Nat := 4983230072969 + 3 ^ 40 * 1991551 * 2
def baseEnd_1991551 : Nat := 50499896836663841049557

theorem tailTrace_1991551 : CollatzResearch.WordTrace tailWord_1991551 prefixEnd_1991551 50499896836663841049557 := by
  unfold tailWord_1991551
  simp only [CollatzResearch.WordTrace]
  refine ⟨72637832407958331676790507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48425221605305554451193671 72637832407958331676790507)
  ·
    refine ⟨108956748611937497515185761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72637832407958331676790507 108956748611937497515185761)
    ·
      refine ⟨81717561458953123136389321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108956748611937497515185761 81717561458953123136389321)
      ·
        refine ⟨61288171094214842352291991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81717561458953123136389321 61288171094214842352291991)
        ·
          refine ⟨91932256641322263528437987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61288171094214842352291991 91932256641322263528437987)
          ·
            refine ⟨137898384961983395292656981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91932256641322263528437987 137898384961983395292656981)
            ·
              refine ⟨50499896836663841049557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 137898384961983395292656981 50499896836663841049557)
              ·
                rfl

theorem cell21_1991551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 13].length) (baseStart_1991551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991551 prefixEnd_1991551 := by exact prefixLift 1991551
  have htrace : WordTrace (prefixWord ++ tailWord_1991551) baseStart_1991551 baseEnd_1991551 := by
    simpa [prefixWord, tailWord_1991551, baseEnd_1991551] using wordTrace_append hprefix tailTrace_1991551
  have hstable : (prefixWord ++ tailWord_1991551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991551).length < 2 ^ (prefixWord ++ tailWord_1991551).sum := by decide
  have hdescent : baseEnd_1991551 < baseStart_1991551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991557 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 3]
def baseStart_1991557 : Nat := 118140960795 + 1991557 * 2 ^ 59
def prefixEnd_1991557 : Nat := 4983230072969 + 3 ^ 40 * 1991557 * 2
def baseEnd_1991557 : Nat := 454500440811719892346001

theorem tailTrace_1991557 : CollatzResearch.WordTrace tailWord_1991557 prefixEnd_1991557 454500440811719892346001 := by
  unfold tailWord_1991557
  simp only [CollatzResearch.WordTrace]
  refine ⟨72638051245936594701508925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48425367497291063134339283 72638051245936594701508925)
  ·
    refine ⟨27239269217226223013065847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72638051245936594701508925 27239269217226223013065847)
    ·
      refine ⟨40858903825839334519598771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27239269217226223013065847 40858903825839334519598771)
      ·
        refine ⟨61288355738759001779398157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40858903825839334519598771 61288355738759001779398157)
        ·
          refine ⟨22983133402034625667274309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61288355738759001779398157 22983133402034625667274309)
          ·
            refine ⟨4309337512881492312613933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22983133402034625667274309 4309337512881492312613933)
            ·
              refine ⟨1616001567330559617230225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4309337512881492312613933 1616001567330559617230225)
              ·
                refine ⟨1212001175497919712922669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616001567330559617230225 1212001175497919712922669)
                ·
                  refine ⟨454500440811719892346001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212001175497919712922669 454500440811719892346001)
                  ·
                    rfl

theorem cell21_1991557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_1991557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991557 prefixEnd_1991557 := by exact prefixLift 1991557
  have htrace : WordTrace (prefixWord ++ tailWord_1991557) baseStart_1991557 baseEnd_1991557 := by
    simpa [prefixWord, tailWord_1991557, baseEnd_1991557] using wordTrace_append hprefix tailTrace_1991557
  have hstable : (prefixWord ++ tailWord_1991557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991557).length < 2 ^ (prefixWord ++ tailWord_1991557).sum := by decide
  have hdescent : baseEnd_1991557 < baseStart_1991557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991616 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_1991616 : Nat := 118140960795 + 1991616 * 2 ^ 59
def prefixEnd_1991616 : Nat := 4983230072969 + 3 ^ 40 * 1991616 * 2
def baseEnd_1991616 : Nat := 454513905415548900862547

theorem tailTrace_1991616 : CollatzResearch.WordTrace tailWord_1991616 prefixEnd_1991616 454513905415548900862547 := by
  unfold tailWord_1991616
  simp only [CollatzResearch.WordTrace]
  refine ⟨36320101576361423888953351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48426802101815231851937801 36320101576361423888953351)
  ·
    refine ⟨54480152364542135833430027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36320101576361423888953351 54480152364542135833430027)
    ·
      refine ⟨81720228546813203750145041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54480152364542135833430027 81720228546813203750145041)
      ·
        refine ⟨61290171410109902812608781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81720228546813203750145041 61290171410109902812608781)
        ·
          refine ⟨22983814278791213554728293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61290171410109902812608781 22983814278791213554728293)
          ·
            refine ⟨4309465177273352541511555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22983814278791213554728293 4309465177273352541511555)
            ·
              refine ⟨6464197765910028812267333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309465177273352541511555 6464197765910028812267333)
              ·
                refine ⟨1212037081108130402300125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6464197765910028812267333 1212037081108130402300125)
                ·
                  refine ⟨454513905415548900862547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212037081108130402300125 454513905415548900862547)
                  ·
                    rfl

theorem cell21_1991616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_1991616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991616 prefixEnd_1991616 := by exact prefixLift 1991616
  have htrace : WordTrace (prefixWord ++ tailWord_1991616) baseStart_1991616 baseEnd_1991616 := by
    simpa [prefixWord, tailWord_1991616, baseEnd_1991616] using wordTrace_append hprefix tailTrace_1991616
  have hstable : (prefixWord ++ tailWord_1991616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991616).length < 2 ^ (prefixWord ++ tailWord_1991616).sum := by decide
  have hdescent : baseEnd_1991616 < baseStart_1991616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991630 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1991630 : Nat := 118140960795 + 1991630 * 2 ^ 59
def prefixEnd_1991630 : Nat := 4983230072969 + 3 ^ 40 * 1991630 * 2
def baseEnd_1991630 : Nat := 454517100406287987629185

theorem tailTrace_1991630 : CollatzResearch.WordTrace tailWord_1991630 prefixEnd_1991630 454517100406287987629185 := by
  unfold tailWord_1991630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080089221834016021114543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48427142516448085445944229 9080089221834016021114543)
  ·
    refine ⟨13620133832751024031671815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080089221834016021114543 13620133832751024031671815)
    ·
      refine ⟨20430200749126536047507723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13620133832751024031671815 20430200749126536047507723)
      ·
        refine ⟨30645301123689804071261585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20430200749126536047507723 30645301123689804071261585)
        ·
          refine ⟨22983975842767353053446189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30645301123689804071261585 22983975842767353053446189)
          ·
            refine ⟨8618990941037757395042321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22983975842767353053446189 8618990941037757395042321)
            ·
              refine ⟨6464243205778318046281741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8618990941037757395042321 6464243205778318046281741)
              ·
                refine ⟨2424091202166869267355653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6464243205778318046281741 2424091202166869267355653)
                ·
                  refine ⟨454517100406287987629185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2424091202166869267355653 454517100406287987629185)
                  ·
                    rfl

theorem cell21_1991630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1991630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991630 prefixEnd_1991630 := by exact prefixLift 1991630
  have htrace : WordTrace (prefixWord ++ tailWord_1991630) baseStart_1991630 baseEnd_1991630 := by
    simpa [prefixWord, tailWord_1991630, baseEnd_1991630] using wordTrace_append hprefix tailTrace_1991630
  have hstable : (prefixWord ++ tailWord_1991630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991630).length < 2 ^ (prefixWord ++ tailWord_1991630).sum := by decide
  have hdescent : baseEnd_1991630 < baseStart_1991630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991650 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1991650 : Nat := 118140960795 + 1991650 * 2 ^ 59
def prefixEnd_1991650 : Nat := 4983230072969 + 3 ^ 40 * 1991650 * 2
def baseEnd_1991650 : Nat := 454521664678772397295811

theorem tailTrace_1991650 : CollatzResearch.WordTrace tailWord_1991650 prefixEnd_1991650 454521664678772397295811 := by
  unfold tailWord_1991650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18160360808649917896161101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48427628823066447723096269 18160360808649917896161101)
  ·
    refine ⟨6810135303243719211060413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18160360808649917896161101 6810135303243719211060413)
    ·
      refine ⟨2553800738716394704147655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6810135303243719211060413 2553800738716394704147655)
      ·
        refine ⟨3830701108074592056221483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553800738716394704147655 3830701108074592056221483)
        ·
          refine ⟨5746051662111888084332225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830701108074592056221483 5746051662111888084332225)
          ·
            refine ⟨4309538746583916063249169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5746051662111888084332225 4309538746583916063249169)
            ·
              refine ⟨3232154059937937047436877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309538746583916063249169 3232154059937937047436877)
              ·
                refine ⟨1212057772476726392788829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3232154059937937047436877 1212057772476726392788829)
                ·
                  refine ⟨454521664678772397295811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212057772476726392788829 454521664678772397295811)
                  ·
                    rfl

theorem cell21_1991650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1991650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991650 prefixEnd_1991650 := by exact prefixLift 1991650
  have htrace : WordTrace (prefixWord ++ tailWord_1991650) baseStart_1991650 baseEnd_1991650 := by
    simpa [prefixWord, tailWord_1991650, baseEnd_1991650] using wordTrace_append hprefix tailTrace_1991650
  have hstable : (prefixWord ++ tailWord_1991650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991650).length < 2 ^ (prefixWord ++ tailWord_1991650).sum := by decide
  have hdescent : baseEnd_1991650 < baseStart_1991650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991689 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 4]
def baseStart_1991689 : Nat := 118140960795 + 1991689 * 2 ^ 59
def prefixEnd_1991689 : Nat := 4983230072969 + 3 ^ 40 * 1991689 * 2
def baseEnd_1991689 : Nat := 454530565010116996145731

theorem tailTrace_1991689 : CollatzResearch.WordTrace tailWord_1991689 prefixEnd_1991689 454530565010116996145731 := by
  unfold tailWord_1991689
  simp only [CollatzResearch.WordTrace]
  refine ⟨72642865681458381245314121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48428577120972254163542747 72642865681458381245314121)
  ·
    refine ⟨54482149261093785933985591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72642865681458381245314121 54482149261093785933985591)
    ·
      refine ⟨81723223891640678900978387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54482149261093785933985591 81723223891640678900978387)
      ·
        refine ⟨122584835837461018351467581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81723223891640678900978387 122584835837461018351467581)
        ·
          refine ⟨45969313439047881881800343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122584835837461018351467581 45969313439047881881800343)
          ·
            refine ⟨68953970158571822822700515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45969313439047881881800343 68953970158571822822700515)
            ·
              refine ⟨103430955237857734234050773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68953970158571822822700515 103430955237857734234050773)
              ·
                refine ⟨2424163013387290646110565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103430955237857734234050773 2424163013387290646110565)
                ·
                  refine ⟨454530565010116996145731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2424163013387290646110565 454530565010116996145731)
                  ·
                    rfl

theorem cell21_1991689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_1991689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991689 prefixEnd_1991689 := by exact prefixLift 1991689
  have htrace : WordTrace (prefixWord ++ tailWord_1991689) baseStart_1991689 baseEnd_1991689 := by
    simpa [prefixWord, tailWord_1991689, baseEnd_1991689] using wordTrace_append hprefix tailTrace_1991689
  have hstable : (prefixWord ++ tailWord_1991689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991689).length < 2 ^ (prefixWord ++ tailWord_1991689).sum := by decide
  have hdescent : baseEnd_1991689 < baseStart_1991689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991785 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 3]
def baseStart_1991785 : Nat := 118140960795 + 1991785 * 2 ^ 59
def prefixEnd_1991785 : Nat := 4983230072969 + 3 ^ 40 * 1991785 * 2
def baseEnd_1991785 : Nat := 454552473518042162545535

theorem tailTrace_1991785 : CollatzResearch.WordTrace tailWord_1991785 prefixEnd_1991785 454552473518042162545535 := by
  unfold tailWord_1991785
  simp only [CollatzResearch.WordTrace]
  refine ⟨72646367089110589640808809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48430911392740393093872539 72646367089110589640808809)
  ·
    refine ⟨54484775316832942230606607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72646367089110589640808809 54484775316832942230606607)
    ·
      refine ⟨81727162975249413345909911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54484775316832942230606607 81727162975249413345909911)
      ·
        refine ⟨122590744462874120018864867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81727162975249413345909911 122590744462874120018864867)
        ·
          refine ⟨183886116694311180028297301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122590744462874120018864867 183886116694311180028297301)
          ·
            refine ⟨2154915430011459140956609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 183886116694311180028297301 2154915430011459140956609)
            ·
              refine ⟨1616186572508594355717457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2154915430011459140956609 1616186572508594355717457)
              ·
                refine ⟨1212139929381445766788093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616186572508594355717457 1212139929381445766788093)
                ·
                  refine ⟨454552473518042162545535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212139929381445766788093 454552473518042162545535)
                  ·
                    rfl

theorem cell21_1991785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_1991785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991785 prefixEnd_1991785 := by exact prefixLift 1991785
  have htrace : WordTrace (prefixWord ++ tailWord_1991785) baseStart_1991785 baseEnd_1991785 := by
    simpa [prefixWord, tailWord_1991785, baseEnd_1991785] using wordTrace_append hprefix tailTrace_1991785
  have hstable : (prefixWord ++ tailWord_1991785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991785).length < 2 ^ (prefixWord ++ tailWord_1991785).sum := by decide
  have hdescent : baseEnd_1991785 < baseStart_1991785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991813 : List Nat := [1, 3, 1, 1, 6, 1, 3, 5]
def baseStart_1991813 : Nat := 118140960795 + 1991813 * 2 ^ 59
def prefixEnd_1991813 : Nat := 4983230072969 + 3 ^ 40 * 1991813 * 2
def baseEnd_1991813 : Nat := 151519621166506778692937

theorem tailTrace_1991813 : CollatzResearch.WordTrace tailWord_1991813 prefixEnd_1991813 151519621166506778692937 := by
  unfold tailWord_1991813
  simp only [CollatzResearch.WordTrace]
  refine ⟨72647388333009150422828093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48431592222006100281885395 72647388333009150422828093)
  ·
    refine ⟨27242770624878431408560535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72647388333009150422828093 27242770624878431408560535)
    ·
      refine ⟨40864155937317647112840803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27242770624878431408560535 40864155937317647112840803)
      ·
        refine ⟨61296233905976470669261205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40864155937317647112840803 61296233905976470669261205)
        ·
          refine ⟨2873260964342647062621619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61296233905976470669261205 2873260964342647062621619)
          ·
            refine ⟨4309891446513970593932429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873260964342647062621619 4309891446513970593932429)
            ·
              refine ⟨1616209292442738972724661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4309891446513970593932429 1616209292442738972724661)
              ·
                refine ⟨151519621166506778692937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1616209292442738972724661 151519621166506778692937)
                ·
                  rfl

theorem cell21_1991813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 5].length) (baseStart_1991813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991813 prefixEnd_1991813 := by exact prefixLift 1991813
  have htrace : WordTrace (prefixWord ++ tailWord_1991813) baseStart_1991813 baseEnd_1991813 := by
    simpa [prefixWord, tailWord_1991813, baseEnd_1991813] using wordTrace_append hprefix tailTrace_1991813
  have hstable : (prefixWord ++ tailWord_1991813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991813).length < 2 ^ (prefixWord ++ tailWord_1991813).sum := by decide
  have hdescent : baseEnd_1991813 < baseStart_1991813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991827 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 3]
def baseStart_1991827 : Nat := 118140960795 + 1991827 * 2 ^ 59
def prefixEnd_1991827 : Nat := 4983230072969 + 3 ^ 40 * 1991827 * 2
def baseEnd_1991827 : Nat := 454562058490259422845449

theorem tailTrace_1991827 : CollatzResearch.WordTrace tailWord_1991827 prefixEnd_1991827 454562058490259422845449 := by
  unfold tailWord_1991827
  simp only [CollatzResearch.WordTrace]
  refine ⟨72647898954958430813837735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48431932636638953875891823 72647898954958430813837735)
  ·
    refine ⟨108971848432437646220756603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72647898954958430813837735 108971848432437646220756603)
    ·
      refine ⟨163457772648656469331134905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108971848432437646220756603 163457772648656469331134905)
      ·
        refine ⟨122593329486492351998351179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163457772648656469331134905 122593329486492351998351179)
        ·
          refine ⟨183889994229738527997526769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122593329486492351998351179 183889994229738527997526769)
          ·
            refine ⟨137917495672303895998145077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183889994229738527997526769 137917495672303895998145077)
            ·
              refine ⟨12929765219278490249826101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137917495672303895998145077 12929765219278490249826101)
              ·
                refine ⟨1212165489307358460921197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12929765219278490249826101 1212165489307358460921197)
                ·
                  refine ⟨454562058490259422845449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212165489307358460921197 454562058490259422845449)
                  ·
                    rfl

theorem cell21_1991827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 3].length) (baseStart_1991827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991827 prefixEnd_1991827 := by exact prefixLift 1991827
  have htrace : WordTrace (prefixWord ++ tailWord_1991827) baseStart_1991827 baseEnd_1991827 := by
    simpa [prefixWord, tailWord_1991827, baseEnd_1991827] using wordTrace_append hprefix tailTrace_1991827
  have hstable : (prefixWord ++ tailWord_1991827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991827).length < 2 ^ (prefixWord ++ tailWord_1991827).sum := by decide
  have hdescent : baseEnd_1991827 < baseStart_1991827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991841 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_1991841 : Nat := 118140960795 + 1991841 * 2 ^ 59
def prefixEnd_1991841 : Nat := 4983230072969 + 3 ^ 40 * 1991841 * 2
def baseEnd_1991841 : Nat := 454565253480998509612087

theorem tailTrace_1991841 : CollatzResearch.WordTrace tailWord_1991841 prefixEnd_1991841 454565253480998509612087 := by
  unfold tailWord_1991841
  simp only [CollatzResearch.WordTrace]
  refine ⟨72648409576907711204847377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48432273051271807469898251 72648409576907711204847377)
  ·
    refine ⟨54486307182680783403635533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72648409576907711204847377 54486307182680783403635533)
    ·
      refine ⟨20432365193505293776363325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54486307182680783403635533 20432365193505293776363325)
      ·
        refine ⟨7662136947564485166136247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20432365193505293776363325 7662136947564485166136247)
        ·
          refine ⟨11493205421346727749204371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7662136947564485166136247 11493205421346727749204371)
          ·
            refine ⟨17239808132020091623806557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11493205421346727749204371 17239808132020091623806557)
            ·
              refine ⟨6464928049507534358927459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17239808132020091623806557 6464928049507534358927459)
              ·
                refine ⟨9697392074261301538391189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6464928049507534358927459 9697392074261301538391189)
                ·
                  refine ⟨454565253480998509612087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9697392074261301538391189 454565253480998509612087)
                  ·
                    rfl

theorem cell21_1991841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_1991841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991841 prefixEnd_1991841 := by exact prefixLift 1991841
  have htrace : WordTrace (prefixWord ++ tailWord_1991841) baseStart_1991841 baseEnd_1991841 := by
    simpa [prefixWord, tailWord_1991841, baseEnd_1991841] using wordTrace_append hprefix tailTrace_1991841
  have hstable : (prefixWord ++ tailWord_1991841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991841).length < 2 ^ (prefixWord ++ tailWord_1991841).sum := by decide
  have hdescent : baseEnd_1991841 < baseStart_1991841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991844 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_1991844 : Nat := 118140960795 + 1991844 * 2 ^ 59
def prefixEnd_1991844 : Nat := 4983230072969 + 3 ^ 40 * 1991844 * 2
def baseEnd_1991844 : Nat := 454565938121871171062081

theorem tailTrace_1991844 : CollatzResearch.WordTrace tailWord_1991844 prefixEnd_1991844 454565938121871171062081 := by
  unfold tailWord_1991844
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324259497948421358603293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48432345997264561811471057 36324259497948421358603293)
  ·
    refine ⟨13621597311730658009476235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36324259497948421358603293 13621597311730658009476235)
    ·
      refine ⟨20432395967595987014214353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13621597311730658009476235 20432395967595987014214353)
      ·
        refine ⟨15324296975696990260660765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20432395967595987014214353 15324296975696990260660765)
        ·
          refine ⟨5746611365886371347747787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15324296975696990260660765 5746611365886371347747787)
          ·
            refine ⟨8619917048829557021621681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746611365886371347747787 8619917048829557021621681)
            ·
              refine ⟨6464937786622167766216261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8619917048829557021621681 6464937786622167766216261)
              ·
                refine ⟨1212175834991656456165549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6464937786622167766216261 1212175834991656456165549)
                ·
                  refine ⟨454565938121871171062081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212175834991656456165549 454565938121871171062081)
                  ·
                    rfl

theorem cell21_1991844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_1991844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991844 prefixEnd_1991844 := by exact prefixLift 1991844
  have htrace : WordTrace (prefixWord ++ tailWord_1991844) baseStart_1991844 baseEnd_1991844 := by
    simpa [prefixWord, tailWord_1991844, baseEnd_1991844] using wordTrace_append hprefix tailTrace_1991844
  have hstable : (prefixWord ++ tailWord_1991844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991844).length < 2 ^ (prefixWord ++ tailWord_1991844).sum := by decide
  have hdescent : baseEnd_1991844 < baseStart_1991844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991872 : List Nat := [2, 1, 1, 2, 6, 1, 1, 7]
def baseStart_1991872 : Nat := 118140960795 + 1991872 * 2 ^ 59
def prefixEnd_1991872 : Nat := 4983230072969 + 3 ^ 40 * 1991872 * 2
def baseEnd_1991872 : Nat := 151524109367783114865119

theorem tailTrace_1991872 : CollatzResearch.WordTrace tailWord_1991872 prefixEnd_1991872 151524109367783114865119 := by
  unfold tailWord_1991872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36324770119897701749612935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48433026826530268999483913 36324770119897701749612935)
  ·
    refine ⟨54487155179846552624419403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36324770119897701749612935 54487155179846552624419403)
    ·
      refine ⟨81730732769769828936629105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54487155179846552624419403 81730732769769828936629105)
      ·
        refine ⟨61298049577327371702471829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81730732769769828936629105 61298049577327371702471829)
        ·
          refine ⟨2873346073937220548553367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61298049577327371702471829 2873346073937220548553367)
          ·
            refine ⟨4310019110905830822830051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873346073937220548553367 4310019110905830822830051)
            ·
              refine ⟨6465028666358746234245077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310019110905830822830051 6465028666358746234245077)
              ·
                refine ⟨151524109367783114865119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6465028666358746234245077 151524109367783114865119)
                ·
                  rfl

theorem cell21_1991872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_1991872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991872 prefixEnd_1991872 := by exact prefixLift 1991872
  have htrace : WordTrace (prefixWord ++ tailWord_1991872) baseStart_1991872 baseEnd_1991872 := by
    simpa [prefixWord, tailWord_1991872, baseEnd_1991872] using wordTrace_append hprefix tailTrace_1991872
  have hstable : (prefixWord ++ tailWord_1991872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991872).length < 2 ^ (prefixWord ++ tailWord_1991872).sum := by decide
  have hdescent : baseEnd_1991872 < baseStart_1991872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991903 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 3]
def baseStart_1991903 : Nat := 118140960795 + 1991903 * 2 ^ 59
def prefixEnd_1991903 : Nat := 4983230072969 + 3 ^ 40 * 1991903 * 2
def baseEnd_1991903 : Nat := 454579402725700179578627

theorem tailTrace_1991903 : CollatzResearch.WordTrace tailWord_1991903 prefixEnd_1991903 454579402725700179578627 := by
  unfold tailWord_1991903
  simp only [CollatzResearch.WordTrace]
  refine ⟨72650670902683095793604363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48433780601788730529069575 72650670902683095793604363)
  ·
    refine ⟨108976006354024643690406545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72650670902683095793604363 108976006354024643690406545)
    ·
      refine ⟨81732004765518482767804909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108976006354024643690406545 81732004765518482767804909)
      ·
        refine ⟨30649501787069431037926841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81732004765518482767804909 30649501787069431037926841)
        ·
          refine ⟨22987126340302073278445131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30649501787069431037926841 22987126340302073278445131)
          ·
            refine ⟨34480689510453109917667697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22987126340302073278445131 34480689510453109917667697)
            ·
              refine ⟨25860517132839832438250773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34480689510453109917667697 25860517132839832438250773)
              ·
                refine ⟨1212211740601867145543005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25860517132839832438250773 1212211740601867145543005)
                ·
                  refine ⟨454579402725700179578627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212211740601867145543005 454579402725700179578627)
                  ·
                    rfl

theorem cell21_1991903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 3].length) (baseStart_1991903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991903 prefixEnd_1991903 := by exact prefixLift 1991903
  have htrace : WordTrace (prefixWord ++ tailWord_1991903) baseStart_1991903 baseEnd_1991903 := by
    simpa [prefixWord, tailWord_1991903, baseEnd_1991903] using wordTrace_append hprefix tailTrace_1991903
  have hstable : (prefixWord ++ tailWord_1991903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991903).length < 2 ^ (prefixWord ++ tailWord_1991903).sum := by decide
  have hdescent : baseEnd_1991903 < baseStart_1991903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991954 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_1991954 : Nat := 118140960795 + 1991954 * 2 ^ 59
def prefixEnd_1991954 : Nat := 4983230072969 + 3 ^ 40 * 1991954 * 2
def baseEnd_1991954 : Nat := 454591041620535424228523

theorem tailTrace_1991954 : CollatzResearch.WordTrace tailWord_1991954 prefixEnd_1991954 454591041620535424228523 := by
  unfold tailWord_1991954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18163132756374582875927729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48435020683665554335807277 18163132756374582875927729)
  ·
    refine ⟨13622349567280937156945797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18163132756374582875927729 13622349567280937156945797)
    ·
      refine ⟨2554190543865175716927337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13622349567280937156945797 2554190543865175716927337)
      ·
        refine ⟨1915642907898881787695503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2554190543865175716927337 1915642907898881787695503)
        ·
          refine ⟨2873464361848322681543255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915642907898881787695503 2873464361848322681543255)
          ·
            refine ⟨4310196542772484022314883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873464361848322681543255 4310196542772484022314883)
            ·
              refine ⟨6465294814158726033472325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310196542772484022314883 6465294814158726033472325)
              ·
                refine ⟨1212242777654761131276061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6465294814158726033472325 1212242777654761131276061)
                ·
                  refine ⟨454591041620535424228523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212242777654761131276061 454591041620535424228523)
                  ·
                    rfl

theorem cell21_1991954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_1991954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991954 prefixEnd_1991954 := by exact prefixLift 1991954
  have htrace : WordTrace (prefixWord ++ tailWord_1991954) baseStart_1991954 baseEnd_1991954 := by
    simpa [prefixWord, tailWord_1991954, baseEnd_1991954] using wordTrace_append hprefix tailTrace_1991954
  have hstable : (prefixWord ++ tailWord_1991954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991954).length < 2 ^ (prefixWord ++ tailWord_1991954).sum := by decide
  have hdescent : baseEnd_1991954 < baseStart_1991954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991965 : List Nat := [1, 4, 2, 3, 1, 3, 1, 6]
def baseStart_1991965 : Nat := 118140960795 + 1991965 * 2 ^ 59
def prefixEnd_1991965 : Nat := 4983230072969 + 3 ^ 40 * 1991965 * 2
def baseEnd_1991965 : Nat := 151531183990133949848389

theorem tailTrace_1991965 : CollatzResearch.WordTrace tailWord_1991965 prefixEnd_1991965 151531183990133949848389 := by
  unfold tailWord_1991965
  simp only [CollatzResearch.WordTrace]
  refine ⟨72652932228458480382361349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48435288152305653588240899 72652932228458480382361349)
  ·
    refine ⟨13622424792835965071692753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72652932228458480382361349 13622424792835965071692753)
    ·
      refine ⟨10216818594626973803769565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13622424792835965071692753 10216818594626973803769565)
      ·
        refine ⟨3831306972985115176413587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10216818594626973803769565 3831306972985115176413587)
        ·
          refine ⟨5746960459477672764620381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831306972985115176413587 5746960459477672764620381)
          ·
            refine ⟨2155110172304127286732643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5746960459477672764620381 2155110172304127286732643)
            ·
              refine ⟨3232665258456190930098965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155110172304127286732643 3232665258456190930098965)
              ·
                refine ⟨151531183990133949848389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3232665258456190930098965 151531183990133949848389)
                ·
                  rfl

theorem cell21_1991965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 6].length) (baseStart_1991965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991965 prefixEnd_1991965 := by exact prefixLift 1991965
  have htrace : WordTrace (prefixWord ++ tailWord_1991965) baseStart_1991965 baseEnd_1991965 := by
    simpa [prefixWord, tailWord_1991965, baseEnd_1991965] using wordTrace_append hprefix tailTrace_1991965
  have hstable : (prefixWord ++ tailWord_1991965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991965).length < 2 ^ (prefixWord ++ tailWord_1991965).sum := by decide
  have hdescent : baseEnd_1991965 < baseStart_1991965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1991996 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_1991996 : Nat := 118140960795 + 1991996 * 2 ^ 59
def prefixEnd_1991996 : Nat := 4983230072969 + 3 ^ 40 * 1991996 * 2
def baseEnd_1991996 : Nat := 454600626592752684528437

theorem tailTrace_1991996 : CollatzResearch.WordTrace tailWord_1991996 prefixEnd_1991996 454600626592752684528437 := by
  unfold tailWord_1991996
  simp only [CollatzResearch.WordTrace]
  refine ⟨36327031445673086338369921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48436041927564115117826561 36327031445673086338369921)
  ·
    refine ⟨27245273584254814753777441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36327031445673086338369921 27245273584254814753777441)
    ·
      refine ⟨20433955188191111065333081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27245273584254814753777441 20433955188191111065333081)
      ·
        refine ⟨15325466391143333298999811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20433955188191111065333081 15325466391143333298999811)
        ·
          refine ⟨22988199586714999948499717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15325466391143333298999811 22988199586714999948499717)
          ·
            refine ⟨4310287422509062490343697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22988199586714999948499717 4310287422509062490343697)
            ·
              refine ⟨3232715566881796867757773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310287422509062490343697 3232715566881796867757773)
              ·
                refine ⟨1212268337580673825409165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3232715566881796867757773 1212268337580673825409165)
                ·
                  refine ⟨454600626592752684528437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212268337580673825409165 454600626592752684528437)
                  ·
                    rfl

theorem cell21_1991996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_1991996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1991996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1991996 prefixEnd_1991996 := by exact prefixLift 1991996
  have htrace : WordTrace (prefixWord ++ tailWord_1991996) baseStart_1991996 baseEnd_1991996 := by
    simpa [prefixWord, tailWord_1991996, baseEnd_1991996] using wordTrace_append hprefix tailTrace_1991996
  have hstable : (prefixWord ++ tailWord_1991996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1991996).length < 2 ^ (prefixWord ++ tailWord_1991996).sum := by decide
  have hdescent : baseEnd_1991996 < baseStart_1991996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1991996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992007 : List Nat := [1, 1, 4, 1, 2, 4, 8]
def baseStart_1992007 : Nat := 118140960795 + 1992007 * 2 ^ 59
def prefixEnd_1992007 : Nat := 4983230072969 + 3 ^ 40 * 1992007 * 2
def baseEnd_1992007 : Nat := 50511459660291012205009

theorem tailTrace_1992007 : CollatzResearch.WordTrace tailWord_1992007 prefixEnd_1992007 50511459660291012205009 := by
  unfold tailWord_1992007
  simp only [CollatzResearch.WordTrace]
  refine ⟨72654464094306321555390275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48436309396204214370260183 72654464094306321555390275)
  ·
    refine ⟨108981696141459482333085413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72654464094306321555390275 108981696141459482333085413)
    ·
      refine ⟨20434068026523652937453515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108981696141459482333085413 20434068026523652937453515)
      ·
        refine ⟨30651102039785479406180273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20434068026523652937453515 30651102039785479406180273)
        ·
          refine ⟨22988326529839109554635205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30651102039785479406180273 22988326529839109554635205)
          ·
            refine ⟨4310311224344833041494101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22988326529839109554635205 4310311224344833041494101)
            ·
              refine ⟨50511459660291012205009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4310311224344833041494101 50511459660291012205009)
              ·
                rfl

theorem cell21_1992007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 8].length) (baseStart_1992007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992007 prefixEnd_1992007 := by exact prefixLift 1992007
  have htrace : WordTrace (prefixWord ++ tailWord_1992007) baseStart_1992007 baseEnd_1992007 := by
    simpa [prefixWord, tailWord_1992007, baseEnd_1992007] using wordTrace_append hprefix tailTrace_1992007
  have hstable : (prefixWord ++ tailWord_1992007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992007).length < 2 ^ (prefixWord ++ tailWord_1992007).sum := by decide
  have hdescent : baseEnd_1992007 < baseStart_1992007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992013 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1992013 : Nat := 118140960795 + 1992013 * 2 ^ 59
def prefixEnd_1992013 : Nat := 4983230072969 + 3 ^ 40 * 1992013 * 2
def baseEnd_1992013 : Nat := 454604506224364432745069

theorem tailTrace_1992013 : CollatzResearch.WordTrace tailWord_1992013 prefixEnd_1992013 454604506224364432745069 := by
  unfold tailWord_1992013
  simp only [CollatzResearch.WordTrace]
  refine ⟨72654682932284584580108693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48436455288189723053405795 72654682932284584580108693)
  ·
    refine ⟨3405688262450839902192595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72654682932284584580108693 3405688262450839902192595)
    ·
      refine ⟨5108532393676259853288893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405688262450839902192595 5108532393676259853288893)
      ·
        refine ⟨1915699647628597444983335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5108532393676259853288893 1915699647628597444983335)
        ·
          refine ⟨2873549471442896167475003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915699647628597444983335 2873549471442896167475003)
          ·
            refine ⟨4310324207164344251212505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873549471442896167475003 4310324207164344251212505)
            ·
              refine ⟨3232743155373258188409379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310324207164344251212505 3232743155373258188409379)
              ·
                refine ⟨4849114733059887282614069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232743155373258188409379 4849114733059887282614069)
                ·
                  refine ⟨454604506224364432745069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4849114733059887282614069 454604506224364432745069)
                  ·
                    rfl

theorem cell21_1992013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1992013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992013 prefixEnd_1992013 := by exact prefixLift 1992013
  have htrace : WordTrace (prefixWord ++ tailWord_1992013) baseStart_1992013 baseEnd_1992013 := by
    simpa [prefixWord, tailWord_1992013, baseEnd_1992013] using wordTrace_append hprefix tailTrace_1992013
  have hstable : (prefixWord ++ tailWord_1992013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992013).length < 2 ^ (prefixWord ++ tailWord_1992013).sum := by decide
  have hdescent : baseEnd_1992013 < baseStart_1992013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992128 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_1992128 : Nat := 118140960795 + 1992128 * 2 ^ 59
def prefixEnd_1992128 : Nat := 4983230072969 + 3 ^ 40 * 1992128 * 2
def baseEnd_1992128 : Nat := 454630750791149788328167

theorem tailTrace_1992128 : CollatzResearch.WordTrace tailWord_1992128 prefixEnd_1992128 454630750791149788328167 := by
  unfold tailWord_1992128
  simp only [CollatzResearch.WordTrace]
  refine ⟨36329438663433979610272519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48439251551245306147030025 36329438663433979610272519)
  ·
    refine ⟨54494157995150969415408779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36329438663433979610272519 54494157995150969415408779)
    ·
      refine ⟨81741236992726454123113169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54494157995150969415408779 81741236992726454123113169)
      ·
        refine ⟨61305927744544840592334877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81741236992726454123113169 61305927744544840592334877)
        ·
          refine ⟨22989722904204315222125579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61305927744544840592334877 22989722904204315222125579)
          ·
            refine ⟨34484584356306472833188369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22989722904204315222125579 34484584356306472833188369)
            ·
              refine ⟨25863438267229854624891277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34484584356306472833188369 25863438267229854624891277)
              ·
                refine ⟨9698789350211195484334229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25863438267229854624891277 9698789350211195484334229)
                ·
                  refine ⟨454630750791149788328167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9698789350211195484334229 454630750791149788328167)
                  ·
                    rfl

theorem cell21_1992128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_1992128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992128 prefixEnd_1992128 := by exact prefixLift 1992128
  have htrace : WordTrace (prefixWord ++ tailWord_1992128) baseStart_1992128 baseEnd_1992128 := by
    simpa [prefixWord, tailWord_1992128, baseEnd_1992128] using wordTrace_append hprefix tailTrace_1992128
  have hstable : (prefixWord ++ tailWord_1992128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992128).length < 2 ^ (prefixWord ++ tailWord_1992128).sum := by decide
  have hdescent : baseEnd_1992128 < baseStart_1992128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992224 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_1992224 : Nat := 118140960795 + 1992224 * 2 ^ 59
def prefixEnd_1992224 : Nat := 4983230072969 + 3 ^ 40 * 1992224 * 2
def baseEnd_1992224 : Nat := 454652659299074954727971

theorem tailTrace_1992224 : CollatzResearch.WordTrace tailWord_1992224 prefixEnd_1992224 454652659299074954727971 := by
  unfold tailWord_1992224
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331189367260083808019863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48441585823013445077359817 36331189367260083808019863)
  ·
    refine ⟨54496784050890125712029795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36331189367260083808019863 54496784050890125712029795)
    ·
      refine ⟨81745176076335188568044693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54496784050890125712029795 81745176076335188568044693)
      ·
        refine ⟨3831805128578211964127095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81745176076335188568044693 3831805128578211964127095)
        ·
          refine ⟨5747707692867317946190643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831805128578211964127095 5747707692867317946190643)
          ·
            refine ⟨8621561539300976919285965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5747707692867317946190643 8621561539300976919285965)
            ·
              refine ⟨3233085577237866344732237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8621561539300976919285965 3233085577237866344732237)
              ·
                refine ⟨1212407091464199879274589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3233085577237866344732237 1212407091464199879274589)
                ·
                  refine ⟨454652659299074954727971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212407091464199879274589 454652659299074954727971)
                  ·
                    rfl

theorem cell21_1992224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_1992224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992224 prefixEnd_1992224 := by exact prefixLift 1992224
  have htrace : WordTrace (prefixWord ++ tailWord_1992224) baseStart_1992224 baseEnd_1992224 := by
    simpa [prefixWord, tailWord_1992224, baseEnd_1992224] using wordTrace_append hprefix tailTrace_1992224
  have hstable : (prefixWord ++ tailWord_1992224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992224).length < 2 ^ (prefixWord ++ tailWord_1992224).sum := by decide
  have hdescent : baseEnd_1992224 < baseStart_1992224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992252 : List Nat := [2, 2, 2, 2, 4, 1, 2, 6]
def baseStart_1992252 : Nat := 118140960795 + 1992252 * 2 ^ 59
def prefixEnd_1992252 : Nat := 4983230072969 + 3 ^ 40 * 1992252 * 2
def baseEnd_1992252 : Nat := 151553016426851042753749

theorem tailTrace_1992252 : CollatzResearch.WordTrace tailWord_1992252 prefixEnd_1992252 151553016426851042753749 := by
  unfold tailWord_1992252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36331699989209364199029505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48442266652279152265372673 36331699989209364199029505)
  ·
    refine ⟨27248774991907023149272129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36331699989209364199029505 27248774991907023149272129)
    ·
      refine ⟨20436581243930267361954097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27248774991907023149272129 20436581243930267361954097)
      ·
        refine ⟨15327435932947700521465573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20436581243930267361954097 15327435932947700521465573)
        ·
          refine ⟨2873894237427693847774795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15327435932947700521465573 2873894237427693847774795)
          ·
            refine ⟨4310841356141540771662193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873894237427693847774795 4310841356141540771662193)
            ·
              refine ⟨3233131017106155578746645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4310841356141540771662193 3233131017106155578746645)
              ·
                refine ⟨151553016426851042753749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3233131017106155578746645 151553016426851042753749)
                ·
                  rfl

theorem cell21_1992252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_1992252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992252 prefixEnd_1992252 := by exact prefixLift 1992252
  have htrace : WordTrace (prefixWord ++ tailWord_1992252) baseStart_1992252 baseEnd_1992252 := by
    simpa [prefixWord, tailWord_1992252, baseEnd_1992252] using wordTrace_append hprefix tailTrace_1992252
  have hstable : (prefixWord ++ tailWord_1992252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992252).length < 2 ^ (prefixWord ++ tailWord_1992252).sum := by decide
  have hdescent : baseEnd_1992252 < baseStart_1992252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992404 : List Nat := [2, 4, 1, 3, 1, 3, 7]
def baseStart_1992404 : Nat := 118140960795 + 1992404 * 2 ^ 59
def prefixEnd_1992404 : Nat := 4983230072969 + 3 ^ 40 * 1992404 * 2
def baseEnd_1992404 : Nat := 50521526416826071303067

theorem tailTrace_1992404 : CollatzResearch.WordTrace tailWord_1992404 prefixEnd_1992404 50521526416826071303067 := by
  unfold tailWord_1992404
  simp only [CollatzResearch.WordTrace]
  refine ⟨36334471936934029178796133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48445962582578705571728177 36334471936934029178796133)
  ·
    refine ⟨6812713488175130471024275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36334471936934029178796133 6812713488175130471024275)
    ·
      refine ⟨10219070232262695706536413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6812713488175130471024275 10219070232262695706536413)
      ·
        refine ⟨3832151337098510889951155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10219070232262695706536413 3832151337098510889951155)
        ·
          refine ⟨5748227005647766334926733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832151337098510889951155 5748227005647766334926733)
          ·
            refine ⟨2155585127117912375597525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5748227005647766334926733 2155585127117912375597525)
            ·
              refine ⟨50521526416826071303067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2155585127117912375597525 50521526416826071303067)
              ·
                rfl

theorem cell21_1992404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 7].length) (baseStart_1992404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992404 prefixEnd_1992404 := by exact prefixLift 1992404
  have htrace : WordTrace (prefixWord ++ tailWord_1992404) baseStart_1992404 baseEnd_1992404 := by
    simpa [prefixWord, tailWord_1992404, baseEnd_1992404] using wordTrace_append hprefix tailTrace_1992404
  have hstable : (prefixWord ++ tailWord_1992404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992404).length < 2 ^ (prefixWord ++ tailWord_1992404).sum := by decide
  have hdescent : baseEnd_1992404 < baseStart_1992404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992461 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1992461 : Nat := 118140960795 + 1992461 * 2 ^ 59
def prefixEnd_1992461 : Nat := 4983230072969 + 3 ^ 40 * 1992461 * 2
def baseEnd_1992461 : Nat := 454706745928015209277487

theorem tailTrace_1992461 : CollatzResearch.WordTrace tailWord_1992461 prefixEnd_1992461 454706745928015209277487 := by
  unfold tailWord_1992461
  simp only [CollatzResearch.WordTrace]
  refine ⟨72671022834661557092417237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48447348556441038061611491 72671022834661557092417237)
  ·
    refine ⟨1703227097687380244353529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 72671022834661557092417237 1703227097687380244353529)
    ·
      refine ⟨1277420323265535183265147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703227097687380244353529 1277420323265535183265147)
      ·
        refine ⟨1916130484898302774897721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277420323265535183265147 1916130484898302774897721)
        ·
          refine ⟨1437097863673727081173291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916130484898302774897721 1437097863673727081173291)
          ·
            refine ⟨2155646795510590621759937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437097863673727081173291 2155646795510590621759937)
            ·
              refine ⟨1616735096632942966319953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155646795510590621759937 1616735096632942966319953)
              ·
                refine ⟨1212551322474707224739965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616735096632942966319953 1212551322474707224739965)
                ·
                  refine ⟨454706745928015209277487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212551322474707224739965 454706745928015209277487)
                  ·
                    rfl

theorem cell21_1992461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1992461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992461 prefixEnd_1992461 := by exact prefixLift 1992461
  have htrace : WordTrace (prefixWord ++ tailWord_1992461) baseStart_1992461 baseEnd_1992461 := by
    simpa [prefixWord, tailWord_1992461, baseEnd_1992461] using wordTrace_append hprefix tailTrace_1992461
  have hstable : (prefixWord ++ tailWord_1992461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992461).length < 2 ^ (prefixWord ++ tailWord_1992461).sum := by decide
  have hdescent : baseEnd_1992461 < baseStart_1992461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992466 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1992466 : Nat := 118140960795 + 1992466 * 2 ^ 59
def prefixEnd_1992466 : Nat := 4983230072969 + 3 ^ 40 * 1992466 * 2
def baseEnd_1992466 : Nat := 454707886996136311694143

theorem tailTrace_1992466 : CollatzResearch.WordTrace tailWord_1992466 prefixEnd_1992466 454707886996136311694143 := by
  unfold tailWord_1992466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18167801299910860736587313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48447470133095628630899501 18167801299910860736587313)
  ·
    refine ⟨13625850974933145552440485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18167801299910860736587313 13625850974933145552440485)
    ·
      refine ⟨2554847057799964791082591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13625850974933145552440485 2554847057799964791082591)
      ·
        refine ⟨3832270586699947186623887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554847057799964791082591 3832270586699947186623887)
        ·
          refine ⟨5748405880049920779935831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832270586699947186623887 5748405880049920779935831)
          ·
            refine ⟨8622608820074881169903747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748405880049920779935831 8622608820074881169903747)
            ·
              refine ⟨12933913230112321754855621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8622608820074881169903747 12933913230112321754855621)
              ·
                refine ⟨2425108730646060329035429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12933913230112321754855621 2425108730646060329035429)
                ·
                  refine ⟨454707886996136311694143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425108730646060329035429 454707886996136311694143)
                  ·
                    rfl

theorem cell21_1992466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1992466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992466 prefixEnd_1992466 := by exact prefixLift 1992466
  have htrace : WordTrace (prefixWord ++ tailWord_1992466) baseStart_1992466 baseEnd_1992466 := by
    simpa [prefixWord, tailWord_1992466, baseEnd_1992466] using wordTrace_append hprefix tailTrace_1992466
  have hstable : (prefixWord ++ tailWord_1992466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992466).length < 2 ^ (prefixWord ++ tailWord_1992466).sum := by decide
  have hdescent : baseEnd_1992466 < baseStart_1992466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992522 : List Nat := [3, 1, 2, 1, 1, 1, 12]
def baseStart_1992522 : Nat := 118140960795 + 1992522 * 2 ^ 59
def prefixEnd_1992522 : Nat := 4983230072969 + 3 ^ 40 * 1992522 * 2
def baseEnd_1992522 : Nat := 50524518551010295417855

theorem tailTrace_1992522 : CollatzResearch.WordTrace tailWord_1992522 prefixEnd_1992522 50524518551010295417855 := by
  unfold tailWord_1992522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18168311921860141127596955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48448831791627043006925213 18168311921860141127596955)
  ·
    refine ⟨27252467882790211691395433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18168311921860141127596955 27252467882790211691395433)
    ·
      refine ⟨20439350912092658768546575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27252467882790211691395433 20439350912092658768546575)
      ·
        refine ⟨30659026368138988152819863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20439350912092658768546575 30659026368138988152819863)
        ·
          refine ⟨45988539552208482229229795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30659026368138988152819863 45988539552208482229229795)
          ·
            refine ⟨68982809328312723343844693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45988539552208482229229795 68982809328312723343844693)
            ·
              refine ⟨50524518551010295417855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 68982809328312723343844693 50524518551010295417855)
              ·
                rfl

theorem cell21_1992522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 12].length) (baseStart_1992522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992522 prefixEnd_1992522 := by exact prefixLift 1992522
  have htrace : WordTrace (prefixWord ++ tailWord_1992522) baseStart_1992522 baseEnd_1992522 := by
    simpa [prefixWord, tailWord_1992522, baseEnd_1992522] using wordTrace_append hprefix tailTrace_1992522
  have hstable : (prefixWord ++ tailWord_1992522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992522).length < 2 ^ (prefixWord ++ tailWord_1992522).sum := by decide
  have hdescent : baseEnd_1992522 < baseStart_1992522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992556 : List Nat := [2, 2, 1, 1, 4, 4, 2, 5]
def baseStart_1992556 : Nat := 118140960795 + 1992556 * 2 ^ 59
def prefixEnd_1992556 : Nat := 4983230072969 + 3 ^ 40 * 1992556 * 2
def baseEnd_1992556 : Nat := 151576142074105385064653

theorem tailTrace_1992556 : CollatzResearch.WordTrace tailWord_1992556 prefixEnd_1992556 151576142074105385064653 := by
  unfold tailWord_1992556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36337243884658694158562761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48449658512878258878083681 36337243884658694158562761)
  ·
    refine ⟨27252932913494020618922071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36337243884658694158562761 27252932913494020618922071)
    ·
      refine ⟨40879399370241030928383107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27252932913494020618922071 40879399370241030928383107)
      ·
        refine ⟨61319099055361546392574661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40879399370241030928383107 61319099055361546392574661)
        ·
          refine ⟨11497331072880289948607749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61319099055361546392574661 11497331072880289948607749)
          ·
            refine ⟨2155749576165054365363953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11497331072880289948607749 2155749576165054365363953)
            ·
              refine ⟨1616812182123790774022965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155749576165054365363953 1616812182123790774022965)
              ·
                refine ⟨151576142074105385064653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1616812182123790774022965 151576142074105385064653)
                ·
                  rfl

theorem cell21_1992556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_1992556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992556 prefixEnd_1992556 := by exact prefixLift 1992556
  have htrace : WordTrace (prefixWord ++ tailWord_1992556) baseStart_1992556 baseEnd_1992556 := by
    simpa [prefixWord, tailWord_1992556, baseEnd_1992556] using wordTrace_append hprefix tailTrace_1992556
  have hstable : (prefixWord ++ tailWord_1992556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992556).length < 2 ^ (prefixWord ++ tailWord_1992556).sum := by decide
  have hdescent : baseEnd_1992556 < baseStart_1992556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992601 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 4]
def baseStart_1992601 : Nat := 118140960795 + 1992601 * 2 ^ 59
def prefixEnd_1992601 : Nat := 4983230072969 + 3 ^ 40 * 1992601 * 2
def baseEnd_1992601 : Nat := 454738695835406076943867

theorem tailTrace_1992601 : CollatzResearch.WordTrace tailWord_1992601 prefixEnd_1992601 454738695835406076943867 := by
  unfold tailWord_1992601
  simp only [CollatzResearch.WordTrace]
  refine ⟨72676129054154361002513657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48450752702769574001675771 72676129054154361002513657)
  ·
    refine ⟨54507096790615770751885243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72676129054154361002513657 54507096790615770751885243)
    ·
      refine ⟨81760645185923656127827865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54507096790615770751885243 81760645185923656127827865)
      ·
        refine ⟨61320483889442742095870899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81760645185923656127827865 61320483889442742095870899)
        ·
          refine ⟨91980725834164113143806349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61320483889442742095870899 91980725834164113143806349)
          ·
            refine ⟨34492772187811542428927381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91980725834164113143806349 34492772187811542428927381)
            ·
              refine ⟨1616848696303666051355971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34492772187811542428927381 1616848696303666051355971)
              ·
                refine ⟨2425273044455499077033957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616848696303666051355971 2425273044455499077033957)
                ·
                  refine ⟨454738695835406076943867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425273044455499077033957 454738695835406076943867)
                  ·
                    rfl

theorem cell21_1992601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_1992601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992601 prefixEnd_1992601 := by exact prefixLift 1992601
  have htrace : WordTrace (prefixWord ++ tailWord_1992601) baseStart_1992601 baseEnd_1992601 := by
    simpa [prefixWord, tailWord_1992601, baseEnd_1992601] using wordTrace_append hprefix tailTrace_1992601
  have hstable : (prefixWord ++ tailWord_1992601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992601).length < 2 ^ (prefixWord ++ tailWord_1992601).sum := by decide
  have hdescent : baseEnd_1992601 < baseStart_1992601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992615 : List Nat := [1, 1, 6, 1, 2, 1, 2, 7]
def baseStart_1992615 : Nat := 118140960795 + 1992615 * 2 ^ 59
def prefixEnd_1992615 : Nat := 4983230072969 + 3 ^ 40 * 1992615 * 2
def baseEnd_1992615 : Nat := 151580630275381721236835

theorem tailTrace_1992615 : CollatzResearch.WordTrace tailWord_1992615 prefixEnd_1992615 151580630275381721236835 := by
  unfold tailWord_1992615
  simp only [CollatzResearch.WordTrace]
  refine ⟨72676639676103641393523299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48451093117402427595682199 72676639676103641393523299)
  ·
    refine ⟨109014959514155462090284949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72676639676103641393523299 109014959514155462090284949)
    ·
      refine ⟨5110076227226037285482107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109014959514155462090284949 5110076227226037285482107)
      ·
        refine ⟨7665114340839055928223161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110076227226037285482107 7665114340839055928223161)
        ·
          refine ⟨5748835755629291946167371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7665114340839055928223161 5748835755629291946167371)
          ·
            refine ⟨8623253633443937919251057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5748835755629291946167371 8623253633443937919251057)
            ·
              refine ⟨6467440225082953439438293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8623253633443937919251057 6467440225082953439438293)
              ·
                refine ⟨151580630275381721236835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6467440225082953439438293 151580630275381721236835)
                ·
                  rfl

theorem cell21_1992615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_1992615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992615 prefixEnd_1992615 := by exact prefixLift 1992615
  have htrace : WordTrace (prefixWord ++ tailWord_1992615) baseStart_1992615 baseEnd_1992615 := by
    simpa [prefixWord, tailWord_1992615, baseEnd_1992615] using wordTrace_append hprefix tailTrace_1992615
  have hstable : (prefixWord ++ tailWord_1992615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992615).length < 2 ^ (prefixWord ++ tailWord_1992615).sum := by decide
  have hdescent : baseEnd_1992615 < baseStart_1992615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992725 : List Nat := [1, 3, 2, 1, 6, 1, 2, 5]
def baseStart_1992725 : Nat := 118140960795 + 1992725 * 2 ^ 59
def prefixEnd_1992725 : Nat := 4983230072969 + 3 ^ 40 * 1992725 * 2
def baseEnd_1992725 : Nat := 151588998108269805625649

theorem tailTrace_1992725 : CollatzResearch.WordTrace tailWord_1992725 prefixEnd_1992725 151588998108269805625649 := by
  unfold tailWord_1992725
  simp only [CollatzResearch.WordTrace]
  refine ⟨72680651705705130180027629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48453767803803420120018419 72680651705705130180027629)
  ·
    refine ⟨27255244389639423817510361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72680651705705130180027629 27255244389639423817510361)
    ·
      refine ⟨20441433292229567863132771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27255244389639423817510361 20441433292229567863132771)
      ·
        refine ⟨30662149938344351794699157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20441433292229567863132771 30662149938344351794699157)
        ·
          refine ⟨1437288278359891490376523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30662149938344351794699157 1437288278359891490376523)
          ·
            refine ⟨2155932417539837235564785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437288278359891490376523 2155932417539837235564785)
            ·
              refine ⟨1616949313154877926673589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2155932417539837235564785 1616949313154877926673589)
              ·
                refine ⟨151588998108269805625649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1616949313154877926673589 151588998108269805625649)
                ·
                  rfl

theorem cell21_1992725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 5].length) (baseStart_1992725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992725 prefixEnd_1992725 := by exact prefixLift 1992725
  have htrace : WordTrace (prefixWord ++ tailWord_1992725) baseStart_1992725 baseEnd_1992725 := by
    simpa [prefixWord, tailWord_1992725, baseEnd_1992725] using wordTrace_append hprefix tailTrace_1992725
  have hstable : (prefixWord ++ tailWord_1992725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992725).length < 2 ^ (prefixWord ++ tailWord_1992725).sum := by decide
  have hdescent : baseEnd_1992725 < baseStart_1992725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992756 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1992756 : Nat := 118140960795 + 1992756 * 2 ^ 59
def prefixEnd_1992756 : Nat := 4983230072969 + 3 ^ 40 * 1992756 * 2
def baseEnd_1992756 : Nat := 454774068947160251860217

theorem tailTrace_1992756 : CollatzResearch.WordTrace tailWord_1992756 prefixEnd_1992756 454774068947160251860217 := by
  unfold tailWord_1992756
  simp only [CollatzResearch.WordTrace]
  refine ⟨36340891184296411237203061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48454521579061881649604081 36340891184296411237203061)
  ·
    refine ⟨3406958548527788553487787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36340891184296411237203061 3406958548527788553487787)
    ·
      refine ⟨5110437822791682830231681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406958548527788553487787 5110437822791682830231681)
      ·
        refine ⟨3832828367093762122673761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110437822791682830231681 3832828367093762122673761)
        ·
          refine ⟨2874621275320321592005321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3832828367093762122673761 2874621275320321592005321)
          ·
            refine ⟨2155965956490241194003991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874621275320321592005321 2155965956490241194003991)
            ·
              refine ⟨3233948934735361791005987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155965956490241194003991 3233948934735361791005987)
              ·
                refine ⟨4850923402103042686508981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233948934735361791005987 4850923402103042686508981)
                ·
                  refine ⟨454774068947160251860217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4850923402103042686508981 454774068947160251860217)
                  ·
                    rfl

theorem cell21_1992756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1992756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992756 prefixEnd_1992756 := by exact prefixLift 1992756
  have htrace : WordTrace (prefixWord ++ tailWord_1992756) baseStart_1992756 baseEnd_1992756 := by
    simpa [prefixWord, tailWord_1992756, baseEnd_1992756] using wordTrace_append hprefix tailTrace_1992756
  have hstable : (prefixWord ++ tailWord_1992756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992756).length < 2 ^ (prefixWord ++ tailWord_1992756).sum := by decide
  have hdescent : baseEnd_1992756 < baseStart_1992756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992812 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1992812 : Nat := 118140960795 + 1992812 * 2 ^ 59
def prefixEnd_1992812 : Nat := 4983230072969 + 3 ^ 40 * 1992812 * 2
def baseEnd_1992812 : Nat := 454786848910116598926769

theorem tailTrace_1992812 : CollatzResearch.WordTrace tailWord_1992812 prefixEnd_1992812 454786848910116598926769 := by
  unfold tailWord_1992812
  simp only [CollatzResearch.WordTrace]
  refine ⟨36341912428194972019222345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48455883237593296025629793 36341912428194972019222345)
  ·
    refine ⟨27256434321146229014416759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36341912428194972019222345 27256434321146229014416759)
    ·
      refine ⟨40884651481719343521625139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27256434321146229014416759 40884651481719343521625139)
      ·
        refine ⟨61326977222579015282437709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40884651481719343521625139 61326977222579015282437709)
        ·
          refine ⟨22997616458467130730914141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61326977222579015282437709 22997616458467130730914141)
          ·
            refine ⟨8624106171925174024092803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22997616458467130730914141 8624106171925174024092803)
            ·
              refine ⟨12936159257887761036139205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8624106171925174024092803 12936159257887761036139205)
              ·
                refine ⟨2425529860853955194276101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12936159257887761036139205 2425529860853955194276101)
                ·
                  refine ⟨454786848910116598926769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425529860853955194276101 454786848910116598926769)
                  ·
                    rfl

theorem cell21_1992812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1992812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992812 prefixEnd_1992812 := by exact prefixLift 1992812
  have htrace : WordTrace (prefixWord ++ tailWord_1992812) baseStart_1992812 baseEnd_1992812 := by
    simpa [prefixWord, tailWord_1992812, baseEnd_1992812] using wordTrace_append hprefix tailTrace_1992812
  have hstable : (prefixWord ++ tailWord_1992812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992812).length < 2 ^ (prefixWord ++ tailWord_1992812).sum := by decide
  have hdescent : baseEnd_1992812 < baseStart_1992812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992815 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 3]
def baseStart_1992815 : Nat := 118140960795 + 1992815 * 2 ^ 59
def prefixEnd_1992815 : Nat := 4983230072969 + 3 ^ 40 * 1992815 * 2
def baseEnd_1992815 : Nat := 454787533550989260376763

theorem tailTrace_1992815 : CollatzResearch.WordTrace tailWord_1992815 prefixEnd_1992815 454787533550989260376763 := by
  unfold tailWord_1992815
  simp only [CollatzResearch.WordTrace]
  refine ⟨72683934275379075550803899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48455956183586050367202599 72683934275379075550803899)
  ·
    refine ⟨109025901413068613326205849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72683934275379075550803899 109025901413068613326205849)
    ·
      refine ⟨81769426059801459994654387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109025901413068613326205849 81769426059801459994654387)
      ·
        refine ⟨122654139089702189991981581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81769426059801459994654387 122654139089702189991981581)
        ·
          refine ⟨45995302158638321246993093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122654139089702189991981581 45995302158638321246993093)
          ·
            refine ⟨8624119154744685233811205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45995302158638321246993093 8624119154744685233811205)
            ·
              refine ⟨1617022341514628481339601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8624119154744685233811205 1617022341514628481339601)
              ·
                refine ⟨1212766756135971361004701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617022341514628481339601 1212766756135971361004701)
                ·
                  refine ⟨454787533550989260376763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212766756135971361004701 454787533550989260376763)
                  ·
                    rfl

theorem cell21_1992815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 3].length) (baseStart_1992815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992815 prefixEnd_1992815 := by exact prefixLift 1992815
  have htrace : WordTrace (prefixWord ++ tailWord_1992815) baseStart_1992815 baseEnd_1992815 := by
    simpa [prefixWord, tailWord_1992815, baseEnd_1992815] using wordTrace_append hprefix tailTrace_1992815
  have hstable : (prefixWord ++ tailWord_1992815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992815).length < 2 ^ (prefixWord ++ tailWord_1992815).sum := by decide
  have hdescent : baseEnd_1992815 < baseStart_1992815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1992978 : List Nat := [3, 2, 4, 12]
def baseStart_1992978 : Nat := 118140960795 + 1992978 * 2 ^ 59
def prefixEnd_1992978 : Nat := 4983230072969 + 3 ^ 40 * 1992978 * 2
def baseEnd_1992978 : Nat := 1871706717579165428641

theorem tailTrace_1992978 : CollatzResearch.WordTrace tailWord_1992978 prefixEnd_1992978 1871706717579165428641 := by
  unfold tailWord_1992978
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172469843447138597246897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48459919582525702925991725 18172469843447138597246897)
  ·
    refine ⟨13629352382585353947935173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18172469843447138597246897 13629352382585353947935173)
    ·
      refine ⟨2555503571734753865237845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13629352382585353947935173 2555503571734753865237845)
      ·
        refine ⟨1871706717579165428641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2555503571734753865237845 1871706717579165428641)
        ·
          rfl

theorem cell21_1992978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 12].length) (baseStart_1992978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1992978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1992978 prefixEnd_1992978 := by exact prefixLift 1992978
  have htrace : WordTrace (prefixWord ++ tailWord_1992978) baseStart_1992978 baseEnd_1992978 := by
    simpa [prefixWord, tailWord_1992978, baseEnd_1992978] using wordTrace_append hprefix tailTrace_1992978
  have hstable : (prefixWord ++ tailWord_1992978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1992978).length < 2 ^ (prefixWord ++ tailWord_1992978).sum := by decide
  have hdescent : baseEnd_1992978 < baseStart_1992978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1992978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993012 : List Nat := [2, 5, 1, 1, 1, 3, 3, 5]
def baseStart_1993012 : Nat := 118140960795 + 1993012 * 2 ^ 59
def prefixEnd_1993012 : Nat := 4983230072969 + 3 ^ 40 * 1993012 * 2
def baseEnd_1993012 : Nat := 151610830544986898531009

theorem tailTrace_1993012 : CollatzResearch.WordTrace tailWord_1993012 prefixEnd_1993012 151610830544986898531009 := by
  unfold tailWord_1993012
  simp only [CollatzResearch.WordTrace]
  refine ⟨36345559727832689097862645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48460746303776918797150193 36345559727832689097862645)
  ·
    refine ⟨3407396224484314602924623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36345559727832689097862645 3407396224484314602924623)
    ·
      refine ⟨5111094336726471904386935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407396224484314602924623 5111094336726471904386935)
      ·
        refine ⟨7666641505089707856580403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5111094336726471904386935 7666641505089707856580403)
        ·
          refine ⟨11499962257634561784870605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7666641505089707856580403 11499962257634561784870605)
          ·
            refine ⟨4312485846612960669326477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11499962257634561784870605 4312485846612960669326477)
            ·
              refine ⟨1617182192479860250997429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4312485846612960669326477 1617182192479860250997429)
              ·
                refine ⟨151610830544986898531009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1617182192479860250997429 151610830544986898531009)
                ·
                  rfl

theorem cell21_1993012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_1993012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993012 prefixEnd_1993012 := by exact prefixLift 1993012
  have htrace : WordTrace (prefixWord ++ tailWord_1993012) baseStart_1993012 baseEnd_1993012 := by
    simpa [prefixWord, tailWord_1993012, baseEnd_1993012] using wordTrace_append hprefix tailTrace_1993012
  have hstable : (prefixWord ++ tailWord_1993012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993012).length < 2 ^ (prefixWord ++ tailWord_1993012).sum := by decide
  have hdescent : baseEnd_1993012 < baseStart_1993012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993023 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_1993023 : Nat := 118140960795 + 1993023 * 2 ^ 59
def prefixEnd_1993023 : Nat := 4983230072969 + 3 ^ 40 * 1993023 * 2
def baseEnd_1993023 : Nat := 454835001984827120909671

theorem tailTrace_1993023 : CollatzResearch.WordTrace tailWord_1993023 prefixEnd_1993023 454835001984827120909671 := by
  unfold tailWord_1993023
  simp only [CollatzResearch.WordTrace]
  refine ⟨72691520658625527074375723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48461013772417018049583815 72691520658625527074375723)
  ·
    refine ⟨109037280987938290611563585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72691520658625527074375723 109037280987938290611563585)
    ·
      refine ⟨81777960740953717958672689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109037280987938290611563585 81777960740953717958672689)
      ·
        refine ⟨61333470555715288469004517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81777960740953717958672689 61333470555715288469004517)
        ·
          refine ⟨11500025729196616587938347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61333470555715288469004517 11500025729196616587938347)
          ·
            refine ⟨17250038593794924881907521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500025729196616587938347 17250038593794924881907521)
            ·
              refine ⟨12937528945346193661430641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17250038593794924881907521 12937528945346193661430641)
              ·
                refine ⟨9703146709009645246072981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12937528945346193661430641 9703146709009645246072981)
                ·
                  refine ⟨454835001984827120909671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9703146709009645246072981 454835001984827120909671)
                  ·
                    rfl

theorem cell21_1993023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_1993023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993023 prefixEnd_1993023 := by exact prefixLift 1993023
  have htrace : WordTrace (prefixWord ++ tailWord_1993023) baseStart_1993023 baseEnd_1993023 := by
    simpa [prefixWord, tailWord_1993023, baseEnd_1993023] using wordTrace_append hprefix tailTrace_1993023
  have hstable : (prefixWord ++ tailWord_1993023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993023).length < 2 ^ (prefixWord ++ tailWord_1993023).sum := by decide
  have hdescent : baseEnd_1993023 < baseStart_1993023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993040 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_1993040 : Nat := 118140960795 + 1993040 * 2 ^ 59
def prefixEnd_1993040 : Nat := 4983230072969 + 3 ^ 40 * 1993040 * 2
def baseEnd_1993040 : Nat := 454838881616438869126303

theorem tailTrace_1993040 : CollatzResearch.WordTrace tailWord_1993040 prefixEnd_1993040 454838881616438869126303 := by
  unfold tailWord_1993040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36346070349781969488872287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48461427133042625985163049 36346070349781969488872287)
  ·
    refine ⟨54519105524672954233308431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36346070349781969488872287 54519105524672954233308431)
    ·
      refine ⟨81778658287009431349962647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54519105524672954233308431 81778658287009431349962647)
      ·
        refine ⟨122667987430514147024943971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81778658287009431349962647 122667987430514147024943971)
        ·
          refine ⟨184001981145771220537415957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122667987430514147024943971 184001981145771220537415957)
          ·
            refine ⟨8625092866208025962691373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184001981145771220537415957 8625092866208025962691373)
            ·
              refine ⟨3234409824828009736009265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8625092866208025962691373 3234409824828009736009265)
              ·
                refine ⟨2425807368621007302006949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234409824828009736009265 2425807368621007302006949)
                ·
                  refine ⟨454838881616438869126303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2425807368621007302006949 454838881616438869126303)
                  ·
                    rfl

theorem cell21_1993040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_1993040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993040 prefixEnd_1993040 := by exact prefixLift 1993040
  have htrace : WordTrace (prefixWord ++ tailWord_1993040) baseStart_1993040 baseEnd_1993040 := by
    simpa [prefixWord, tailWord_1993040, baseEnd_1993040] using wordTrace_append hprefix tailTrace_1993040
  have hstable : (prefixWord ++ tailWord_1993040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993040).length < 2 ^ (prefixWord ++ tailWord_1993040).sum := by decide
  have hdescent : baseEnd_1993040 < baseStart_1993040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993099 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_1993099 : Nat := 118140960795 + 1993099 * 2 ^ 59
def prefixEnd_1993099 : Nat := 4983230072969 + 3 ^ 40 * 1993099 * 2
def baseEnd_1993099 : Nat := 454852346220267877642849

theorem tailTrace_1993099 : CollatzResearch.WordTrace tailWord_1993099 prefixEnd_1993099 454852346220267877642849 := by
  unfold tailWord_1993099
  simp only [CollatzResearch.WordTrace]
  refine ⟨72694292606350192054142351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48462861737566794702761567 72694292606350192054142351)
  ·
    refine ⟨109041438909525288081213527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72694292606350192054142351 109041438909525288081213527)
    ·
      refine ⟨163562158364287932121820291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109041438909525288081213527 163562158364287932121820291)
      ·
        refine ⟨245343237546431898182730437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163562158364287932121820291 245343237546431898182730437)
        ·
          refine ⟨46001857039955980909261957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245343237546431898182730437 46001857039955980909261957)
          ·
            refine ⟨8625348194991746420486617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46001857039955980909261957 8625348194991746420486617)
            ·
              refine ⟨6469011146243809815364963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8625348194991746420486617 6469011146243809815364963)
              ·
                refine ⟨9703516719365714723047445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469011146243809815364963 9703516719365714723047445)
                ·
                  refine ⟨454852346220267877642849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9703516719365714723047445 454852346220267877642849)
                  ·
                    rfl

theorem cell21_1993099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_1993099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993099 prefixEnd_1993099 := by exact prefixLift 1993099
  have htrace : WordTrace (prefixWord ++ tailWord_1993099) baseStart_1993099 baseEnd_1993099 := by
    simpa [prefixWord, tailWord_1993099, baseEnd_1993099] using wordTrace_append hprefix tailTrace_1993099
  have hstable : (prefixWord ++ tailWord_1993099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993099).length < 2 ^ (prefixWord ++ tailWord_1993099).sum := by decide
  have hdescent : baseEnd_1993099 < baseStart_1993099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993102 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1993102 : Nat := 118140960795 + 1993102 * 2 ^ 59
def prefixEnd_1993102 : Nat := 4983230072969 + 3 ^ 40 * 1993102 * 2
def baseEnd_1993102 : Nat := 454853030861140539092843

theorem tailTrace_1993102 : CollatzResearch.WordTrace tailWord_1993102 prefixEnd_1993102 454853030861140539092843 := by
  unfold tailWord_1993102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086800253167415445812695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48462934683559549044334373 9086800253167415445812695)
  ·
    refine ⟨13630200379751123168719043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9086800253167415445812695 13630200379751123168719043)
    ·
      refine ⟨20445300569626684753078565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13630200379751123168719043 20445300569626684753078565)
      ·
        refine ⟨3833493856805003391202231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20445300569626684753078565 3833493856805003391202231)
        ·
          refine ⟨5750240785207505086803347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833493856805003391202231 5750240785207505086803347)
          ·
            refine ⟨8625361177811257630205021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750240785207505086803347 8625361177811257630205021)
            ·
              refine ⟨3234510441679221611326883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8625361177811257630205021 3234510441679221611326883)
              ·
                refine ⟨4851765662518832416990325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234510441679221611326883 4851765662518832416990325)
                ·
                  refine ⟨454853030861140539092843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4851765662518832416990325 454853030861140539092843)
                  ·
                    rfl

theorem cell21_1993102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1993102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993102 prefixEnd_1993102 := by exact prefixLift 1993102
  have htrace : WordTrace (prefixWord ++ tailWord_1993102) baseStart_1993102 baseEnd_1993102 := by
    simpa [prefixWord, tailWord_1993102, baseEnd_1993102] using wordTrace_append hprefix tailTrace_1993102
  have hstable : (prefixWord ++ tailWord_1993102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993102).length < 2 ^ (prefixWord ++ tailWord_1993102).sum := by decide
  have hdescent : baseEnd_1993102 < baseStart_1993102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993153 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 3]
def baseStart_1993153 : Nat := 118140960795 + 1993153 * 2 ^ 59
def prefixEnd_1993153 : Nat := 4983230072969 + 3 ^ 40 * 1993153 * 2
def baseEnd_1993153 : Nat := 454864669755975783742739

theorem tailTrace_1993153 : CollatzResearch.WordTrace tailWord_1993153 prefixEnd_1993153 454864669755975783742739 := by
  unfold tailWord_1993153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72696262148154559276608113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48464174765436372851072075 72696262148154559276608113)
  ·
    refine ⟨54522196611115919457456085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72696262148154559276608113 54522196611115919457456085)
    ·
      refine ⟨1277863983073029362284127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54522196611115919457456085 1277863983073029362284127)
      ·
        refine ⟨1916795974609544043426191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277863983073029362284127 1916795974609544043426191)
        ·
          refine ⟨2875193961914316065139287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916795974609544043426191 2875193961914316065139287)
          ·
            refine ⟨4312790942871474097708931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875193961914316065139287 4312790942871474097708931)
            ·
              refine ⟨6469186414307211146563397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312790942871474097708931 6469186414307211146563397)
              ·
                refine ⟨1212972452682602089980637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6469186414307211146563397 1212972452682602089980637)
                ·
                  refine ⟨454864669755975783742739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212972452682602089980637 454864669755975783742739)
                  ·
                    rfl

theorem cell21_1993153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_1993153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993153 prefixEnd_1993153 := by exact prefixLift 1993153
  have htrace : WordTrace (prefixWord ++ tailWord_1993153) baseStart_1993153 baseEnd_1993153 := by
    simpa [prefixWord, tailWord_1993153, baseEnd_1993153] using wordTrace_append hprefix tailTrace_1993153
  have hstable : (prefixWord ++ tailWord_1993153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993153).length < 2 ^ (prefixWord ++ tailWord_1993153).sum := by decide
  have hdescent : baseEnd_1993153 < baseStart_1993153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993164 : List Nat := [2, 2, 1, 4, 4, 1, 1, 6]
def baseStart_1993164 : Nat := 118140960795 + 1993164 * 2 ^ 59
def prefixEnd_1993164 : Nat := 4983230072969 + 3 ^ 40 * 1993164 * 2
def baseEnd_1993164 : Nat := 151622393368614069686461

theorem tailTrace_1993164 : CollatzResearch.WordTrace tailWord_1993164 prefixEnd_1993164 151622393368614069686461 := by
  unfold tailWord_1993164
  simp only [CollatzResearch.WordTrace]
  refine ⟨36348331675557354077629273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48464442234076472103505697 36348331675557354077629273)
  ·
    refine ⟨27261248756668015558221955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36348331675557354077629273 27261248756668015558221955)
    ·
      refine ⟨40891873135002023337332933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27261248756668015558221955 40891873135002023337332933)
      ·
        refine ⟨7667226212812879375749925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40891873135002023337332933 7667226212812879375749925)
        ·
          refine ⟨1437604914902414882953111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7667226212812879375749925 1437604914902414882953111)
          ·
            refine ⟨2156407372353622324429667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437604914902414882953111 2156407372353622324429667)
            ·
              refine ⟨3234611058530433486644501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156407372353622324429667 3234611058530433486644501)
              ·
                refine ⟨151622393368614069686461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3234611058530433486644501 151622393368614069686461)
                ·
                  rfl

theorem cell21_1993164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_1993164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993164 prefixEnd_1993164 := by exact prefixLift 1993164
  have htrace : WordTrace (prefixWord ++ tailWord_1993164) baseStart_1993164 baseEnd_1993164 := by
    simpa [prefixWord, tailWord_1993164, baseEnd_1993164] using wordTrace_append hprefix tailTrace_1993164
  have hstable : (prefixWord ++ tailWord_1993164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993164).length < 2 ^ (prefixWord ++ tailWord_1993164).sum := by decide
  have hdescent : baseEnd_1993164 < baseStart_1993164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993206 : List Nat := [5, 1, 1, 1, 2, 1, 10]
def baseStart_1993206 : Nat := 118140960795 + 1993206 * 2 ^ 59
def prefixEnd_1993206 : Nat := 4983230072969 + 3 ^ 40 * 1993206 * 2
def baseEnd_1993206 : Nat := 50541862786451052151033

theorem tailTrace_1993206 : CollatzResearch.WordTrace tailWord_1993206 prefixEnd_1993206 50541862786451052151033 := by
  unfold tailWord_1993206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4543637201060159333017967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48465463477975032885524981 4543637201060159333017967)
  ·
    refine ⟨6815455801590238999526951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4543637201060159333017967 6815455801590238999526951)
    ·
      refine ⟨10223183702385358499290427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6815455801590238999526951 10223183702385358499290427)
      ·
        refine ⟨15334775553578037748935641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10223183702385358499290427 15334775553578037748935641)
        ·
          refine ⟨11501081665183528311701731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15334775553578037748935641 11501081665183528311701731)
          ·
            refine ⟨17251622497775292467552597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501081665183528311701731 17251622497775292467552597)
            ·
              refine ⟨50541862786451052151033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17251622497775292467552597 50541862786451052151033)
              ·
                rfl

theorem cell21_1993206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 10].length) (baseStart_1993206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993206 prefixEnd_1993206 := by exact prefixLift 1993206
  have htrace : WordTrace (prefixWord ++ tailWord_1993206) baseStart_1993206 baseEnd_1993206 := by
    simpa [prefixWord, tailWord_1993206, baseEnd_1993206] using wordTrace_append hprefix tailTrace_1993206
  have hstable : (prefixWord ++ tailWord_1993206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993206).length < 2 ^ (prefixWord ++ tailWord_1993206).sum := by decide
  have hdescent : baseEnd_1993206 < baseStart_1993206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993251 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_1993251 : Nat := 118140960795 + 1993251 * 2 ^ 59
def prefixEnd_1993251 : Nat := 4983230072969 + 3 ^ 40 * 1993251 * 2
def baseEnd_1993251 : Nat := 454887034691149391109205

theorem tailTrace_1993251 : CollatzResearch.WordTrace tailWord_1993251 prefixEnd_1993251 454887034691149391109205 := by
  unfold tailWord_1993251
  simp only [CollatzResearch.WordTrace]
  refine ⟨72699836501799522013675607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48466557667866348009117071 72699836501799522013675607)
  ·
    refine ⟨109049754752699283020513411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72699836501799522013675607 109049754752699283020513411)
    ·
      refine ⟨163574632129048924530770117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109049754752699283020513411 163574632129048924530770117)
      ·
        refine ⟨30670243524196673349519397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163574632129048924530770117 30670243524196673349519397)
        ·
          refine ⟨5750670660786876253034887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30670243524196673349519397 5750670660786876253034887)
          ·
            refine ⟨8626005991180314379552331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5750670660786876253034887 8626005991180314379552331)
            ·
              refine ⟨12939008986770471569328497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8626005991180314379552331 12939008986770471569328497)
              ·
                refine ⟨9704256740077853676996373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12939008986770471569328497 9704256740077853676996373)
                ·
                  refine ⟨454887034691149391109205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9704256740077853676996373 454887034691149391109205)
                  ·
                    rfl

theorem cell21_1993251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_1993251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993251 prefixEnd_1993251 := by exact prefixLift 1993251
  have htrace : WordTrace (prefixWord ++ tailWord_1993251) baseStart_1993251 baseEnd_1993251 := by
    simpa [prefixWord, tailWord_1993251, baseEnd_1993251] using wordTrace_append hprefix tailTrace_1993251
  have hstable : (prefixWord ++ tailWord_1993251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993251).length < 2 ^ (prefixWord ++ tailWord_1993251).sum := by decide
  have hdescent : baseEnd_1993251 < baseStart_1993251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993265 : List Nat := [1, 2, 2, 3, 1, 1, 11]
def baseStart_1993265 : Nat := 118140960795 + 1993265 * 2 ^ 59
def prefixEnd_1993265 : Nat := 4983230072969 + 3 ^ 40 * 1993265 * 2
def baseEnd_1993265 : Nat := 50543358853543164208427

theorem tailTrace_1993265 : CollatzResearch.WordTrace tailWord_1993265 prefixEnd_1993265 50543358853543164208427 := by
  unfold tailWord_1993265
  simp only [CollatzResearch.WordTrace]
  refine ⟨72700347123748802404685249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48466898082499201603123499 72700347123748802404685249)
  ·
    refine ⟨54525260342811601803513937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72700347123748802404685249 54525260342811601803513937)
    ·
      refine ⟨40893945257108701352635453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54525260342811601803513937 40893945257108701352635453)
      ·
        refine ⟨15335229471415763007238295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40893945257108701352635453 15335229471415763007238295)
        ·
          refine ⟨23002844207123644510857443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15335229471415763007238295 23002844207123644510857443)
          ·
            refine ⟨34504266310685466766286165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23002844207123644510857443 34504266310685466766286165)
            ·
              refine ⟨50543358853543164208427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34504266310685466766286165 50543358853543164208427)
              ·
                rfl

theorem cell21_1993265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 11].length) (baseStart_1993265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993265 prefixEnd_1993265 := by exact prefixLift 1993265
  have htrace : WordTrace (prefixWord ++ tailWord_1993265) baseStart_1993265 baseEnd_1993265 := by
    simpa [prefixWord, tailWord_1993265, baseEnd_1993265] using wordTrace_append hprefix tailTrace_1993265
  have hstable : (prefixWord ++ tailWord_1993265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993265).length < 2 ^ (prefixWord ++ tailWord_1993265).sum := by decide
  have hdescent : baseEnd_1993265 < baseStart_1993265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993285 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 4]
def baseStart_1993285 : Nat := 118140960795 + 1993285 * 2 ^ 59
def prefixEnd_1993285 : Nat := 4983230072969 + 3 ^ 40 * 1993285 * 2
def baseEnd_1993285 : Nat := 454894793954372887542469

theorem tailTrace_1993285 : CollatzResearch.WordTrace tailWord_1993285 prefixEnd_1993285 454894793954372887542469 := by
  unfold tailWord_1993285
  simp only [CollatzResearch.WordTrace]
  refine ⟨72701076583676345820413309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48467384389117563880275539 72701076583676345820413309)
  ·
    refine ⟨27262903718878629682654991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72701076583676345820413309 27262903718878629682654991)
    ·
      refine ⟨40894355578317944523982487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27262903718878629682654991 40894355578317944523982487)
      ·
        refine ⟨61341533367476916785973731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40894355578317944523982487 61341533367476916785973731)
        ·
          refine ⟨92012300051215375178960597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61341533367476916785973731 92012300051215375178960597)
          ·
            refine ⟨2156538282450360355756889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 92012300051215375178960597 2156538282450360355756889)
            ·
              refine ⟨1617403711837770266817667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156538282450360355756889 1617403711837770266817667)
              ·
                refine ⟨2426105567756655400226501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617403711837770266817667 2426105567756655400226501)
                ·
                  refine ⟨454894793954372887542469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2426105567756655400226501 454894793954372887542469)
                  ·
                    rfl

theorem cell21_1993285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_1993285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993285 prefixEnd_1993285 := by exact prefixLift 1993285
  have htrace : WordTrace (prefixWord ++ tailWord_1993285) baseStart_1993285 baseEnd_1993285 := by
    simpa [prefixWord, tailWord_1993285, baseEnd_1993285] using wordTrace_append hprefix tailTrace_1993285
  have hstable : (prefixWord ++ tailWord_1993285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993285).length < 2 ^ (prefixWord ++ tailWord_1993285).sum := by decide
  have hdescent : baseEnd_1993285 < baseStart_1993285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993327 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 4]
def baseStart_1993327 : Nat := 118140960795 + 1993327 * 2 ^ 59
def prefixEnd_1993327 : Nat := 4983230072969 + 3 ^ 40 * 1993327 * 2
def baseEnd_1993327 : Nat := 454904378926590147842383

theorem tailTrace_1993327 : CollatzResearch.WordTrace tailWord_1993327 prefixEnd_1993327 454904378926590147842383 := by
  unfold tailWord_1993327
  simp only [CollatzResearch.WordTrace]
  refine ⟨72702608449524186993442235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48468405633016124662294823 72702608449524186993442235)
  ·
    refine ⟨109053912674286280490163353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72702608449524186993442235 109053912674286280490163353)
    ·
      refine ⟨81790434505714710367622515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109053912674286280490163353 81790434505714710367622515)
      ·
        refine ⟨122685651758572065551433773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81790434505714710367622515 122685651758572065551433773)
        ·
          refine ⟨46007119409464524581787665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122685651758572065551433773 46007119409464524581787665)
          ·
            refine ⟨34505339557098393436340749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46007119409464524581787665 34505339557098393436340749)
            ·
              refine ⟨12939502333911897538627781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34505339557098393436340749 12939502333911897538627781)
              ·
                refine ⟨2426156687608480788492709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12939502333911897538627781 2426156687608480788492709)
                ·
                  refine ⟨454904378926590147842383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2426156687608480788492709 454904378926590147842383)
                  ·
                    rfl

theorem cell21_1993327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 4].length) (baseStart_1993327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993327 prefixEnd_1993327 := by exact prefixLift 1993327
  have htrace : WordTrace (prefixWord ++ tailWord_1993327) baseStart_1993327 baseEnd_1993327 := by
    simpa [prefixWord, tailWord_1993327, baseEnd_1993327] using wordTrace_append hprefix tailTrace_1993327
  have hstable : (prefixWord ++ tailWord_1993327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993327).length < 2 ^ (prefixWord ++ tailWord_1993327).sum := by decide
  have hdescent : baseEnd_1993327 < baseStart_1993327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993389 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_1993389 : Nat := 118140960795 + 1993389 * 2 ^ 59
def prefixEnd_1993389 : Nat := 4983230072969 + 3 ^ 40 * 1993389 * 2
def baseEnd_1993389 : Nat := 454918528171291817808923

theorem tailTrace_1993389 : CollatzResearch.WordTrace tailWord_1993389 prefixEnd_1993389 454918528171291817808923 := by
  unfold tailWord_1993389
  simp only [CollatzResearch.WordTrace]
  refine ⟨72704869775299571582199221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48469913183533047721466147 72704869775299571582199221)
  ·
    refine ⟨6816081541434334835831177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72704869775299571582199221 6816081541434334835831177)
    ·
      refine ⟨5112061156075751126873383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6816081541434334835831177 5112061156075751126873383)
      ·
        refine ⟨7668091734113626690310075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112061156075751126873383 7668091734113626690310075)
        ·
          refine ⟨11502137601170440035465113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7668091734113626690310075 11502137601170440035465113)
          ·
            refine ⟨8626603200877830026598835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11502137601170440035465113 8626603200877830026598835)
            ·
              refine ⟨12939904801316745039898253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8626603200877830026598835 12939904801316745039898253)
              ·
                refine ⟨4852464300493779389961845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12939904801316745039898253 4852464300493779389961845)
                ·
                  refine ⟨454918528171291817808923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4852464300493779389961845 454918528171291817808923)
                  ·
                    rfl

theorem cell21_1993389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_1993389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993389 prefixEnd_1993389 := by exact prefixLift 1993389
  have htrace : WordTrace (prefixWord ++ tailWord_1993389) baseStart_1993389 baseEnd_1993389 := by
    simpa [prefixWord, tailWord_1993389, baseEnd_1993389] using wordTrace_append hprefix tailTrace_1993389
  have hstable : (prefixWord ++ tailWord_1993389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993389).length < 2 ^ (prefixWord ++ tailWord_1993389).sum := by decide
  have hdescent : baseEnd_1993389 < baseStart_1993389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993409 : List Nat := [1, 2, 6, 2, 1, 2, 2, 5]
def baseStart_1993409 : Nat := 118140960795 + 1993409 * 2 ^ 59
def prefixEnd_1993409 : Nat := 4983230072969 + 3 ^ 40 * 1993409 * 2
def baseEnd_1993409 : Nat := 151641030814592075825183

theorem tailTrace_1993409 : CollatzResearch.WordTrace tailWord_1993409 prefixEnd_1993409 151641030814592075825183 := by
  unfold tailWord_1993409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72705599235227114997927281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48470399490151409998618187 72705599235227114997927281)
  ·
    refine ⟨54529199426420336248445461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72705599235227114997927281 54529199426420336248445461)
    ·
      refine ⟨2556056223113453261645881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54529199426420336248445461 2556056223113453261645881)
      ·
        refine ⟨1917042167335089946234411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2556056223113453261645881 1917042167335089946234411)
        ·
          refine ⟨2875563251002634919351617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917042167335089946234411 2875563251002634919351617)
          ·
            refine ⟨2156672438251976189513713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2875563251002634919351617 2156672438251976189513713)
            ·
              refine ⟨1617504328688982142135285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156672438251976189513713 1617504328688982142135285)
              ·
                refine ⟨151641030814592075825183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1617504328688982142135285 151641030814592075825183)
                ·
                  rfl

theorem cell21_1993409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 5].length) (baseStart_1993409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993409 prefixEnd_1993409 := by exact prefixLift 1993409
  have htrace : WordTrace (prefixWord ++ tailWord_1993409) baseStart_1993409 baseEnd_1993409 := by
    simpa [prefixWord, tailWord_1993409, baseEnd_1993409] using wordTrace_append hprefix tailTrace_1993409
  have hstable : (prefixWord ++ tailWord_1993409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993409).length < 2 ^ (prefixWord ++ tailWord_1993409).sum := by decide
  have hdescent : baseEnd_1993409 < baseStart_1993409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993586 : List Nat := [3, 2, 1, 2, 1, 1, 6, 5]
def baseStart_1993586 : Nat := 118140960795 + 1993586 * 2 ^ 59
def prefixEnd_1993586 : Nat := 4983230072969 + 3 ^ 40 * 1993586 * 2
def baseEnd_1993586 : Nat := 151654495418421084341729

theorem tailTrace_1993586 : CollatzResearch.WordTrace tailWord_1993586 prefixEnd_1993586 151654495418421084341729 := by
  unfold tailWord_1993586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18178013738896468556780153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48474703303723916151413741 18178013738896468556780153)
  ·
    refine ⟨13633510304172351417585115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18178013738896468556780153 13633510304172351417585115)
    ·
      refine ⟨20450265456258527126377673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13633510304172351417585115 20450265456258527126377673)
      ·
        refine ⟨15337699092193895344783255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20450265456258527126377673 15337699092193895344783255)
        ·
          refine ⟨23006548638290843017174883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15337699092193895344783255 23006548638290843017174883)
          ·
            refine ⟨34509822957436264525762325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23006548638290843017174883 34509822957436264525762325)
            ·
              refine ⟨1617647951129824899645109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34509822957436264525762325 1617647951129824899645109)
              ·
                refine ⟨151654495418421084341729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1617647951129824899645109 151654495418421084341729)
                ·
                  rfl

theorem cell21_1993586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_1993586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993586 prefixEnd_1993586 := by exact prefixLift 1993586
  have htrace : WordTrace (prefixWord ++ tailWord_1993586) baseStart_1993586 baseEnd_1993586 := by
    simpa [prefixWord, tailWord_1993586, baseEnd_1993586] using wordTrace_append hprefix tailTrace_1993586
  have hstable : (prefixWord ++ tailWord_1993586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993586).length < 2 ^ (prefixWord ++ tailWord_1993586).sum := by decide
  have hdescent : baseEnd_1993586 < baseStart_1993586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993676 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1993676 : Nat := 118140960795 + 1993676 * 2 ^ 59
def prefixEnd_1993676 : Nat := 4983230072969 + 3 ^ 40 * 1993676 * 2
def baseEnd_1993676 : Nat := 454984025481443096525003

theorem tailTrace_1993676 : CollatzResearch.WordTrace tailWord_1993676 prefixEnd_1993676 454984025481443096525003 := by
  unfold tailWord_1993676
  simp only [CollatzResearch.WordTrace]
  refine ⟨36357668762629909798948441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48476891683506546398597921 36357668762629909798948441)
  ·
    refine ⟨27268251571972432349211331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36357668762629909798948441 27268251571972432349211331)
    ·
      refine ⟨40902377357958648523816997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27268251571972432349211331 40902377357958648523816997)
      ·
        refine ⟨7669195754617246598215687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40902377357958648523816997 7669195754617246598215687)
        ·
          refine ⟨11503793631925869897323531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7669195754617246598215687 11503793631925869897323531)
          ·
            refine ⟨17255690447888804845985297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503793631925869897323531 17255690447888804845985297)
            ·
              refine ⟨12941767835916603634488973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17255690447888804845985297 12941767835916603634488973)
              ·
                refine ⟨4853162938468726362933365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12941767835916603634488973 4853162938468726362933365)
                ·
                  refine ⟨454984025481443096525003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853162938468726362933365 454984025481443096525003)
                  ·
                    rfl

theorem cell21_1993676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1993676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993676 prefixEnd_1993676 := by exact prefixLift 1993676
  have htrace : WordTrace (prefixWord ++ tailWord_1993676) baseStart_1993676 baseEnd_1993676 := by
    simpa [prefixWord, tailWord_1993676, baseEnd_1993676] using wordTrace_append hprefix tailTrace_1993676
  have hstable : (prefixWord ++ tailWord_1993676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993676).length < 2 ^ (prefixWord ++ tailWord_1993676).sum := by decide
  have hdescent : baseEnd_1993676 < baseStart_1993676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993693 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1993693 : Nat := 118140960795 + 1993693 * 2 ^ 59
def prefixEnd_1993693 : Nat := 4983230072969 + 3 ^ 40 * 1993693 * 2
def baseEnd_1993693 : Nat := 454987905113054844741635

theorem tailTrace_1993693 : CollatzResearch.WordTrace tailWord_1993693 prefixEnd_1993693 454987905113054844741635 := by
  unfold tailWord_1993693
  simp only [CollatzResearch.WordTrace]
  refine ⟨72715957566198231501265733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48477305044132154334177155 72715957566198231501265733)
  ·
    refine ⟨13634242043662168406487325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72715957566198231501265733 13634242043662168406487325)
    ·
      refine ⟨5112840766373313152432747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13634242043662168406487325 5112840766373313152432747)
      ·
        refine ⟨7669261149559969728649121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5112840766373313152432747 7669261149559969728649121)
        ·
          refine ⟨5751945862169977296486841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7669261149559969728649121 5751945862169977296486841)
          ·
            refine ⟨4313959396627482972365131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5751945862169977296486841 4313959396627482972365131)
            ·
              refine ⟨6470939094941224458547697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313959396627482972365131 6470939094941224458547697)
              ·
                refine ⟨4853204321205918343910773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6470939094941224458547697 4853204321205918343910773)
                ·
                  refine ⟨454987905113054844741635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853204321205918343910773 454987905113054844741635)
                  ·
                    rfl

theorem cell21_1993693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1993693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993693 prefixEnd_1993693 := by exact prefixLift 1993693
  have htrace : WordTrace (prefixWord ++ tailWord_1993693) baseStart_1993693 baseEnd_1993693 := by
    simpa [prefixWord, tailWord_1993693, baseEnd_1993693] using wordTrace_append hprefix tailTrace_1993693
  have hstable : (prefixWord ++ tailWord_1993693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993693).length < 2 ^ (prefixWord ++ tailWord_1993693).sum := by decide
  have hdescent : baseEnd_1993693 < baseStart_1993693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993716 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1993716 : Nat := 118140960795 + 1993716 * 2 ^ 59
def prefixEnd_1993716 : Nat := 4983230072969 + 3 ^ 40 * 1993716 * 2
def baseEnd_1993716 : Nat := 454993154026411915858255

theorem tailTrace_1993716 : CollatzResearch.WordTrace tailWord_1993716 prefixEnd_1993716 454993154026411915858255 := by
  unfold tailWord_1993716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36358398222557453214676501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48477864296743270952902001 36358398222557453214676501)
  ·
    refine ⟨1704299916682380619437961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36358398222557453214676501 1704299916682380619437961)
    ·
      refine ⟨1278224937511785464578471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1704299916682380619437961 1278224937511785464578471)
      ·
        refine ⟨1917337406267678196867707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278224937511785464578471 1917337406267678196867707)
        ·
          refine ⟨2876006109401517295301561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917337406267678196867707 2876006109401517295301561)
          ·
            refine ⟨2157004582051137971476171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876006109401517295301561 2157004582051137971476171)
            ·
              refine ⟨3235506873076706957214257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157004582051137971476171 3235506873076706957214257)
              ·
                refine ⟨2426630154807530217910693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3235506873076706957214257 2426630154807530217910693)
                ·
                  refine ⟨454993154026411915858255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2426630154807530217910693 454993154026411915858255)
                  ·
                    rfl

theorem cell21_1993716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1993716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993716 prefixEnd_1993716 := by exact prefixLift 1993716
  have htrace : WordTrace (prefixWord ++ tailWord_1993716) baseStart_1993716 baseEnd_1993716 := by
    simpa [prefixWord, tailWord_1993716, baseEnd_1993716] using wordTrace_append hprefix tailTrace_1993716
  have hstable : (prefixWord ++ tailWord_1993716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993716).length < 2 ^ (prefixWord ++ tailWord_1993716).sum := by decide
  have hdescent : baseEnd_1993716 < baseStart_1993716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993724 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1993724 : Nat := 118140960795 + 1993724 * 2 ^ 59
def prefixEnd_1993724 : Nat := 4983230072969 + 3 ^ 40 * 1993724 * 2
def baseEnd_1993724 : Nat := 454994979735405679724905

theorem tailTrace_1993724 : CollatzResearch.WordTrace tailWord_1993724 prefixEnd_1993724 454994979735405679724905 := by
  unfold tailWord_1993724
  simp only [CollatzResearch.WordTrace]
  refine ⟨36358544114542961897822113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48478058819390615863762817 36358544114542961897822113)
  ·
    refine ⟨27268908085907221423366585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36358544114542961897822113 27268908085907221423366585)
    ·
      refine ⟨20451681064430416067524939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27268908085907221423366585 20451681064430416067524939)
      ·
        refine ⟨30677521596645624101287409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20451681064430416067524939 30677521596645624101287409)
        ·
          refine ⟨23008141197484218075965557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30677521596645624101287409 23008141197484218075965557)
          ·
            refine ⟨2157013237264145444621771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23008141197484218075965557 2157013237264145444621771)
            ·
              refine ⟨3235519855896218166932657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157013237264145444621771 3235519855896218166932657)
              ·
                refine ⟨2426639891922163625199493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3235519855896218166932657 2426639891922163625199493)
                ·
                  refine ⟨454994979735405679724905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2426639891922163625199493 454994979735405679724905)
                  ·
                    rfl

theorem cell21_1993724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1993724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993724 prefixEnd_1993724 := by exact prefixLift 1993724
  have htrace : WordTrace (prefixWord ++ tailWord_1993724) baseStart_1993724 baseEnd_1993724 := by
    simpa [prefixWord, tailWord_1993724, baseEnd_1993724] using wordTrace_append hprefix tailTrace_1993724
  have hstable : (prefixWord ++ tailWord_1993724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993724).length < 2 ^ (prefixWord ++ tailWord_1993724).sum := by decide
  have hdescent : baseEnd_1993724 < baseStart_1993724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993752 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_1993752 : Nat := 118140960795 + 1993752 * 2 ^ 59
def prefixEnd_1993752 : Nat := 4983230072969 + 3 ^ 40 * 1993752 * 2
def baseEnd_1993752 : Nat := 455001369716883853258181

theorem tailTrace_1993752 : CollatzResearch.WordTrace tailWord_1993752 prefixEnd_1993752 455001369716883853258181 := by
  unfold tailWord_1993752
  simp only [CollatzResearch.WordTrace]
  refine ⟨36359054736492242288831755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48478739648656323051775673 36359054736492242288831755)
  ·
    refine ⟨54538582104738363433247633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36359054736492242288831755 54538582104738363433247633)
    ·
      refine ⟨40903936578553772574935725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54538582104738363433247633 40903936578553772574935725)
      ·
        refine ⟨15338976216957664715600897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40903936578553772574935725 15338976216957664715600897)
        ·
          refine ⟨11504232162718248536700673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15338976216957664715600897 11504232162718248536700673)
          ·
            refine ⟨8628174122038686402525505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11504232162718248536700673 8628174122038686402525505)
            ·
              refine ⟨6471130591529014801894129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628174122038686402525505 6471130591529014801894129)
              ·
                refine ⟨4853347943646761101420597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471130591529014801894129 4853347943646761101420597)
                ·
                  refine ⟨455001369716883853258181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853347943646761101420597 455001369716883853258181)
                  ·
                    rfl

theorem cell21_1993752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_1993752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993752 prefixEnd_1993752 := by exact prefixLift 1993752
  have htrace : WordTrace (prefixWord ++ tailWord_1993752) baseStart_1993752 baseEnd_1993752 := by
    simpa [prefixWord, tailWord_1993752, baseEnd_1993752] using wordTrace_append hprefix tailTrace_1993752
  have hstable : (prefixWord ++ tailWord_1993752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993752).length < 2 ^ (prefixWord ++ tailWord_1993752).sum := by decide
  have hdescent : baseEnd_1993752 < baseStart_1993752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993890 : List Nat := [3, 3, 1, 3, 2, 1, 8]
def baseStart_1993890 : Nat := 118140960795 + 1993890 * 2 ^ 59
def prefixEnd_1993890 : Nat := 4983230072969 + 3 ^ 40 * 1993890 * 2
def baseEnd_1993890 : Nat := 50559207021891808884211

theorem tailTrace_1993890 : CollatzResearch.WordTrace tailWord_1993890 prefixEnd_1993890 50559207021891808884211 := by
  unfold tailWord_1993890
  simp only [CollatzResearch.WordTrace]
  refine ⟨18180785686621133536546781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48482095164323022764124749 18180785686621133536546781)
  ·
    refine ⟨6817794632482925076205043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18180785686621133536546781 6817794632482925076205043)
    ·
      refine ⟨10226691948724387614307565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6817794632482925076205043 10226691948724387614307565)
      ·
        refine ⟨3835009480771645355365337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10226691948724387614307565 3835009480771645355365337)
        ·
          refine ⟨2876257110578734016524003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3835009480771645355365337 2876257110578734016524003)
          ·
            refine ⟨4314385665868101024786005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2876257110578734016524003 4314385665868101024786005)
            ·
              refine ⟨50559207021891808884211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4314385665868101024786005 50559207021891808884211)
              ·
                rfl

theorem cell21_1993890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 8].length) (baseStart_1993890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993890 prefixEnd_1993890 := by exact prefixLift 1993890
  have htrace : WordTrace (prefixWord ++ tailWord_1993890) baseStart_1993890 baseEnd_1993890 := by
    simpa [prefixWord, tailWord_1993890, baseEnd_1993890] using wordTrace_append hprefix tailTrace_1993890
  have hstable : (prefixWord ++ tailWord_1993890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993890).length < 2 ^ (prefixWord ++ tailWord_1993890).sum := by decide
  have hdescent : baseEnd_1993890 < baseStart_1993890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993921 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 5]
def baseStart_1993921 : Nat := 118140960795 + 1993921 * 2 ^ 59
def prefixEnd_1993921 : Nat := 4983230072969 + 3 ^ 40 * 1993921 * 2
def baseEnd_1993921 : Nat := 455039937819377114941169

theorem tailTrace_1993921 : CollatzResearch.WordTrace tailWord_1993921 prefixEnd_1993921 455039937819377114941169 := by
  unfold tailWord_1993921
  simp only [CollatzResearch.WordTrace]
  refine ⟨72724273409372226440565617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48482848939581484293710411 72724273409372226440565617)
  ·
    refine ⟨54543205057029169830424213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72724273409372226440565617 54543205057029169830424213)
    ·
      refine ⟨2556712737048242335801135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54543205057029169830424213 2556712737048242335801135)
      ·
        refine ⟨3835069105572363503701703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556712737048242335801135 3835069105572363503701703)
        ·
          refine ⟨5752603658358545255552555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835069105572363503701703 5752603658358545255552555)
          ·
            refine ⟨8628905487537817883328833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752603658358545255552555 8628905487537817883328833)
            ·
              refine ⟨6471679115653363412496625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628905487537817883328833 6471679115653363412496625)
              ·
                refine ⟨4853759336740022559372469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6471679115653363412496625 4853759336740022559372469)
                ·
                  refine ⟨455039937819377114941169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4853759336740022559372469 455039937819377114941169)
                  ·
                    rfl

theorem cell21_1993921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_1993921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993921 prefixEnd_1993921 := by exact prefixLift 1993921
  have htrace : WordTrace (prefixWord ++ tailWord_1993921) baseStart_1993921 baseEnd_1993921 := by
    simpa [prefixWord, tailWord_1993921, baseEnd_1993921] using wordTrace_append hprefix tailTrace_1993921
  have hstable : (prefixWord ++ tailWord_1993921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993921).length < 2 ^ (prefixWord ++ tailWord_1993921).sum := by decide
  have hdescent : baseEnd_1993921 < baseStart_1993921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1993924 : List Nat := [2, 3, 3, 1, 4, 1, 2, 5]
def baseStart_1993924 : Nat := 118140960795 + 1993924 * 2 ^ 59
def prefixEnd_1993924 : Nat := 4983230072969 + 3 ^ 40 * 1993924 * 2
def baseEnd_1993924 : Nat := 151680207486749925463721

theorem tailTrace_1993924 : CollatzResearch.WordTrace tailWord_1993924 prefixEnd_1993924 151680207486749925463721 := by
  unfold tailWord_1993924
  simp only [CollatzResearch.WordTrace]
  refine ⟨36362191414180678976462413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48482921885574238635283217 36362191414180678976462413)
  ·
    refine ⟨13635821780317754616173405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36362191414180678976462413 13635821780317754616173405)
    ·
      refine ⟨5113433167619157981065027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13635821780317754616173405 5113433167619157981065027)
      ·
        refine ⟨7670149751428736971597541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113433167619157981065027 7670149751428736971597541)
        ·
          refine ⟨1438153078392888182174539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7670149751428736971597541 1438153078392888182174539)
          ·
            refine ⟨2157229617589332273261809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438153078392888182174539 2157229617589332273261809)
            ·
              refine ⟨1617922213191999204946357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157229617589332273261809 1617922213191999204946357)
              ·
                refine ⟨151680207486749925463721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1617922213191999204946357 151680207486749925463721)
                ·
                  rfl

theorem cell21_1993924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_1993924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1993924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1993924 prefixEnd_1993924 := by exact prefixLift 1993924
  have htrace : WordTrace (prefixWord ++ tailWord_1993924) baseStart_1993924 baseEnd_1993924 := by
    simpa [prefixWord, tailWord_1993924, baseEnd_1993924] using wordTrace_append hprefix tailTrace_1993924
  have hstable : (prefixWord ++ tailWord_1993924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1993924).length < 2 ^ (prefixWord ++ tailWord_1993924).sum := by decide
  have hdescent : baseEnd_1993924 < baseStart_1993924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1993924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994008 : List Nat := [2, 1, 2, 3, 1, 12]
def baseStart_1994008 : Nat := 118140960795 + 1994008 * 2 ^ 59
def prefixEnd_1994008 : Nat := 4983230072969 + 3 ^ 40 * 1994008 * 2
def baseEnd_1994008 : Nat := 16854066385358677666333

theorem tailTrace_1994008 : CollatzResearch.WordTrace tailWord_1994008 prefixEnd_1994008 16854066385358677666333 := by
  unfold tailWord_1994008
  simp only [CollatzResearch.WordTrace]
  refine ⟨36363723280028520149491339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48484964373371360199321785 36363723280028520149491339)
  ·
    refine ⟨54545584920042780224237009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36363723280028520149491339 54545584920042780224237009)
    ·
      refine ⟨40909188690032085168177757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54545584920042780224237009 40909188690032085168177757)
      ·
        refine ⟨15340945758762031938066659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40909188690032085168177757 15340945758762031938066659)
        ·
          refine ⟨23011418638143047907099989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15340945758762031938066659 23011418638143047907099989)
          ·
            refine ⟨16854066385358677666333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23011418638143047907099989 16854066385358677666333)
            ·
              rfl

theorem cell21_1994008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 12].length) (baseStart_1994008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994008 prefixEnd_1994008 := by exact prefixLift 1994008
  have htrace : WordTrace (prefixWord ++ tailWord_1994008) baseStart_1994008 baseEnd_1994008 := by
    simpa [prefixWord, tailWord_1994008, baseEnd_1994008] using wordTrace_append hprefix tailTrace_1994008
  have hstable : (prefixWord ++ tailWord_1994008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994008).length < 2 ^ (prefixWord ++ tailWord_1994008).sum := by decide
  have hdescent : baseEnd_1994008 < baseStart_1994008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994177 : List Nat := [1, 2, 7, 11]
def baseStart_1994177 : Nat := 118140960795 + 1994177 * 2 ^ 59
def prefixEnd_1994177 : Nat := 4983230072969 + 3 ^ 40 * 1994177 * 2
def baseEnd_1994177 : Nat := 1872832759288796537753

theorem tailTrace_1994177 : CollatzResearch.WordTrace tailWord_1994177 prefixEnd_1994177 1872832759288796537753 := by
  unfold tailWord_1994177
  simp only [CollatzResearch.WordTrace]
  refine ⟨72733610496444782161884785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48489073664296521441256523 72733610496444782161884785)
  ·
    refine ⟨54550207872333586621413589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72733610496444782161884785 54550207872333586621413589)
    ·
      refine ⟨1278520497007818436439381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54550207872333586621413589 1278520497007818436439381)
      ·
        refine ⟨1872832759288796537753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1278520497007818436439381 1872832759288796537753)
        ·
          rfl

theorem cell21_1994177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 11].length) (baseStart_1994177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994177 prefixEnd_1994177 := by exact prefixLift 1994177
  have htrace : WordTrace (prefixWord ++ tailWord_1994177) baseStart_1994177 baseEnd_1994177 := by
    simpa [prefixWord, tailWord_1994177, baseEnd_1994177] using wordTrace_append hprefix tailTrace_1994177
  have hstable : (prefixWord ++ tailWord_1994177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994177).length < 2 ^ (prefixWord ++ tailWord_1994177).sum := by decide
  have hdescent : baseEnd_1994177 < baseStart_1994177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994180 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1994180 : Nat := 118140960795 + 1994180 * 2 ^ 59
def prefixEnd_1994180 : Nat := 4983230072969 + 3 ^ 40 * 1994180 * 2
def baseEnd_1994180 : Nat := 455099045148050220123973

theorem tailTrace_1994180 : CollatzResearch.WordTrace tailWord_1994180 prefixEnd_1994180 455099045148050220123973 := by
  unfold tailWord_1994180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36366859957716956837121997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48489146610289275782829329 36366859957716956837121997)
  ·
    refine ⟨13637572484143858813920749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36366859957716956837121997 13637572484143858813920749)
    ·
      refine ⟨5114089681553947055220281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13637572484143858813920749 5114089681553947055220281)
      ·
        refine ⟨3835567261165460291415211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5114089681553947055220281 3835567261165460291415211)
        ·
          refine ⟨5753350891748190437122817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835567261165460291415211 5753350891748190437122817)
          ·
            refine ⟨4315013168811142827842113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5753350891748190437122817 4315013168811142827842113)
            ·
              refine ⟨3236259876608357120881585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315013168811142827842113 3236259876608357120881585)
              ·
                refine ⟨2427194907456267840661189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236259876608357120881585 2427194907456267840661189)
                ·
                  refine ⟨455099045148050220123973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427194907456267840661189 455099045148050220123973)
                  ·
                    rfl

theorem cell21_1994180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1994180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994180 prefixEnd_1994180 := by exact prefixLift 1994180
  have htrace : WordTrace (prefixWord ++ tailWord_1994180) baseStart_1994180 baseEnd_1994180 := by
    simpa [prefixWord, tailWord_1994180, baseEnd_1994180] using wordTrace_append hprefix tailTrace_1994180
  have hstable : (prefixWord ++ tailWord_1994180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994180).length < 2 ^ (prefixWord ++ tailWord_1994180).sum := by decide
  have hdescent : baseEnd_1994180 < baseStart_1994180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994222 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1994222 : Nat := 118140960795 + 1994222 * 2 ^ 59
def prefixEnd_1994222 : Nat := 4983230072969 + 3 ^ 40 * 1994222 * 2
def baseEnd_1994222 : Nat := 455108630120267480423887

theorem tailTrace_1994222 : CollatzResearch.WordTrace tailWord_1994222 prefixEnd_1994222 455108630120267480423887 := by
  unfold tailWord_1994222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9091906472660219355909115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48490167854187836564848613 9091906472660219355909115)
  ·
    refine ⟨13637859708990329033863673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9091906472660219355909115 13637859708990329033863673)
    ·
      refine ⟨10228394781742746775397755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13637859708990329033863673 10228394781742746775397755)
      ·
        refine ⟨15342592172614120163096633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10228394781742746775397755 15342592172614120163096633)
        ·
          refine ⟨11506944129460590122322475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15342592172614120163096633 11506944129460590122322475)
          ·
            refine ⟨17260416194190885183483713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11506944129460590122322475 17260416194190885183483713)
            ·
              refine ⟨12945312145643163887612785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17260416194190885183483713 12945312145643163887612785)
              ·
                refine ⟨9708984109232372915709589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12945312145643163887612785 9708984109232372915709589)
                ·
                  refine ⟨455108630120267480423887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9708984109232372915709589 455108630120267480423887)
                  ·
                    rfl

theorem cell21_1994222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1994222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994222 prefixEnd_1994222 := by exact prefixLift 1994222
  have htrace : WordTrace (prefixWord ++ tailWord_1994222) baseStart_1994222 baseEnd_1994222 := by
    simpa [prefixWord, tailWord_1994222, baseEnd_1994222] using wordTrace_append hprefix tailTrace_1994222
  have hstable : (prefixWord ++ tailWord_1994222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994222).length < 2 ^ (prefixWord ++ tailWord_1994222).sum := by decide
  have hdescent : baseEnd_1994222 < baseStart_1994222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994225 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 3]
def baseStart_1994225 : Nat := 118140960795 + 1994225 * 2 ^ 59
def prefixEnd_1994225 : Nat := 4983230072969 + 3 ^ 40 * 1994225 * 2
def baseEnd_1994225 : Nat := 455109314761140141873881

theorem tailTrace_1994225 : CollatzResearch.WordTrace tailWord_1994225 prefixEnd_1994225 455109314761140141873881 := by
  unfold tailWord_1994225
  simp only [CollatzResearch.WordTrace]
  refine ⟨72735361200270886359632129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48490240800180590906421419 72735361200270886359632129)
  ·
    refine ⟨54551520900203164769724097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72735361200270886359632129 54551520900203164769724097)
    ·
      refine ⟨40913640675152373577293073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54551520900203164769724097 40913640675152373577293073)
      ·
        refine ⟨30685230506364280182969805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40913640675152373577293073 30685230506364280182969805)
        ·
          refine ⟨11506961439886605068613677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30685230506364280182969805 11506961439886605068613677)
          ·
            refine ⟨4315110539957476900730129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11506961439886605068613677 4315110539957476900730129)
            ·
              refine ⟨3236332904968107675547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4315110539957476900730129 3236332904968107675547597)
              ·
                refine ⟨1213624839363040378330349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3236332904968107675547597 1213624839363040378330349)
                ·
                  refine ⟨455109314761140141873881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213624839363040378330349 455109314761140141873881)
                  ·
                    rfl

theorem cell21_1994225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_1994225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994225 prefixEnd_1994225 := by exact prefixLift 1994225
  have htrace : WordTrace (prefixWord ++ tailWord_1994225) baseStart_1994225 baseEnd_1994225 := by
    simpa [prefixWord, tailWord_1994225, baseEnd_1994225] using wordTrace_append hprefix tailTrace_1994225
  have hstable : (prefixWord ++ tailWord_1994225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994225).length < 2 ^ (prefixWord ++ tailWord_1994225).sum := by decide
  have hdescent : baseEnd_1994225 < baseStart_1994225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994242 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1994242 : Nat := 118140960795 + 1994242 * 2 ^ 59
def prefixEnd_1994242 : Nat := 4983230072969 + 3 ^ 40 * 1994242 * 2
def baseEnd_1994242 : Nat := 455113194392751890090513

theorem tailTrace_1994242 : CollatzResearch.WordTrace tailWord_1994242 prefixEnd_1994242 455113194392751890090513 := by
  unfold tailWord_1994242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183995310302324565750245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48490654160806198842000653 18183995310302324565750245)
  ·
    refine ⟨3409499120681685856078171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18183995310302324565750245 3409499120681685856078171)
    ·
      refine ⟨5114248681022528784117257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409499120681685856078171 5114248681022528784117257)
      ·
        refine ⟨3835686510766896588087943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5114248681022528784117257 3835686510766896588087943)
        ·
          refine ⟨5753529766150344882131915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835686510766896588087943 5753529766150344882131915)
          ·
            refine ⟨8630294649225517323197873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5753529766150344882131915 8630294649225517323197873)
            ·
              refine ⟨6472720986919137992398405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8630294649225517323197873 6472720986919137992398405)
              ·
                refine ⟨1213635185047338373574701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6472720986919137992398405 1213635185047338373574701)
                ·
                  refine ⟨455113194392751890090513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213635185047338373574701 455113194392751890090513)
                  ·
                    rfl

theorem cell21_1994242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1994242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994242 prefixEnd_1994242 := by exact prefixLift 1994242
  have htrace : WordTrace (prefixWord ++ tailWord_1994242) baseStart_1994242 baseEnd_1994242 := by
    simpa [prefixWord, tailWord_1994242, baseEnd_1994242] using wordTrace_append hprefix tailTrace_1994242
  have hstable : (prefixWord ++ tailWord_1994242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994242).length < 2 ^ (prefixWord ++ tailWord_1994242).sum := by decide
  have hdescent : baseEnd_1994242 < baseStart_1994242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994298 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_1994298 : Nat := 118140960795 + 1994298 * 2 ^ 59
def prefixEnd_1994298 : Nat := 4983230072969 + 3 ^ 40 * 1994298 * 2
def baseEnd_1994298 : Nat := 455125974355708237157065

theorem tailTrace_1994298 : CollatzResearch.WordTrace tailWord_1994298 prefixEnd_1994298 455125974355708237157065 := by
  unfold tailWord_1994298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184505932251604956759887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48492015819337613218026365 18184505932251604956759887)
  ·
    refine ⟨27276758898377407435139831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18184505932251604956759887 27276758898377407435139831)
    ·
      refine ⟨40915138347566111152709747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27276758898377407435139831 40915138347566111152709747)
      ·
        refine ⟨61372707521349166729064621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40915138347566111152709747 61372707521349166729064621)
        ·
          refine ⟨23014765320505937523399233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61372707521349166729064621 23014765320505937523399233)
          ·
            refine ⟨17261073990379453142549425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23014765320505937523399233 17261073990379453142549425)
            ·
              refine ⟨12945805492784589856912069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17261073990379453142549425 12945805492784589856912069)
              ·
                refine ⟨2427338529897110598171013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12945805492784589856912069 2427338529897110598171013)
                ·
                  refine ⟨455125974355708237157065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427338529897110598171013 455125974355708237157065)
                  ·
                    rfl

theorem cell21_1994298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_1994298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994298 prefixEnd_1994298 := by exact prefixLift 1994298
  have htrace : WordTrace (prefixWord ++ tailWord_1994298) baseStart_1994298 baseEnd_1994298 := by
    simpa [prefixWord, tailWord_1994298, baseEnd_1994298] using wordTrace_append hprefix tailTrace_1994298
  have hstable : (prefixWord ++ tailWord_1994298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994298).length < 2 ^ (prefixWord ++ tailWord_1994298).sum := by decide
  have hdescent : baseEnd_1994298 < baseStart_1994298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994301 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1994301 : Nat := 118140960795 + 1994301 * 2 ^ 59
def prefixEnd_1994301 : Nat := 4983230072969 + 3 ^ 40 * 1994301 * 2
def baseEnd_1994301 : Nat := 455126658996580898607059

theorem tailTrace_1994301 : CollatzResearch.WordTrace tailWord_1994301 prefixEnd_1994301 455126658996580898607059 := by
  unfold tailWord_1994301
  simp only [CollatzResearch.WordTrace]
  refine ⟨72738133147995551339398757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48492088765330367559599171 72738133147995551339398757)
  ·
    refine ⟨13638399965249165876137267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72738133147995551339398757 13638399965249165876137267)
    ·
      refine ⟨20457599947873748814205901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13638399965249165876137267 20457599947873748814205901)
      ·
        refine ⟨7671599980452655805327213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20457599947873748814205901 7671599980452655805327213)
        ·
          refine ⟨2876849992669745926997705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7671599980452655805327213 2876849992669745926997705)
          ·
            refine ⟨2157637494502309445248279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2876849992669745926997705 2157637494502309445248279)
            ·
              refine ⟨3236456241753464167872419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157637494502309445248279 3236456241753464167872419)
              ·
                refine ⟨4854684362630196251808629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236456241753464167872419 4854684362630196251808629)
                ·
                  refine ⟨455126658996580898607059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4854684362630196251808629 455126658996580898607059)
                  ·
                    rfl

theorem cell21_1994301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1994301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994301 prefixEnd_1994301 := by exact prefixLift 1994301
  have htrace : WordTrace (prefixWord ++ tailWord_1994301) baseStart_1994301 baseEnd_1994301 := by
    simpa [prefixWord, tailWord_1994301, baseEnd_1994301] using wordTrace_append hprefix tailTrace_1994301
  have hstable : (prefixWord ++ tailWord_1994301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994301).length < 2 ^ (prefixWord ++ tailWord_1994301).sum := by decide
  have hdescent : baseEnd_1994301 < baseStart_1994301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994419 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 5]
def baseStart_1994419 : Nat := 118140960795 + 1994419 * 2 ^ 59
def prefixEnd_1994419 : Nat := 4983230072969 + 3 ^ 40 * 1994419 * 2
def baseEnd_1994419 : Nat := 455153588204238915640151

theorem tailTrace_1994419 : CollatzResearch.WordTrace tailWord_1994419 prefixEnd_1994419 455153588204238915640151 := by
  unfold tailWord_1994419
  simp only [CollatzResearch.WordTrace]
  refine ⟨72742436961568057492194311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48494957974378704994796207 72742436961568057492194311)
  ·
    refine ⟨109113655442352086238291467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72742436961568057492194311 109113655442352086238291467)
    ·
      refine ⟨163670483163528129357437201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109113655442352086238291467 163670483163528129357437201)
      ·
        refine ⟨122752862372646097018077901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163670483163528129357437201 122752862372646097018077901)
        ·
          refine ⟨46032323389742286381779213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122752862372646097018077901 46032323389742286381779213)
          ·
            refine ⟨17262121271153357393167205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46032323389742286381779213 17262121271153357393167205)
            ·
              refine ⟨3236647738341254511218851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17262121271153357393167205 3236647738341254511218851)
              ·
                refine ⟨4854971607511881766828277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236647738341254511218851 4854971607511881766828277)
                ·
                  refine ⟨455153588204238915640151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4854971607511881766828277 455153588204238915640151)
                  ·
                    rfl

theorem cell21_1994419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 5].length) (baseStart_1994419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994419 prefixEnd_1994419 := by exact prefixLift 1994419
  have htrace : WordTrace (prefixWord ++ tailWord_1994419) baseStart_1994419 baseEnd_1994419 := by
    simpa [prefixWord, tailWord_1994419, baseEnd_1994419] using wordTrace_append hprefix tailTrace_1994419
  have hstable : (prefixWord ++ tailWord_1994419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994419).length < 2 ^ (prefixWord ++ tailWord_1994419).sum := by decide
  have hdescent : baseEnd_1994419 < baseStart_1994419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994450 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1994450 : Nat := 118140960795 + 1994450 * 2 ^ 59
def prefixEnd_1994450 : Nat := 4983230072969 + 3 ^ 40 * 1994450 * 2
def baseEnd_1994450 : Nat := 455160662826589750623421

theorem tailTrace_1994450 : CollatzResearch.WordTrace tailWord_1994450 prefixEnd_1994450 455160662826589750623421 := by
  unfold tailWord_1994450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185891906113937446643201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48495711749637166524381869 18185891906113937446643201)
  ·
    refine ⟨13639418929585453084982401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18185891906113937446643201 13639418929585453084982401)
    ·
      refine ⟨10229564197189089813736801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13639418929585453084982401 10229564197189089813736801)
      ·
        refine ⟨7672173147891817360302601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10229564197189089813736801 7672173147891817360302601)
        ·
          refine ⟨5754129860918863020226951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7672173147891817360302601 5754129860918863020226951)
          ·
            refine ⟨8631194791378294530340427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754129860918863020226951 8631194791378294530340427)
            ·
              refine ⟨12946792187067441795510641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8631194791378294530340427 12946792187067441795510641)
              ·
                refine ⟨9710094140300581346632981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12946792187067441795510641 9710094140300581346632981)
                ·
                  refine ⟨455160662826589750623421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9710094140300581346632981 455160662826589750623421)
                  ·
                    rfl

theorem cell21_1994450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1994450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994450 prefixEnd_1994450 := by exact prefixLift 1994450
  have htrace : WordTrace (prefixWord ++ tailWord_1994450) baseStart_1994450 baseEnd_1994450 := by
    simpa [prefixWord, tailWord_1994450, baseEnd_1994450] using wordTrace_append hprefix tailTrace_1994450
  have hstable : (prefixWord ++ tailWord_1994450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994450).length < 2 ^ (prefixWord ++ tailWord_1994450).sum := by decide
  have hdescent : baseEnd_1994450 < baseStart_1994450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994529 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 3]
def baseStart_1994529 : Nat := 118140960795 + 1994529 * 2 ^ 59
def prefixEnd_1994529 : Nat := 4983230072969 + 3 ^ 40 * 1994529 * 2
def baseEnd_1994529 : Nat := 455178691702903168806593

theorem tailTrace_1994529 : CollatzResearch.WordTrace tailWord_1994529 prefixEnd_1994529 455178691702903168806593 := by
  unfold tailWord_1994529
  simp only [CollatzResearch.WordTrace]
  refine ⟨72746448991169546278698641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48497632660779697519132427 72746448991169546278698641)
  ·
    refine ⟨54559836743377159709023981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72746448991169546278698641 54559836743377159709023981)
    ·
      refine ⟨20459938778766434890883993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54559836743377159709023981 20459938778766434890883993)
      ·
        refine ⟨15344954084074826168162995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20459938778766434890883993 15344954084074826168162995)
        ·
          refine ⟨23017431126112239252244493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15344954084074826168162995 23017431126112239252244493)
          ·
            refine ⟨8631536672292089719591685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23017431126112239252244493 8631536672292089719591685)
            ·
              refine ⟨1618413126054766822423441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8631536672292089719591685 1618413126054766822423441)
              ·
                refine ⟨1213809844541075116817581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618413126054766822423441 1213809844541075116817581)
                ·
                  refine ⟨455178691702903168806593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213809844541075116817581 455178691702903168806593)
                  ·
                    rfl

theorem cell21_1994529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_1994529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994529 prefixEnd_1994529 := by exact prefixLift 1994529
  have htrace : WordTrace (prefixWord ++ tailWord_1994529) baseStart_1994529 baseEnd_1994529 := by
    simpa [prefixWord, tailWord_1994529, baseEnd_1994529] using wordTrace_append hprefix tailTrace_1994529
  have hstable : (prefixWord ++ tailWord_1994529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994529).length < 2 ^ (prefixWord ++ tailWord_1994529).sum := by decide
  have hdescent : baseEnd_1994529 < baseStart_1994529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994540 : List Nat := [2, 2, 1, 1, 1, 5, 3, 6]
def baseStart_1994540 : Nat := 118140960795 + 1994540 * 2 ^ 59
def prefixEnd_1994540 : Nat := 4983230072969 + 3 ^ 40 * 1994540 * 2
def baseEnd_1994540 : Nat := 151727067350923198041079

theorem tailTrace_1994540 : CollatzResearch.WordTrace tailWord_1994540 prefixEnd_1994540 151727067350923198041079 := by
  unfold tailWord_1994540
  simp only [CollatzResearch.WordTrace]
  refine ⟨36373425097064847578674537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48497900129419796771566049 36373425097064847578674537)
  ·
    refine ⟨27280068822798635684005903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36373425097064847578674537 27280068822798635684005903)
    ·
      refine ⟨40920103234197953526008855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27280068822798635684005903 40920103234197953526008855)
      ·
        refine ⟨61380154851296930289013283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40920103234197953526008855 61380154851296930289013283)
        ·
          refine ⟨92070232276945395433519925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61380154851296930289013283 92070232276945395433519925)
          ·
            refine ⟨8631584275963630821892493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92070232276945395433519925 8631584275963630821892493)
            ·
              refine ⟨3236844103486361558209685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8631584275963630821892493 3236844103486361558209685)
              ·
                refine ⟨151727067350923198041079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3236844103486361558209685 151727067350923198041079)
                ·
                  rfl

theorem cell21_1994540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_1994540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994540 prefixEnd_1994540 := by exact prefixLift 1994540
  have htrace : WordTrace (prefixWord ++ tailWord_1994540) baseStart_1994540 baseEnd_1994540 := by
    simpa [prefixWord, tailWord_1994540, baseEnd_1994540] using wordTrace_append hprefix tailTrace_1994540
  have hstable : (prefixWord ++ tailWord_1994540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994540).length < 2 ^ (prefixWord ++ tailWord_1994540).sum := by decide
  have hdescent : baseEnd_1994540 < baseStart_1994540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994585 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_1994585 : Nat := 118140960795 + 1994585 * 2 ^ 59
def prefixEnd_1994585 : Nat := 4983230072969 + 3 ^ 40 * 1994585 * 2
def baseEnd_1994585 : Nat := 455191471665859515873145

theorem tailTrace_1994585 : CollatzResearch.WordTrace tailWord_1994585 prefixEnd_1994585 455191471665859515873145 := by
  unfold tailWord_1994585
  simp only [CollatzResearch.WordTrace]
  refine ⟨72748491478966667842737209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48498994319311111895158139 72748491478966667842737209)
  ·
    refine ⟨54561368609225000882052907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72748491478966667842737209 54561368609225000882052907)
    ·
      refine ⟨81842052913837501323079361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54561368609225000882052907 81842052913837501323079361)
      ·
        refine ⟨61381539685378125992309521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81842052913837501323079361 61381539685378125992309521)
        ·
          refine ⟨46036154764033594494232141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61381539685378125992309521 46036154764033594494232141)
          ·
            refine ⟨17263558036512597935337053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46036154764033594494232141 17263558036512597935337053)
            ·
              refine ⟨6473834263692224225751395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17263558036512597935337053 6473834263692224225751395)
              ·
                refine ⟨9710751395538336338627093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473834263692224225751395 9710751395538336338627093)
                ·
                  refine ⟨455191471665859515873145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9710751395538336338627093 455191471665859515873145)
                  ·
                    rfl

theorem cell21_1994585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_1994585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994585 prefixEnd_1994585 := by exact prefixLift 1994585
  have htrace : WordTrace (prefixWord ++ tailWord_1994585) baseStart_1994585 baseEnd_1994585 := by
    simpa [prefixWord, tailWord_1994585, baseEnd_1994585] using wordTrace_append hprefix tailTrace_1994585
  have hstable : (prefixWord ++ tailWord_1994585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994585).length < 2 ^ (prefixWord ++ tailWord_1994585).sum := by decide
  have hdescent : baseEnd_1994585 < baseStart_1994585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994622 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1994622 : Nat := 118140960795 + 1994622 * 2 ^ 59
def prefixEnd_1994622 : Nat := 4983230072969 + 3 ^ 40 * 1994622 * 2
def baseEnd_1994622 : Nat := 455199915569955673756403

theorem tailTrace_1994622 : CollatzResearch.WordTrace tailWord_1994622 prefixEnd_1994622 455199915569955673756403 := by
  unfold tailWord_1994622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093730122479077895229265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48499893986555082107889413 9093730122479077895229265)
  ·
    refine ⟨6820297591859308421421949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9093730122479077895229265 6820297591859308421421949)
    ·
      refine ⟨2557611596947240658033231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6820297591859308421421949 2557611596947240658033231)
      ·
        refine ⟨3836417395420860987049847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557611596947240658033231 3836417395420860987049847)
        ·
          refine ⟨5754626093131291480574771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3836417395420860987049847 5754626093131291480574771)
          ·
            refine ⟨8631939139696937220862157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754626093131291480574771 8631939139696937220862157)
            ·
              refine ⟨3236977177386351457823309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8631939139696937220862157 3236977177386351457823309)
              ·
                refine ⟨1213866441519881796683741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3236977177386351457823309 1213866441519881796683741)
                ·
                  refine ⟨455199915569955673756403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213866441519881796683741 455199915569955673756403)
                  ·
                    rfl

theorem cell21_1994622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1994622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994622 prefixEnd_1994622 := by exact prefixLift 1994622
  have htrace : WordTrace (prefixWord ++ tailWord_1994622) baseStart_1994622 baseEnd_1994622 := by
    simpa [prefixWord, tailWord_1994622, baseEnd_1994622] using wordTrace_append hprefix tailTrace_1994622
  have hstable : (prefixWord ++ tailWord_1994622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994622).length < 2 ^ (prefixWord ++ tailWord_1994622).sum := by decide
  have hdescent : baseEnd_1994622 < baseStart_1994622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994647 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 5]
def baseStart_1994647 : Nat := 118140960795 + 1994647 * 2 ^ 59
def prefixEnd_1994647 : Nat := 4983230072969 + 3 ^ 40 * 1994647 * 2
def baseEnd_1994647 : Nat := 455205620910561185839685

theorem tailTrace_1994647 : CollatzResearch.WordTrace tailWord_1994647 prefixEnd_1994647 455205620910561185839685 := by
  unfold tailWord_1994647
  simp only [CollatzResearch.WordTrace]
  refine ⟨72750752804742052431494195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48500501869828034954329463 72750752804742052431494195)
  ·
    refine ⟨109126129207113078647241293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72750752804742052431494195 109126129207113078647241293)
    ·
      refine ⟨40922298452667404492715485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109126129207113078647241293 40922298452667404492715485)
      ·
        refine ⟨15345861919750276684768307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40922298452667404492715485 15345861919750276684768307)
        ·
          refine ⟨23018792879625415027152461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15345861919750276684768307 23018792879625415027152461)
          ·
            refine ⟨8632047329859530635182173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23018792879625415027152461 8632047329859530635182173)
            ·
              refine ⟨3237017748697323988193315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8632047329859530635182173 3237017748697323988193315)
              ·
                refine ⟨4855526623045985982289973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237017748697323988193315 4855526623045985982289973)
                ·
                  refine ⟨455205620910561185839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4855526623045985982289973 455205620910561185839685)
                  ·
                    rfl

theorem cell21_1994647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_1994647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994647 prefixEnd_1994647 := by exact prefixLift 1994647
  have htrace : WordTrace (prefixWord ++ tailWord_1994647) baseStart_1994647 baseEnd_1994647 := by
    simpa [prefixWord, tailWord_1994647, baseEnd_1994647] using wordTrace_append hprefix tailTrace_1994647
  have hstable : (prefixWord ++ tailWord_1994647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994647).length < 2 ^ (prefixWord ++ tailWord_1994647).sum := by decide
  have hdescent : baseEnd_1994647 < baseStart_1994647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994675 : List Nat := [1, 1, 1, 2, 3, 1, 3, 9]
def baseStart_1994675 : Nat := 118140960795 + 1994675 * 2 ^ 59
def prefixEnd_1994675 : Nat := 4983230072969 + 3 ^ 40 * 1994675 * 2
def baseEnd_1994675 : Nat := 151737336964013119790987

theorem tailTrace_1994675 : CollatzResearch.WordTrace tailWord_1994675 prefixEnd_1994675 151737336964013119790987 := by
  unfold tailWord_1994675
  simp only [CollatzResearch.WordTrace]
  refine ⟨72751774048640613213513479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48501182699093742142342319 72751774048640613213513479)
  ·
    refine ⟨109127661072960919820270219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72751774048640613213513479 109127661072960919820270219)
    ·
      refine ⟨163691491609441379730405329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109127661072960919820270219 163691491609441379730405329)
      ·
        refine ⟨122768618707081034797803997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163691491609441379730405329 122768618707081034797803997)
        ·
          refine ⟨46038232015155388049176499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122768618707081034797803997 46038232015155388049176499)
          ·
            refine ⟨69057348022733082073764749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46038232015155388049176499 69057348022733082073764749)
            ·
              refine ⟨25896505508524905777661781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69057348022733082073764749 25896505508524905777661781)
              ·
                refine ⟨151737336964013119790987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25896505508524905777661781 151737336964013119790987)
                ·
                  rfl

theorem cell21_1994675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_1994675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994675 prefixEnd_1994675 := by exact prefixLift 1994675
  have htrace : WordTrace (prefixWord ++ tailWord_1994675) baseStart_1994675 baseEnd_1994675 := by
    simpa [prefixWord, tailWord_1994675, baseEnd_1994675] using wordTrace_append hprefix tailTrace_1994675
  have hstable : (prefixWord ++ tailWord_1994675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994675).length < 2 ^ (prefixWord ++ tailWord_1994675).sum := by decide
  have hdescent : baseEnd_1994675 < baseStart_1994675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994709 : List Nat := [1, 3, 2, 3, 2, 3, 1, 6]
def baseStart_1994709 : Nat := 118140960795 + 1994709 * 2 ^ 59
def prefixEnd_1994709 : Nat := 4983230072969 + 3 ^ 40 * 1994709 * 2
def baseEnd_1994709 : Nat := 151739923385087618602075

theorem tailTrace_1994709 : CollatzResearch.WordTrace tailWord_1994709 prefixEnd_1994709 151739923385087618602075 := by
  unfold tailWord_1994709
  simp only [CollatzResearch.WordTrace]
  refine ⟨72753014130517437020251181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48502009420344958013500787 72753014130517437020251181)
  ·
    refine ⟨27282380298944038882594193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72753014130517437020251181 27282380298944038882594193)
    ·
      refine ⟨20461785224208029161945645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27282380298944038882594193 20461785224208029161945645)
      ·
        refine ⟨7673169459078010935729617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20461785224208029161945645 7673169459078010935729617)
        ·
          refine ⟨5754877094308508201797213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7673169459078010935729617 5754877094308508201797213)
          ·
            refine ⟨2158078910365690575673955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5754877094308508201797213 2158078910365690575673955)
            ·
              refine ⟨3237118365548535863510933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158078910365690575673955 3237118365548535863510933)
              ·
                refine ⟨151739923385087618602075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3237118365548535863510933 151739923385087618602075)
                ·
                  rfl

theorem cell21_1994709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 6].length) (baseStart_1994709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994709 prefixEnd_1994709 := by exact prefixLift 1994709
  have htrace : WordTrace (prefixWord ++ tailWord_1994709) baseStart_1994709 baseEnd_1994709 := by
    simpa [prefixWord, tailWord_1994709, baseEnd_1994709] using wordTrace_append hprefix tailTrace_1994709
  have hstable : (prefixWord ++ tailWord_1994709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994709).length < 2 ^ (prefixWord ++ tailWord_1994709).sum := by decide
  have hdescent : baseEnd_1994709 < baseStart_1994709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994723 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 5]
def baseStart_1994723 : Nat := 118140960795 + 1994723 * 2 ^ 59
def prefixEnd_1994723 : Nat := 4983230072969 + 3 ^ 40 * 1994723 * 2
def baseEnd_1994723 : Nat := 455222965146001942572863

theorem tailTrace_1994723 : CollatzResearch.WordTrace tailWord_1994723 prefixEnd_1994723 455222965146001942572863 := by
  unfold tailWord_1994723
  simp only [CollatzResearch.WordTrace]
  refine ⟨72753524752466717411260823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48502349834977811607507215 72753524752466717411260823)
  ·
    refine ⟨109130287128700076116891235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72753524752466717411260823 109130287128700076116891235)
    ·
      refine ⟨163695430693050114175336853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109130287128700076116891235 163695430693050114175336853)
      ·
        refine ⟨7673223313736724101968915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 163695430693050114175336853 7673223313736724101968915)
        ·
          refine ⟨11509834970605086152953373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673223313736724101968915 11509834970605086152953373)
          ·
            refine ⟨4316188113976907307357515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11509834970605086152953373 4316188113976907307357515)
            ·
              refine ⟨6474282170965360961036273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316188113976907307357515 6474282170965360961036273)
              ·
                refine ⟨4855711628224020720777205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474282170965360961036273 4855711628224020720777205)
                ·
                  refine ⟨455222965146001942572863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4855711628224020720777205 455222965146001942572863)
                  ·
                    rfl

theorem cell21_1994723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_1994723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994723 prefixEnd_1994723 := by exact prefixLift 1994723
  have htrace : WordTrace (prefixWord ++ tailWord_1994723) baseStart_1994723 baseEnd_1994723 := by
    simpa [prefixWord, tailWord_1994723, baseEnd_1994723] using wordTrace_append hprefix tailTrace_1994723
  have hstable : (prefixWord ++ tailWord_1994723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994723).length < 2 ^ (prefixWord ++ tailWord_1994723).sum := by decide
  have hdescent : baseEnd_1994723 < baseStart_1994723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994791 : List Nat := [1, 1, 7, 1, 3, 1, 1, 3, 3]
def baseStart_1994791 : Nat := 118140960795 + 1994791 * 2 ^ 59
def prefixEnd_1994791 : Nat := 4983230072969 + 3 ^ 40 * 1994791 * 2
def baseEnd_1994791 : Nat := 455238483672448935439391

theorem tailTrace_1994791 : CollatzResearch.WordTrace tailWord_1994791 prefixEnd_1994791 455238483672448935439391 := by
  unfold tailWord_1994791
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756004916220365024736227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48504003277480243349824151 72756004916220365024736227)
  ·
    refine ⟨109134007374330547537104341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72756004916220365024736227 109134007374330547537104341)
    ·
      refine ⟨2557828297835872207900883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 109134007374330547537104341 2557828297835872207900883)
      ·
        refine ⟨3836742446753808311851325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557828297835872207900883 3836742446753808311851325)
        ·
          refine ⟨1438778417532678116944247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3836742446753808311851325 1438778417532678116944247)
          ·
            refine ⟨2158167626299017175416371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438778417532678116944247 2158167626299017175416371)
            ·
              refine ⟨3237251439448525763124557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158167626299017175416371 3237251439448525763124557)
              ·
                refine ⟨1213969289793197161171709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237251439448525763124557 1213969289793197161171709)
                ·
                  refine ⟨455238483672448935439391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213969289793197161171709 455238483672448935439391)
                  ·
                    rfl

theorem cell21_1994791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 3].length) (baseStart_1994791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994791 prefixEnd_1994791 := by exact prefixLift 1994791
  have htrace : WordTrace (prefixWord ++ tailWord_1994791) baseStart_1994791 baseEnd_1994791 := by
    simpa [prefixWord, tailWord_1994791, baseEnd_1994791] using wordTrace_append hprefix tailTrace_1994791
  have hstable : (prefixWord ++ tailWord_1994791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994791).length < 2 ^ (prefixWord ++ tailWord_1994791).sum := by decide
  have hdescent : baseEnd_1994791 < baseStart_1994791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994799 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 3]
def baseStart_1994799 : Nat := 118140960795 + 1994799 * 2 ^ 59
def prefixEnd_1994799 : Nat := 4983230072969 + 3 ^ 40 * 1994799 * 2
def baseEnd_1994799 : Nat := 455240309381442699306041

theorem tailTrace_1994799 : CollatzResearch.WordTrace tailWord_1994799 prefixEnd_1994799 455240309381442699306041 := by
  unfold tailWord_1994799
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756296700191382391027451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48504197800127588260684967 72756296700191382391027451)
  ·
    refine ⟨109134445050287073586541177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72756296700191382391027451 109134445050287073586541177)
    ·
      refine ⟨81850833787715305189905883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109134445050287073586541177 81850833787715305189905883)
      ·
        refine ⟨122776250681572957784858825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81850833787715305189905883 122776250681572957784858825)
        ·
          refine ⟨92082188011179718338644119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122776250681572957784858825 92082188011179718338644119)
          ·
            refine ⟨138123282016769577507966179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92082188011179718338644119 138123282016769577507966179)
            ·
              refine ⟨207184923025154366261949269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138123282016769577507966179 207184923025154366261949269)
              ·
                refine ⟨1213974158350513864816109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 207184923025154366261949269 1213974158350513864816109)
                ·
                  refine ⟨455240309381442699306041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213974158350513864816109 455240309381442699306041)
                  ·
                    rfl

theorem cell21_1994799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 3].length) (baseStart_1994799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994799 prefixEnd_1994799 := by exact prefixLift 1994799
  have htrace : WordTrace (prefixWord ++ tailWord_1994799) baseStart_1994799 baseEnd_1994799 := by
    simpa [prefixWord, tailWord_1994799, baseEnd_1994799] using wordTrace_append hprefix tailTrace_1994799
  have hstable : (prefixWord ++ tailWord_1994799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994799).length < 2 ^ (prefixWord ++ tailWord_1994799).sum := by decide
  have hdescent : baseEnd_1994799 < baseStart_1994799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994813 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1994813 : Nat := 118140960795 + 1994813 * 2 ^ 59
def prefixEnd_1994813 : Nat := 4983230072969 + 3 ^ 40 * 1994813 * 2
def baseEnd_1994813 : Nat := 455243504372181786072679

theorem tailTrace_1994813 : CollatzResearch.WordTrace tailWord_1994813 prefixEnd_1994813 455243504372181786072679 := by
  unfold tailWord_1994813
  simp only [CollatzResearch.WordTrace]
  refine ⟨72756807322140662782037093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48504538214760441854691395 72756807322140662782037093)
  ·
    refine ⟨13641901372901374271631955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72756807322140662782037093 13641901372901374271631955)
    ·
      refine ⟨20462852059352061407447933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13641901372901374271631955 20462852059352061407447933)
      ·
        refine ⟨7673569522257023027792975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20462852059352061407447933 7673569522257023027792975)
        ·
          refine ⟨11510354283385534541689463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673569522257023027792975 11510354283385534541689463)
          ·
            refine ⟨17265531425078301812534195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11510354283385534541689463 17265531425078301812534195)
            ·
              refine ⟨25898297137617452718801293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17265531425078301812534195 25898297137617452718801293)
              ·
                refine ⟨9711861426606544769550485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25898297137617452718801293 9711861426606544769550485)
                ·
                  refine ⟨455243504372181786072679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9711861426606544769550485 455243504372181786072679)
                  ·
                    rfl

theorem cell21_1994813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1994813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994813 prefixEnd_1994813 := by exact prefixLift 1994813
  have htrace : WordTrace (prefixWord ++ tailWord_1994813) baseStart_1994813 baseEnd_1994813 := by
    simpa [prefixWord, tailWord_1994813, baseEnd_1994813] using wordTrace_append hprefix tailTrace_1994813
  have hstable : (prefixWord ++ tailWord_1994813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994813).length < 2 ^ (prefixWord ++ tailWord_1994813).sum := by decide
  have hdescent : baseEnd_1994813 < baseStart_1994813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994830 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1994830 : Nat := 118140960795 + 1994830 * 2 ^ 59
def prefixEnd_1994830 : Nat := 4983230072969 + 3 ^ 40 * 1994830 * 2
def baseEnd_1994830 : Nat := 455247384003793534289311

theorem tailTrace_1994830 : CollatzResearch.WordTrace tailWord_1994830 prefixEnd_1994830 455247384003793534289311 := by
  unfold tailWord_1994830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094678420384884335675743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48504951575386049790270629 9094678420384884335675743)
  ·
    refine ⟨13642017630577326503513615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9094678420384884335675743 13642017630577326503513615)
    ·
      refine ⟨20463026445865989755270423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13642017630577326503513615 20463026445865989755270423)
      ·
        refine ⟨30694539668798984632905635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20463026445865989755270423 30694539668798984632905635)
        ·
          refine ⟨46041809503198476949358453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30694539668798984632905635 46041809503198476949358453)
          ·
            refine ⟨4316419640924857214002355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46041809503198476949358453 4316419640924857214002355)
            ·
              refine ⟨6474629461387285821003533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316419640924857214002355 6474629461387285821003533)
              ·
                refine ⟨2427986048020232182876325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6474629461387285821003533 2427986048020232182876325)
                ·
                  refine ⟨455247384003793534289311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2427986048020232182876325 455247384003793534289311)
                  ·
                    rfl

theorem cell21_1994830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1994830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994830 prefixEnd_1994830 := by exact prefixLift 1994830
  have htrace : WordTrace (prefixWord ++ tailWord_1994830) baseStart_1994830 baseEnd_1994830 := by
    simpa [prefixWord, tailWord_1994830, baseEnd_1994830] using wordTrace_append hprefix tailTrace_1994830
  have hstable : (prefixWord ++ tailWord_1994830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994830).length < 2 ^ (prefixWord ++ tailWord_1994830).sum := by decide
  have hdescent : baseEnd_1994830 < baseStart_1994830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994844 : List Nat := [2, 2, 4, 1, 1, 2, 2, 7]
def baseStart_1994844 : Nat := 118140960795 + 1994844 * 2 ^ 59
def prefixEnd_1994844 : Nat := 4983230072969 + 3 ^ 40 * 1994844 * 2
def baseEnd_1994844 : Nat := 151750192998177540351983

theorem tailTrace_1994844 : CollatzResearch.WordTrace tailWord_1994844 prefixEnd_1994844 151750192998177540351983 := by
  unfold tailWord_1994844
  simp only [CollatzResearch.WordTrace]
  refine ⟨36378968992514177538207793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48505291990018903384277057 36378968992514177538207793)
  ·
    refine ⟨27284226744385633153655845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36378968992514177538207793 27284226744385633153655845)
    ·
      refine ⟨5115792514572306216310471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27284226744385633153655845 5115792514572306216310471)
      ·
        refine ⟨7673688771858459324465707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115792514572306216310471 7673688771858459324465707)
        ·
          refine ⟨11510533157787688986698561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7673688771858459324465707 11510533157787688986698561)
          ·
            refine ⟨8632899868340766740023921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11510533157787688986698561 8632899868340766740023921)
            ·
              refine ⟨6474674901255575055017941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8632899868340766740023921 6474674901255575055017941)
              ·
                refine ⟨151750192998177540351983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6474674901255575055017941 151750192998177540351983)
                ·
                  rfl

theorem cell21_1994844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_1994844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994844 prefixEnd_1994844 := by exact prefixLift 1994844
  have htrace : WordTrace (prefixWord ++ tailWord_1994844) baseStart_1994844 baseEnd_1994844 := by
    simpa [prefixWord, tailWord_1994844, baseEnd_1994844] using wordTrace_append hprefix tailTrace_1994844
  have hstable : (prefixWord ++ tailWord_1994844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994844).length < 2 ^ (prefixWord ++ tailWord_1994844).sum := by decide
  have hdescent : baseEnd_1994844 < baseStart_1994844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994889 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 4]
def baseStart_1994889 : Nat := 118140960795 + 1994889 * 2 ^ 59
def prefixEnd_1994889 : Nat := 4983230072969 + 3 ^ 40 * 1994889 * 2
def baseEnd_1994889 : Nat := 455260848607622542805857

theorem tailTrace_1994889 : CollatzResearch.WordTrace tailWord_1994889 prefixEnd_1994889 455260848607622542805857 := by
  unfold tailWord_1994889
  simp only [CollatzResearch.WordTrace]
  refine ⟨72759579269865327761803721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48506386179910218507869147 72759579269865327761803721)
  ·
    refine ⟨54569684452398995821352791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72759579269865327761803721 54569684452398995821352791)
    ·
      refine ⟨81854526678598493732029187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54569684452398995821352791 81854526678598493732029187)
      ·
        refine ⟨122781790017897740598043781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81854526678598493732029187 122781790017897740598043781)
        ·
          refine ⟨23021585628355826362133209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122781790017897740598043781 23021585628355826362133209)
          ·
            refine ⟨17266189221266869771599907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23021585628355826362133209 17266189221266869771599907)
            ·
              refine ⟨25899283831900304657399861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17266189221266869771599907 25899283831900304657399861)
              ·
                refine ⟨2428057859240653561631237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25899283831900304657399861 2428057859240653561631237)
                ·
                  refine ⟨455260848607622542805857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428057859240653561631237 455260848607622542805857)
                  ·
                    rfl

theorem cell21_1994889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_1994889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994889 prefixEnd_1994889 := by exact prefixLift 1994889
  have htrace : WordTrace (prefixWord ++ tailWord_1994889) baseStart_1994889 baseEnd_1994889 := by
    simpa [prefixWord, tailWord_1994889, baseEnd_1994889] using wordTrace_append hprefix tailTrace_1994889
  have hstable : (prefixWord ++ tailWord_1994889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994889).length < 2 ^ (prefixWord ++ tailWord_1994889).sum := by decide
  have hdescent : baseEnd_1994889 < baseStart_1994889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1994968 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_1994968 : Nat := 118140960795 + 1994968 * 2 ^ 59
def prefixEnd_1994968 : Nat := 4983230072969 + 3 ^ 40 * 1994968 * 2
def baseEnd_1994968 : Nat := 455278877483935960989029

theorem tailTrace_1994968 : CollatzResearch.WordTrace tailWord_1994968 prefixEnd_1994968 455278877483935960989029 := by
  unfold tailWord_1994968
  simp only [CollatzResearch.WordTrace]
  refine ⟨36381230318289562126964779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48508307091052749502619705 36381230318289562126964779)
  ·
    refine ⟨54571845477434343190447169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36381230318289562126964779 54571845477434343190447169)
    ·
      refine ⟨40928884108075757392835377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54571845477434343190447169 40928884108075757392835377)
      ·
        refine ⟨30696663081056818044626533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40928884108075757392835377 30696663081056818044626533)
        ·
          refine ⟨5755624327698153383367475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30696663081056818044626533 5755624327698153383367475)
          ·
            refine ⟨8633436491547230075051213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755624327698153383367475 8633436491547230075051213)
            ·
              refine ⟨3237538684330211278144205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8633436491547230075051213 3237538684330211278144205)
              ·
                refine ⟨1214077006623829229304077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237538684330211278144205 1214077006623829229304077)
                ·
                  refine ⟨455278877483935960989029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214077006623829229304077 455278877483935960989029)
                  ·
                    rfl

theorem cell21_1994968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_1994968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1994968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1994968 prefixEnd_1994968 := by exact prefixLift 1994968
  have htrace : WordTrace (prefixWord ++ tailWord_1994968) baseStart_1994968 baseEnd_1994968 := by
    simpa [prefixWord, tailWord_1994968, baseEnd_1994968] using wordTrace_append hprefix tailTrace_1994968
  have hstable : (prefixWord ++ tailWord_1994968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1994968).length < 2 ^ (prefixWord ++ tailWord_1994968).sum := by decide
  have hdescent : baseEnd_1994968 < baseStart_1994968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1994968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995041 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 4]
def baseStart_1995041 : Nat := 118140960795 + 1995041 * 2 ^ 59
def prefixEnd_1995041 : Nat := 4983230072969 + 3 ^ 40 * 1995041 * 2
def baseEnd_1995041 : Nat := 455295537078504056272213

theorem tailTrace_1995041 : CollatzResearch.WordTrace tailWord_1995041 prefixEnd_1995041 455295537078504056272213 := by
  unfold tailWord_1995041
  simp only [CollatzResearch.WordTrace]
  refine ⟨72765123165314657721336977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48510082110209771814224651 72765123165314657721336977)
  ·
    refine ⟨54573842373985993291002733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72765123165314657721336977 54573842373985993291002733)
    ·
      refine ⟨20465190890244747484126025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54573842373985993291002733 20465190890244747484126025)
      ·
        refine ⟨15348893167683560613094519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20465190890244747484126025 15348893167683560613094519)
        ·
          refine ⟨23023339751525340919641779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348893167683560613094519 23023339751525340919641779)
          ·
            refine ⟨34535009627288011379462669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23023339751525340919641779 34535009627288011379462669)
            ·
              refine ⟨12950628610233004267298501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34535009627288011379462669 12950628610233004267298501)
              ·
                refine ⟨2428242864418688300118469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12950628610233004267298501 2428242864418688300118469)
                ·
                  refine ⟨455295537078504056272213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428242864418688300118469 455295537078504056272213)
                  ·
                    rfl

theorem cell21_1995041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_1995041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995041 prefixEnd_1995041 := by exact prefixLift 1995041
  have htrace : WordTrace (prefixWord ++ tailWord_1995041) baseStart_1995041 baseEnd_1995041 := by
    simpa [prefixWord, tailWord_1995041, baseEnd_1995041] using wordTrace_append hprefix tailTrace_1995041
  have hstable : (prefixWord ++ tailWord_1995041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995041).length < 2 ^ (prefixWord ++ tailWord_1995041).sum := by decide
  have hdescent : baseEnd_1995041 < baseStart_1995041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995044 : List Nat := [2, 3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_1995044 : Nat := 118140960795 + 1995044 * 2 ^ 59
def prefixEnd_1995044 : Nat := 4983230072969 + 3 ^ 40 * 1995044 * 2
def baseEnd_1995044 : Nat := 455296221719376717722207

theorem tailTrace_1995044 : CollatzResearch.WordTrace tailWord_1995044 prefixEnd_1995044 455296221719376717722207 := by
  unfold tailWord_1995044
  simp only [CollatzResearch.WordTrace]
  refine ⟨36382616292151894616848093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48510155056202526155797457 36382616292151894616848093)
  ·
    refine ⟨13643481109556960481318035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36382616292151894616848093 13643481109556960481318035)
    ·
      refine ⟨20465221664335440721977053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13643481109556960481318035 20465221664335440721977053)
      ·
        refine ⟨7674458124125790270741395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20465221664335440721977053 7674458124125790270741395)
        ·
          refine ⟨11511687186188685406112093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674458124125790270741395 11511687186188685406112093)
          ·
            refine ⟨4316882694820757027292035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11511687186188685406112093 4316882694820757027292035)
            ·
              refine ⟨6475324042231135540938053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4316882694820757027292035 6475324042231135540938053)
              ·
                refine ⟨1214123257918337913925885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6475324042231135540938053 1214123257918337913925885)
                ·
                  refine ⟨455296221719376717722207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214123257918337913925885 455296221719376717722207)
                  ·
                    rfl

theorem cell21_1995044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_1995044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995044 prefixEnd_1995044 := by exact prefixLift 1995044
  have htrace : WordTrace (prefixWord ++ tailWord_1995044) baseStart_1995044 baseEnd_1995044 := by
    simpa [prefixWord, tailWord_1995044, baseEnd_1995044] using wordTrace_append hprefix tailTrace_1995044
  have hstable : (prefixWord ++ tailWord_1995044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995044).length < 2 ^ (prefixWord ++ tailWord_1995044).sum := by decide
  have hdescent : baseEnd_1995044 < baseStart_1995044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995047 : List Nat := [1, 1, 8, 1, 1, 2, 1, 6]
def baseStart_1995047 : Nat := 118140960795 + 1995047 * 2 ^ 59
def prefixEnd_1995047 : Nat := 4983230072969 + 3 ^ 40 * 1995047 * 2
def baseEnd_1995047 : Nat := 151765635453416459724067

theorem tailTrace_1995047 : CollatzResearch.WordTrace tailWord_1995047 prefixEnd_1995047 151765635453416459724067 := by
  unfold tailWord_1995047
  simp only [CollatzResearch.WordTrace]
  refine ⟨72765342003292920746055395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48510228002195280497370263 72765342003292920746055395)
  ·
    refine ⟨109148013004939381119083093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72765342003292920746055395 109148013004939381119083093)
    ·
      refine ⟨1279078277401633372489255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 109148013004939381119083093 1279078277401633372489255)
      ·
        refine ⟨1918617416102450058733883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279078277401633372489255 1918617416102450058733883)
        ·
          refine ⟨2877926124153675088100825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918617416102450058733883 2877926124153675088100825)
          ·
            refine ⟨2158444593115256316075619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2877926124153675088100825 2158444593115256316075619)
            ·
              refine ⟨3237666889672884474113429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158444593115256316075619 3237666889672884474113429)
              ·
                refine ⟨151765635453416459724067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3237666889672884474113429 151765635453416459724067)
                ·
                  rfl

theorem cell21_1995047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 6].length) (baseStart_1995047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995047 prefixEnd_1995047 := by exact prefixLift 1995047
  have htrace : WordTrace (prefixWord ++ tailWord_1995047) baseStart_1995047 baseEnd_1995047 := by
    simpa [prefixWord, tailWord_1995047, baseEnd_1995047] using wordTrace_append hprefix tailTrace_1995047
  have hstable : (prefixWord ++ tailWord_1995047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995047).length < 2 ^ (prefixWord ++ tailWord_1995047).sum := by decide
  have hdescent : baseEnd_1995047 < baseStart_1995047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995055 : List Nat := [1, 1, 2, 1, 2, 1, 7, 6]
def baseStart_1995055 : Nat := 118140960795 + 1995055 * 2 ^ 59
def prefixEnd_1995055 : Nat := 4983230072969 + 3 ^ 40 * 1995055 * 2
def baseEnd_1995055 : Nat := 151766244023081047679617

theorem tailTrace_1995055 : CollatzResearch.WordTrace tailWord_1995055 prefixEnd_1995055 151766244023081047679617 := by
  unfold tailWord_1995055
  simp only [CollatzResearch.WordTrace]
  refine ⟨72765633787263938112346619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48510422524842625408231079 72765633787263938112346619)
  ·
    refine ⟨109148450680895907168519929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72765633787263938112346619 109148450680895907168519929)
    ·
      refine ⟨81861338010671930376389947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109148450680895907168519929 81861338010671930376389947)
      ·
        refine ⟨122792007016007895564584921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81861338010671930376389947 122792007016007895564584921)
        ·
          refine ⟨92094005262005921673438691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122792007016007895564584921 92094005262005921673438691)
          ·
            refine ⟨138141007893008882510158037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92094005262005921673438691 138141007893008882510158037)
            ·
              refine ⟨3237679872492395683831829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138141007893008882510158037 3237679872492395683831829)
              ·
                refine ⟨151766244023081047679617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3237679872492395683831829 151766244023081047679617)
                ·
                  rfl

theorem cell21_1995055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_1995055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995055 prefixEnd_1995055 := by exact prefixLift 1995055
  have htrace : WordTrace (prefixWord ++ tailWord_1995055) baseStart_1995055 baseEnd_1995055 := by
    simpa [prefixWord, tailWord_1995055, baseEnd_1995055] using wordTrace_append hprefix tailTrace_1995055
  have hstable : (prefixWord ++ tailWord_1995055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995055).length < 2 ^ (prefixWord ++ tailWord_1995055).sum := by decide
  have hdescent : baseEnd_1995055 < baseStart_1995055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995103 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 3]
def baseStart_1995103 : Nat := 118140960795 + 1995103 * 2 ^ 59
def prefixEnd_1995103 : Nat := 4983230072969 + 3 ^ 40 * 1995103 * 2
def baseEnd_1995103 : Nat := 455309686323205726238753

theorem tailTrace_1995103 : CollatzResearch.WordTrace tailWord_1995103 prefixEnd_1995103 455309686323205726238753 := by
  unfold tailWord_1995103
  simp only [CollatzResearch.WordTrace]
  refine ⟨72767384491090042310093963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48511589660726694873395975 72767384491090042310093963)
  ·
    refine ⟨109151076736635063465140945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72767384491090042310093963 109151076736635063465140945)
    ·
      refine ⟨81863307552476297598855709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109151076736635063465140945 81863307552476297598855709)
      ·
        refine ⟨30698740332178611599570891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81863307552476297598855709 30698740332178611599570891)
        ·
          refine ⟨46048110498267917399356337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30698740332178611599570891 46048110498267917399356337)
          ·
            refine ⟨34536082873700938049517253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46048110498267917399356337 34536082873700938049517253)
            ·
              refine ⟨6475515538818925884284485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34536082873700938049517253 6475515538818925884284485)
              ·
                refine ⟨1214159163528548603303341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6475515538818925884284485 1214159163528548603303341)
                ·
                  refine ⟨455309686323205726238753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214159163528548603303341 455309686323205726238753)
                  ·
                    rfl

theorem cell21_1995103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 3].length) (baseStart_1995103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995103 prefixEnd_1995103 := by exact prefixLift 1995103
  have htrace : WordTrace (prefixWord ++ tailWord_1995103) baseStart_1995103 baseEnd_1995103 := by
    simpa [prefixWord, tailWord_1995103, baseEnd_1995103] using wordTrace_append hprefix tailTrace_1995103
  have hstable : (prefixWord ++ tailWord_1995103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995103).length < 2 ^ (prefixWord ++ tailWord_1995103).sum := by decide
  have hdescent : baseEnd_1995103 < baseStart_1995103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995131 : List Nat := [1, 1, 1, 1, 1, 8, 1, 7]
def baseStart_1995131 : Nat := 118140960795 + 1995131 * 2 ^ 59
def prefixEnd_1995131 : Nat := 4983230072969 + 3 ^ 40 * 1995131 * 2
def baseEnd_1995131 : Nat := 151772025434894633257343

theorem tailTrace_1995131 : CollatzResearch.WordTrace tailWord_1995131 prefixEnd_1995131 151772025434894633257343 := by
  unfold tailWord_1995131
  simp only [CollatzResearch.WordTrace]
  refine ⟨72768405734988603092113247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48512270489992402061408831 72768405734988603092113247)
  ·
    refine ⟨109152608602482904638169871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72768405734988603092113247 109152608602482904638169871)
    ·
      refine ⟨163728912903724356957254807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109152608602482904638169871 163728912903724356957254807)
      ·
        refine ⟨245593369355586535435882211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163728912903724356957254807 245593369355586535435882211)
        ·
          refine ⟨368390054033379803153823317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245593369355586535435882211 368390054033379803153823317)
          ·
            refine ⟨4317070945703669568208867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 368390054033379803153823317 4317070945703669568208867)
            ·
              refine ⟨6475606418555504352313301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317070945703669568208867 6475606418555504352313301)
              ·
                refine ⟨151772025434894633257343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6475606418555504352313301 151772025434894633257343)
                ·
                  rfl

theorem cell21_1995131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_1995131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995131 prefixEnd_1995131 := by exact prefixLift 1995131
  have htrace : WordTrace (prefixWord ++ tailWord_1995131) baseStart_1995131 baseEnd_1995131 := by
    simpa [prefixWord, tailWord_1995131, baseEnd_1995131] using wordTrace_append hprefix tailTrace_1995131
  have hstable : (prefixWord ++ tailWord_1995131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995131).length < 2 ^ (prefixWord ++ tailWord_1995131).sum := by decide
  have hdescent : baseEnd_1995131 < baseStart_1995131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995137 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 3]
def baseStart_1995137 : Nat := 118140960795 + 1995137 * 2 ^ 59
def prefixEnd_1995137 : Nat := 4983230072969 + 3 ^ 40 * 1995137 * 2
def baseEnd_1995137 : Nat := 455317445586429222672017

theorem tailTrace_1995137 : CollatzResearch.WordTrace tailWord_1995137 prefixEnd_1995137 455317445586429222672017 := by
  unfold tailWord_1995137
  simp only [CollatzResearch.WordTrace]
  refine ⟨72768624572966866116831665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48512416381977910744554443 72768624572966866116831665)
  ·
    refine ⟨54576468429725149587623749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72768624572966866116831665 54576468429725149587623749)
    ·
      refine ⟨10233087830573465547679453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54576468429725149587623749 10233087830573465547679453)
      ·
        refine ⟨3837407936465049580379795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10233087830573465547679453 3837407936465049580379795)
        ·
          refine ⟨5756111904697574370569693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837407936465049580379795 5756111904697574370569693)
          ·
            refine ⟨2158541964261590388963635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5756111904697574370569693 2158541964261590388963635)
            ·
              refine ⟨3237812946392385583445453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158541964261590388963635 3237812946392385583445453)
              ·
                refine ⟨1214179854897144593792045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237812946392385583445453 1214179854897144593792045)
                ·
                  refine ⟨455317445586429222672017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214179854897144593792045 455317445586429222672017)
                  ·
                    rfl

theorem cell21_1995137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_1995137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995137 prefixEnd_1995137 := by exact prefixLift 1995137
  have htrace : WordTrace (prefixWord ++ tailWord_1995137) baseStart_1995137 baseEnd_1995137 := by
    simpa [prefixWord, tailWord_1995137, baseEnd_1995137] using wordTrace_append hprefix tailTrace_1995137
  have hstable : (prefixWord ++ tailWord_1995137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995137).length < 2 ^ (prefixWord ++ tailWord_1995137).sum := by decide
  have hdescent : baseEnd_1995137 < baseStart_1995137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995269 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1995269 : Nat := 118140960795 + 1995269 * 2 ^ 59
def prefixEnd_1995269 : Nat := 4983230072969 + 3 ^ 40 * 1995269 * 2
def baseEnd_1995269 : Nat := 455347569784826326471747

theorem tailTrace_1995269 : CollatzResearch.WordTrace tailWord_1995269 prefixEnd_1995269 455347569784826326471747 := by
  unfold tailWord_1995269
  simp only [CollatzResearch.WordTrace]
  refine ⟨72773439008488652660636861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48515626005659101773757907 72773439008488652660636861)
  ·
    refine ⟨27290039628183244747738823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72773439008488652660636861 27290039628183244747738823)
    ·
      refine ⟨40935059442274867121608235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27290039628183244747738823 40935059442274867121608235)
      ·
        refine ⟨61402589163412300682412353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40935059442274867121608235 61402589163412300682412353)
        ·
          refine ⟨46051941872559225511809265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61402589163412300682412353 46051941872559225511809265)
          ·
            refine ⟨34538956404419419133856949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46051941872559225511809265 34538956404419419133856949)
            ·
              refine ⟨3238027162914320543799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34538956404419419133856949 3238027162914320543799089)
              ·
                refine ⟨2428520372185740407849317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3238027162914320543799089 2428520372185740407849317)
                ·
                  refine ⟨455347569784826326471747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428520372185740407849317 455347569784826326471747)
                  ·
                    rfl

theorem cell21_1995269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1995269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995269 prefixEnd_1995269 := by exact prefixLift 1995269
  have htrace : WordTrace (prefixWord ++ tailWord_1995269) baseStart_1995269 baseEnd_1995269 := by
    simpa [prefixWord, tailWord_1995269, baseEnd_1995269] using wordTrace_append hprefix tailTrace_1995269
  have hstable : (prefixWord ++ tailWord_1995269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995269).length < 2 ^ (prefixWord ++ tailWord_1995269).sum := by decide
  have hdescent : baseEnd_1995269 < baseStart_1995269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995328 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_1995328 : Nat := 118140960795 + 1995328 * 2 ^ 59
def prefixEnd_1995328 : Nat := 4983230072969 + 3 ^ 40 * 1995328 * 2
def baseEnd_1995328 : Nat := 455361034388655334988293

theorem tailTrace_1995328 : CollatzResearch.WordTrace tailWord_1995328 prefixEnd_1995328 455361034388655334988293 := by
  unfold tailWord_1995328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36387795457637452868517319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48517060610183270491356425 36387795457637452868517319)
  ·
    refine ⟨54581693186456179302775979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36387795457637452868517319 54581693186456179302775979)
    ·
      refine ⟨81872539779684268954163969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54581693186456179302775979 81872539779684268954163969)
      ·
        refine ⟨61404404834763201715622977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81872539779684268954163969 61404404834763201715622977)
        ·
          refine ⟨46053303626072401286717233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61404404834763201715622977 46053303626072401286717233)
          ·
            refine ⟨34539977719554300965037925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46053303626072401286717233 34539977719554300965037925)
            ·
              refine ⟨6476245822416431430944611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34539977719554300965037925 6476245822416431430944611)
              ·
                refine ⟨9714368733624647146416917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476245822416431430944611 9714368733624647146416917)
                ·
                  refine ⟨455361034388655334988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9714368733624647146416917 455361034388655334988293)
                  ·
                    rfl

theorem cell21_1995328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_1995328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995328 prefixEnd_1995328 := by exact prefixLift 1995328
  have htrace : WordTrace (prefixWord ++ tailWord_1995328) baseStart_1995328 baseEnd_1995328 := by
    simpa [prefixWord, tailWord_1995328, baseEnd_1995328] using wordTrace_append hprefix tailTrace_1995328
  have hstable : (prefixWord ++ tailWord_1995328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995328).length < 2 ^ (prefixWord ++ tailWord_1995328).sum := by decide
  have hdescent : baseEnd_1995328 < baseStart_1995328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995345 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 4]
def baseStart_1995345 : Nat := 118140960795 + 1995345 * 2 ^ 59
def prefixEnd_1995345 : Nat := 4983230072969 + 3 ^ 40 * 1995345 * 2
def baseEnd_1995345 : Nat := 455364914020267083204925

theorem tailTrace_1995345 : CollatzResearch.WordTrace tailWord_1995345 prefixEnd_1995345 455364914020267083204925 := by
  unfold tailWord_1995345
  simp only [CollatzResearch.WordTrace]
  refine ⟨72776210956213317640403489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48517473970808878426935659 72776210956213317640403489)
  ·
    refine ⟨54582158217159988230302617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72776210956213317640403489 54582158217159988230302617)
    ·
      refine ⟨40936618662869991172726963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54582158217159988230302617 40936618662869991172726963)
      ·
        refine ⟨61404927994304986759090445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40936618662869991172726963 61404927994304986759090445)
        ·
          refine ⟨23026847997864370034658917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61404927994304986759090445 23026847997864370034658917)
          ·
            refine ⟨4317533999599569381498547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23026847997864370034658917 4317533999599569381498547)
            ·
              refine ⟨6476300999399354072247821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317533999599569381498547 6476300999399354072247821)
              ·
                refine ⟨2428612874774757777092933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6476300999399354072247821 2428612874774757777092933)
                ·
                  refine ⟨455364914020267083204925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428612874774757777092933 455364914020267083204925)
                  ·
                    rfl

theorem cell21_1995345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_1995345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995345 prefixEnd_1995345 := by exact prefixLift 1995345
  have htrace : WordTrace (prefixWord ++ tailWord_1995345) baseStart_1995345 baseEnd_1995345 := by
    simpa [prefixWord, tailWord_1995345, baseEnd_1995345] using wordTrace_append hprefix tailTrace_1995345
  have hstable : (prefixWord ++ tailWord_1995345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995345).length < 2 ^ (prefixWord ++ tailWord_1995345).sum := by decide
  have hdescent : baseEnd_1995345 < baseStart_1995345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995382 : List Nat := [5, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1995382 : Nat := 118140960795 + 1995382 * 2 ^ 59
def prefixEnd_1995382 : Nat := 4983230072969 + 3 ^ 40 * 1995382 * 2
def baseEnd_1995382 : Nat := 455373357924363241088183

theorem tailTrace_1995382 : CollatzResearch.WordTrace tailWord_1995382 prefixEnd_1995382 455373357924363241088183 := by
  unfold tailWord_1995382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548597528567454559968775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48518373638052848639666933 4548597528567454559968775)
  ·
    refine ⟨6822896292851181839953163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4548597528567454559968775 6822896292851181839953163)
    ·
      refine ⟨10234344439276772759929745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6822896292851181839953163 10234344439276772759929745)
      ·
        refine ⟨7675758329457579569947309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10234344439276772759929745 7675758329457579569947309)
        ·
          refine ⟨2878409373546592338730241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7675758329457579569947309 2878409373546592338730241)
          ·
            refine ⟨2158807030159944254047681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2878409373546592338730241 2158807030159944254047681)
            ·
              refine ⟨1619105272619958190535761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2158807030159944254047681 1619105272619958190535761)
              ·
                refine ⟨1214328954464968642901821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619105272619958190535761 1214328954464968642901821)
                ·
                  refine ⟨455373357924363241088183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214328954464968642901821 455373357924363241088183)
                  ·
                    rfl

theorem cell21_1995382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1995382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995382 prefixEnd_1995382 := by exact prefixLift 1995382
  have htrace : WordTrace (prefixWord ++ tailWord_1995382) baseStart_1995382 baseEnd_1995382 := by
    simpa [prefixWord, tailWord_1995382, baseEnd_1995382] using wordTrace_append hprefix tailTrace_1995382
  have hstable : (prefixWord ++ tailWord_1995382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995382).length < 2 ^ (prefixWord ++ tailWord_1995382).sum := by decide
  have hdescent : baseEnd_1995382 < baseStart_1995382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995424 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_1995424 : Nat := 118140960795 + 1995424 * 2 ^ 59
def prefixEnd_1995424 : Nat := 4983230072969 + 3 ^ 40 * 1995424 * 2
def baseEnd_1995424 : Nat := 455382942896580501388097

theorem tailTrace_1995424 : CollatzResearch.WordTrace tailWord_1995424 prefixEnd_1995424 455382942896580501388097 := by
  unfold tailWord_1995424
  simp only [CollatzResearch.WordTrace]
  refine ⟨36389546161463557066264663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48519394881951409421686217 36389546161463557066264663)
  ·
    refine ⟨54584319242195335599396995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36389546161463557066264663 54584319242195335599396995)
    ·
      refine ⟨81876478863293003399095493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54584319242195335599396995 81876478863293003399095493)
      ·
        refine ⟨15351839786867438137330405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81876478863293003399095493 15351839786867438137330405)
        ·
          refine ⟨2878469960037644650749451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15351839786867438137330405 2878469960037644650749451)
          ·
            refine ⟨4317704940056466976124177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878469960037644650749451 4317704940056466976124177)
            ·
              refine ⟨3238278705042350232093133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4317704940056466976124177 3238278705042350232093133)
              ·
                refine ⟨1214354514390881337034925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3238278705042350232093133 1214354514390881337034925)
                ·
                  refine ⟨455382942896580501388097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214354514390881337034925 455382942896580501388097)
                  ·
                    rfl

theorem cell21_1995424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_1995424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995424 prefixEnd_1995424 := by exact prefixLift 1995424
  have htrace : WordTrace (prefixWord ++ tailWord_1995424) baseStart_1995424 baseEnd_1995424 := by
    simpa [prefixWord, tailWord_1995424, baseEnd_1995424] using wordTrace_append hprefix tailTrace_1995424
  have hstable : (prefixWord ++ tailWord_1995424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995424).length < 2 ^ (prefixWord ++ tailWord_1995424).sum := by decide
  have hdescent : baseEnd_1995424 < baseStart_1995424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995438 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1995438 : Nat := 118140960795 + 1995438 * 2 ^ 59
def prefixEnd_1995438 : Nat := 4983230072969 + 3 ^ 40 * 1995438 * 2
def baseEnd_1995438 : Nat := 455386137887319588154735

theorem tailTrace_1995438 : CollatzResearch.WordTrace tailWord_1995438 prefixEnd_1995438 455386137887319588154735 := by
  unfold tailWord_1995438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097450368109549315442371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48519735296584263015692645 9097450368109549315442371)
  ·
    refine ⟨13646175552164323973163557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9097450368109549315442371 13646175552164323973163557)
    ·
      refine ⟨2558657916030810744968167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13646175552164323973163557 2558657916030810744968167)
      ·
        refine ⟨3837986874046216117452251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558657916030810744968167 3837986874046216117452251)
        ·
          refine ⟨5756980311069324176178377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3837986874046216117452251 5756980311069324176178377)
          ·
            refine ⟨4317735233301993132133783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5756980311069324176178377 4317735233301993132133783)
            ·
              refine ⟨6476602849952989698200675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317735233301993132133783 6476602849952989698200675)
              ·
                refine ⟨9714904274929484547301013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6476602849952989698200675 9714904274929484547301013)
                ·
                  refine ⟨455386137887319588154735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9714904274929484547301013 455386137887319588154735)
                  ·
                    rfl

theorem cell21_1995438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1995438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995438 prefixEnd_1995438 := by exact prefixLift 1995438
  have htrace : WordTrace (prefixWord ++ tailWord_1995438) baseStart_1995438 baseEnd_1995438 := by
    simpa [prefixWord, tailWord_1995438, baseEnd_1995438] using wordTrace_append hprefix tailTrace_1995438
  have hstable : (prefixWord ++ tailWord_1995438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995438).length < 2 ^ (prefixWord ++ tailWord_1995438).sum := by decide
  have hdescent : baseEnd_1995438 < baseStart_1995438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995466 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1995466 : Nat := 118140960795 + 1995466 * 2 ^ 59
def prefixEnd_1995466 : Nat := 4983230072969 + 3 ^ 40 * 1995466 * 2
def baseEnd_1995466 : Nat := 455392527868797761688011

theorem tailTrace_1995466 : CollatzResearch.WordTrace tailWord_1995466 prefixEnd_1995466 455392527868797761688011 := by
  unfold tailWord_1995466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18195156047193738826389563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48520416125849970203705501 18195156047193738826389563)
  ·
    refine ⟨27292734070790608239584345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18195156047193738826389563 27292734070790608239584345)
    ·
      refine ⟨20469550553092956179688259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27292734070790608239584345 20469550553092956179688259)
      ·
        refine ⟨30704325829639434269532389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20469550553092956179688259 30704325829639434269532389)
        ·
          refine ⟨5757061093057393925537323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30704325829639434269532389 5757061093057393925537323)
          ·
            refine ⟨8635591639586090888305985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757061093057393925537323 8635591639586090888305985)
            ·
              refine ⟨6476693729689568166229489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8635591639586090888305985 6476693729689568166229489)
              ·
                refine ⟨4857520297267176124672117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476693729689568166229489 4857520297267176124672117)
                ·
                  refine ⟨455392527868797761688011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4857520297267176124672117 455392527868797761688011)
                  ·
                    rfl

theorem cell21_1995466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1995466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995466 prefixEnd_1995466 := by exact prefixLift 1995466
  have htrace : WordTrace (prefixWord ++ tailWord_1995466) baseStart_1995466 baseEnd_1995466 := by
    simpa [prefixWord, tailWord_1995466, baseEnd_1995466] using wordTrace_append hprefix tailTrace_1995466
  have hstable : (prefixWord ++ tailWord_1995466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995466).length < 2 ^ (prefixWord ++ tailWord_1995466).sum := by decide
  have hdescent : baseEnd_1995466 < baseStart_1995466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995469 : List Nat := [1, 6, 2, 1, 2, 1, 1, 7]
def baseStart_1995469 : Nat := 118140960795 + 1995469 * 2 ^ 59
def prefixEnd_1995469 : Nat := 4983230072969 + 3 ^ 40 * 1995469 * 2
def baseEnd_1995469 : Nat := 151797737503223474379335

theorem tailTrace_1995469 : CollatzResearch.WordTrace tailWord_1995469 prefixEnd_1995469 151797737503223474379335 := by
  unfold tailWord_1995469
  simp only [CollatzResearch.WordTrace]
  refine ⟨72780733607764086817917461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48520489071842724545278307 72780733607764086817917461)
  ·
    refine ⟨3411596887863941569589881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72780733607764086817917461 3411596887863941569589881)
    ·
      refine ⟨2558697665897956177192411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3411596887863941569589881 2558697665897956177192411)
      ·
        refine ⟨3838046498846934265788617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558697665897956177192411 3838046498846934265788617)
        ·
          refine ⟨2878534874135200699341463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3838046498846934265788617 2878534874135200699341463)
          ·
            refine ⟨4317802311202801049012195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878534874135200699341463 4317802311202801049012195)
            ·
              refine ⟨6476703466804201573518293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317802311202801049012195 6476703466804201573518293)
              ·
                refine ⟨151797737503223474379335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6476703466804201573518293 151797737503223474379335)
                ·
                  rfl

theorem cell21_1995469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 7].length) (baseStart_1995469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995469 prefixEnd_1995469 := by exact prefixLift 1995469
  have htrace : WordTrace (prefixWord ++ tailWord_1995469) baseStart_1995469 baseEnd_1995469 := by
    simpa [prefixWord, tailWord_1995469, baseEnd_1995469] using wordTrace_append hprefix tailTrace_1995469
  have hstable : (prefixWord ++ tailWord_1995469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995469).length < 2 ^ (prefixWord ++ tailWord_1995469).sum := by decide
  have hdescent : baseEnd_1995469 < baseStart_1995469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995480 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_1995480 : Nat := 118140960795 + 1995480 * 2 ^ 59
def prefixEnd_1995480 : Nat := 4983230072969 + 3 ^ 40 * 1995480 * 2
def baseEnd_1995480 : Nat := 455395722859536848454649

theorem tailTrace_1995480 : CollatzResearch.WordTrace tailWord_1995480 prefixEnd_1995480 455395722859536848454649 := by
  unfold tailWord_1995480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36390567405362117848283947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48520756540482823797711929 36390567405362117848283947)
  ·
    refine ⟨54585851108043176772425921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36390567405362117848283947 54585851108043176772425921)
    ·
      refine ⟨40939388331032382579319441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54585851108043176772425921 40939388331032382579319441)
      ·
        refine ⟨30704541248274286934489581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40939388331032382579319441 30704541248274286934489581)
        ·
          refine ⟨11514202968102857600433593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30704541248274286934489581 11514202968102857600433593)
          ·
            refine ⟨8635652226077143200325195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11514202968102857600433593 8635652226077143200325195)
            ·
              refine ⟨12953478339115714800487793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635652226077143200325195 12953478339115714800487793)
              ·
                refine ⟨9715108754336786100365845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12953478339115714800487793 9715108754336786100365845)
                ·
                  refine ⟨455395722859536848454649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9715108754336786100365845 455395722859536848454649)
                  ·
                    rfl

theorem cell21_1995480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_1995480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995480 prefixEnd_1995480 := by exact prefixLift 1995480
  have htrace : WordTrace (prefixWord ++ tailWord_1995480) baseStart_1995480 baseEnd_1995480 := by
    simpa [prefixWord, tailWord_1995480, baseEnd_1995480] using wordTrace_append hprefix tailTrace_1995480
  have hstable : (prefixWord ++ tailWord_1995480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995480).length < 2 ^ (prefixWord ++ tailWord_1995480).sum := by decide
  have hdescent : baseEnd_1995480 < baseStart_1995480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995525 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1995525 : Nat := 118140960795 + 1995525 * 2 ^ 59
def prefixEnd_1995525 : Nat := 4983230072969 + 3 ^ 40 * 1995525 * 2
def baseEnd_1995525 : Nat := 455405992472626770204557

theorem tailTrace_1995525 : CollatzResearch.WordTrace tailWord_1995525 prefixEnd_1995525 455405992472626770204557 := by
  unfold tailWord_1995525
  simp only [CollatzResearch.WordTrace]
  refine ⟨72782776095561208381956029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48521850730374138921304019 72782776095561208381956029)
  ·
    refine ⟨27293541035835453143233511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72782776095561208381956029 27293541035835453143233511)
    ·
      refine ⟨40940311553753179714850267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27293541035835453143233511 40940311553753179714850267)
      ·
        refine ⟨61410467330629769572275401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40940311553753179714850267 61410467330629769572275401)
        ·
          refine ⟨46057850497972327179206551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61410467330629769572275401 46057850497972327179206551)
          ·
            refine ⟨69086775746958490768809827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46057850497972327179206551 69086775746958490768809827)
            ·
              refine ⟨103630163620437736153214741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69086775746958490768809827 103630163620437736153214741)
              ·
                refine ⟨4857663919708018882181941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103630163620437736153214741 4857663919708018882181941)
                ·
                  refine ⟨455405992472626770204557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4857663919708018882181941 455405992472626770204557)
                  ·
                    rfl

theorem cell21_1995525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1995525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995525 prefixEnd_1995525 := by exact prefixLift 1995525
  have htrace : WordTrace (prefixWord ++ tailWord_1995525) baseStart_1995525 baseEnd_1995525 := by
    simpa [prefixWord, tailWord_1995525, baseEnd_1995525] using wordTrace_append hprefix tailTrace_1995525
  have hstable : (prefixWord ++ tailWord_1995525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995525).length < 2 ^ (prefixWord ++ tailWord_1995525).sum := by decide
  have hdescent : baseEnd_1995525 < baseStart_1995525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995562 : List Nat := [3, 1, 4, 3, 2, 1, 1, 6]
def baseStart_1995562 : Nat := 118140960795 + 1995562 * 2 ^ 59
def prefixEnd_1995562 : Nat := 4983230072969 + 3 ^ 40 * 1995562 * 2
def baseEnd_1995562 : Nat := 151804812125574309362605

theorem tailTrace_1995562 : CollatzResearch.WordTrace tailWord_1995562 prefixEnd_1995562 151804812125574309362605 := by
  unfold tailWord_1995562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18196031399106790925263235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48522750397618109134035293 18196031399106790925263235)
  ·
    refine ⟨27294047098660186387894853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18196031399106790925263235 27294047098660186387894853)
    ·
      refine ⟨5117633830998784947730285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27294047098660186387894853 5117633830998784947730285)
      ·
        refine ⟨1919112686624544355398857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5117633830998784947730285 1919112686624544355398857)
        ·
          refine ⟨1439334514968408266549143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1919112686624544355398857 1439334514968408266549143)
          ·
            refine ⟨2159001772452612399823715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439334514968408266549143 2159001772452612399823715)
            ·
              refine ⟨3238502658678918599735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159001772452612399823715 3238502658678918599735573)
              ·
                refine ⟨151804812125574309362605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3238502658678918599735573 151804812125574309362605)
                ·
                  rfl

theorem cell21_1995562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_1995562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995562 prefixEnd_1995562 := by exact prefixLift 1995562
  have htrace : WordTrace (prefixWord ++ tailWord_1995562) baseStart_1995562 baseEnd_1995562 := by
    simpa [prefixWord, tailWord_1995562, baseEnd_1995562] using wordTrace_append hprefix tailTrace_1995562
  have hstable : (prefixWord ++ tailWord_1995562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995562).length < 2 ^ (prefixWord ++ tailWord_1995562).sum := by decide
  have hdescent : baseEnd_1995562 < baseStart_1995562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995573 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1995573 : Nat := 118140960795 + 1995573 * 2 ^ 59
def prefixEnd_1995573 : Nat := 4983230072969 + 3 ^ 40 * 1995573 * 2
def baseEnd_1995573 : Nat := 455416946726589353404459

theorem tailTrace_1995573 : CollatzResearch.WordTrace tailWord_1995573 prefixEnd_1995573 455416946726589353404459 := by
  unfold tailWord_1995573
  simp only [CollatzResearch.WordTrace]
  refine ⟨72784526799387312579703373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48523017866258208386468915 72784526799387312579703373)
  ·
    refine ⟨27294197549770242217388765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72784526799387312579703373 27294197549770242217388765)
    ·
      refine ⟨10235324081163840831520787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27294197549770242217388765 10235324081163840831520787)
      ·
        refine ⟨15352986121745761247281181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235324081163840831520787 15352986121745761247281181)
        ·
          refine ⟨5757369795654660467730443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15352986121745761247281181 5757369795654660467730443)
          ·
            refine ⟨8636054693481990701595665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757369795654660467730443 8636054693481990701595665)
            ·
              refine ⟨6477041020111493026196749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8636054693481990701595665 6477041020111493026196749)
              ·
                refine ⟨2428890382541809884823781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6477041020111493026196749 2428890382541809884823781)
                ·
                  refine ⟨455416946726589353404459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428890382541809884823781 455416946726589353404459)
                  ·
                    rfl

theorem cell21_1995573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1995573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995573 prefixEnd_1995573 := by exact prefixLift 1995573
  have htrace : WordTrace (prefixWord ++ tailWord_1995573) baseStart_1995573 baseEnd_1995573 := by
    simpa [prefixWord, tailWord_1995573, baseEnd_1995573] using wordTrace_append hprefix tailTrace_1995573
  have hstable : (prefixWord ++ tailWord_1995573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995573).length < 2 ^ (prefixWord ++ tailWord_1995573).sum := by decide
  have hdescent : baseEnd_1995573 < baseStart_1995573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995587 : List Nat := [1, 1, 1, 3, 1, 4, 5, 5]
def baseStart_1995587 : Nat := 118140960795 + 1995587 * 2 ^ 59
def prefixEnd_1995587 : Nat := 4983230072969 + 3 ^ 40 * 1995587 * 2
def baseEnd_1995587 : Nat := 151806713905776146723699

theorem tailTrace_1995587 : CollatzResearch.WordTrace tailWord_1995587 prefixEnd_1995587 151806713905776146723699 := by
  unfold tailWord_1995587
  simp only [CollatzResearch.WordTrace]
  refine ⟨72785037421336592970713015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48523358280891061980475343 72785037421336592970713015)
  ·
    refine ⟨109177556132004889456069523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72785037421336592970713015 109177556132004889456069523)
    ·
      refine ⟨163766334198007334184104285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109177556132004889456069523 163766334198007334184104285)
      ·
        refine ⟨61412375324252750319039107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163766334198007334184104285 61412375324252750319039107)
        ·
          refine ⟨92118562986379125478558661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61412375324252750319039107 92118562986379125478558661)
          ·
            refine ⟨17272230559946086027229749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92118562986379125478558661 17272230559946086027229749)
            ·
              refine ⟨1619271614994945565052789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17272230559946086027229749 1619271614994945565052789)
              ·
                refine ⟨151806713905776146723699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1619271614994945565052789 151806713905776146723699)
                ·
                  rfl

theorem cell21_1995587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 5].length) (baseStart_1995587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995587 prefixEnd_1995587 := by exact prefixLift 1995587
  have htrace : WordTrace (prefixWord ++ tailWord_1995587) baseStart_1995587 baseEnd_1995587 := by
    simpa [prefixWord, tailWord_1995587, baseEnd_1995587] using wordTrace_append hprefix tailTrace_1995587
  have hstable : (prefixWord ++ tailWord_1995587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995587).length < 2 ^ (prefixWord ++ tailWord_1995587).sum := by decide
  have hdescent : baseEnd_1995587 < baseStart_1995587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995632 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_1995632 : Nat := 118140960795 + 1995632 * 2 ^ 59
def prefixEnd_1995632 : Nat := 4983230072969 + 3 ^ 40 * 1995632 * 2
def baseEnd_1995632 : Nat := 455430411330418361921005

theorem tailTrace_1995632 : CollatzResearch.WordTrace tailWord_1995632 prefixEnd_1995632 455430411330418361921005 := by
  unfold tailWord_1995632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36393339353086782828050575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48524452470782377104067433 36393339353086782828050575)
  ·
    refine ⟨54590009029630174242075863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36393339353086782828050575 54590009029630174242075863)
    ·
      refine ⟨81885013544445261363113795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54590009029630174242075863 81885013544445261363113795)
      ·
        refine ⟨122827520316667892044670693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81885013544445261363113795 122827520316667892044670693)
        ·
          refine ⟨23030160059375229758375755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122827520316667892044670693 23030160059375229758375755)
          ·
            refine ⟨34545240089062844637563633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23030160059375229758375755 34545240089062844637563633)
            ·
              refine ⟨25908930066797133478172725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34545240089062844637563633 25908930066797133478172725)
              ·
                refine ⟨2428962193762231263578693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25908930066797133478172725 2428962193762231263578693)
                ·
                  refine ⟨455430411330418361921005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2428962193762231263578693 455430411330418361921005)
                  ·
                    rfl

theorem cell21_1995632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_1995632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995632 prefixEnd_1995632 := by exact prefixLift 1995632
  have htrace : WordTrace (prefixWord ++ tailWord_1995632) baseStart_1995632 baseEnd_1995632 := by
    simpa [prefixWord, tailWord_1995632, baseEnd_1995632] using wordTrace_append hprefix tailTrace_1995632
  have hstable : (prefixWord ++ tailWord_1995632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995632).length < 2 ^ (prefixWord ++ tailWord_1995632).sum := by decide
  have hdescent : baseEnd_1995632 < baseStart_1995632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995784 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_1995784 : Nat := 118140960795 + 1995784 * 2 ^ 59
def prefixEnd_1995784 : Nat := 4983230072969 + 3 ^ 40 * 1995784 * 2
def baseEnd_1995784 : Nat := 455465099801299875387361

theorem tailTrace_1995784 : CollatzResearch.WordTrace tailWord_1995784 prefixEnd_1995784 455465099801299875387361 := by
  unfold tailWord_1995784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36396111300811447807817203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48528148401081930410422937 36396111300811447807817203)
  ·
    refine ⟨54594166951217171711725805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36396111300811447807817203 54594166951217171711725805)
    ·
      refine ⟨20472812606706439391897177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54594166951217171711725805 20472812606706439391897177)
      ·
        refine ⟨15354609455029829543922883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20472812606706439391897177 15354609455029829543922883)
        ·
          refine ⟨23031914182544744315884325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15354609455029829543922883 23031914182544744315884325)
          ·
            refine ⟨4318483909227139559228311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23031914182544744315884325 4318483909227139559228311)
            ·
              refine ⟨6477725863840709338842467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318483909227139559228311 6477725863840709338842467)
              ·
                refine ⟨9716588795761064008263701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6477725863840709338842467 9716588795761064008263701)
                ·
                  refine ⟨455465099801299875387361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9716588795761064008263701 455465099801299875387361)
                  ·
                    rfl

theorem cell21_1995784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_1995784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995784 prefixEnd_1995784 := by exact prefixLift 1995784
  have htrace : WordTrace (prefixWord ++ tailWord_1995784) baseStart_1995784 baseEnd_1995784 := by
    simpa [prefixWord, tailWord_1995784, baseEnd_1995784] using wordTrace_append hprefix tailTrace_1995784
  have hstable : (prefixWord ++ tailWord_1995784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995784).length < 2 ^ (prefixWord ++ tailWord_1995784).sum := by decide
  have hdescent : baseEnd_1995784 < baseStart_1995784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995843 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_1995843 : Nat := 118140960795 + 1995843 * 2 ^ 59
def prefixEnd_1995843 : Nat := 4983230072969 + 3 ^ 40 * 1995843 * 2
def baseEnd_1995843 : Nat := 455478564405128883903907

theorem tailTrace_1995843 : CollatzResearch.WordTrace tailWord_1995843 prefixEnd_1995843 455478564405128883903907 := by
  unfold tailWord_1995843
  simp only [CollatzResearch.WordTrace]
  refine ⟨72794374508409148692032183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48529583005606099128021455 72794374508409148692032183)
  ·
    refine ⟨109191561762613723038048275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72794374508409148692032183 109191561762613723038048275)
    ·
      refine ⟨163787342643920584557072413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109191561762613723038048275 163787342643920584557072413)
      ·
        refine ⟨61420253491470219208902155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163787342643920584557072413 61420253491470219208902155)
        ·
          refine ⟨92130380237205328813353233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61420253491470219208902155 92130380237205328813353233)
          ·
            refine ⟨69097785177903996610014925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92130380237205328813353233 69097785177903996610014925)
            ·
              refine ⟨25911669441713998728755597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69097785177903996610014925 25911669441713998728755597)
              ·
                refine ⟨9716876040642749523283349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25911669441713998728755597 9716876040642749523283349)
                ·
                  refine ⟨455478564405128883903907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9716876040642749523283349 455478564405128883903907)
                  ·
                    rfl

theorem cell21_1995843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_1995843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995843 prefixEnd_1995843 := by exact prefixLift 1995843
  have htrace : WordTrace (prefixWord ++ tailWord_1995843) baseStart_1995843 baseEnd_1995843 := by
    simpa [prefixWord, tailWord_1995843, baseEnd_1995843] using wordTrace_append hprefix tailTrace_1995843
  have hstable : (prefixWord ++ tailWord_1995843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995843).length < 2 ^ (prefixWord ++ tailWord_1995843).sum := by decide
  have hdescent : baseEnd_1995843 < baseStart_1995843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995897 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 3]
def baseStart_1995897 : Nat := 118140960795 + 1995897 * 2 ^ 59
def prefixEnd_1995897 : Nat := 4983230072969 + 3 ^ 40 * 1995897 * 2
def baseEnd_1995897 : Nat := 455490887940836790003797

theorem tailTrace_1995897 : CollatzResearch.WordTrace tailWord_1995897 prefixEnd_1995897 455490887940836790003797 := by
  unfold tailWord_1995897
  simp only [CollatzResearch.WordTrace]
  refine ⟨72796344050213515914497945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48530896033475677276331963 72796344050213515914497945)
  ·
    refine ⟨54597258037660136935873459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72796344050213515914497945 54597258037660136935873459)
    ·
      refine ⟨81895887056490205403810189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54597258037660136935873459 81895887056490205403810189)
      ·
        refine ⟨30710957646183827026428821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81895887056490205403810189 30710957646183827026428821)
        ·
          refine ⟨1439576139664866891863851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30710957646183827026428821 1439576139664866891863851)
          ·
            refine ⟨2159364209497300337795777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439576139664866891863851 2159364209497300337795777)
            ·
              refine ⟨1619523157122975253346833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2159364209497300337795777 1619523157122975253346833)
              ·
                refine ⟨1214642367842231440010125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619523157122975253346833 1214642367842231440010125)
                ·
                  refine ⟨455490887940836790003797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214642367842231440010125 455490887940836790003797)
                  ·
                    rfl

theorem cell21_1995897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_1995897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995897 prefixEnd_1995897 := by exact prefixLift 1995897
  have htrace : WordTrace (prefixWord ++ tailWord_1995897) baseStart_1995897 baseEnd_1995897 := by
    simpa [prefixWord, tailWord_1995897, baseEnd_1995897] using wordTrace_append hprefix tailTrace_1995897
  have hstable : (prefixWord ++ tailWord_1995897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995897).length < 2 ^ (prefixWord ++ tailWord_1995897).sum := by decide
  have hdescent : baseEnd_1995897 < baseStart_1995897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995922 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1995922 : Nat := 118140960795 + 1995922 * 2 ^ 59
def prefixEnd_1995922 : Nat := 4983230072969 + 3 ^ 40 * 1995922 * 2
def baseEnd_1995922 : Nat := 455496593281442302087079

theorem tailTrace_1995922 : CollatzResearch.WordTrace tailWord_1995922 prefixEnd_1995922 455496593281442302087079 := by
  unfold tailWord_1995922
  simp only [CollatzResearch.WordTrace]
  refine ⟨18199313968780736296039505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48531503916748630122772013 18199313968780736296039505)
  ·
    refine ⟨13649485476585552222029629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18199313968780736296039505 13649485476585552222029629)
    ·
      refine ⟨5118557053719582083261111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13649485476585552222029629 5118557053719582083261111)
      ·
        refine ⟨7677835580579373124891667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118557053719582083261111 7677835580579373124891667)
        ·
          refine ⟨11516753370869059687337501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677835580579373124891667 11516753370869059687337501)
          ·
            refine ⟨4318782514075897382751563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11516753370869059687337501 4318782514075897382751563)
            ·
              refine ⟨6478173771113846074127345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318782514075897382751563 6478173771113846074127345)
              ·
                refine ⟨4858630328335384555595509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6478173771113846074127345 4858630328335384555595509)
                ·
                  refine ⟨455496593281442302087079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858630328335384555595509 455496593281442302087079)
                  ·
                    rfl

theorem cell21_1995922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1995922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995922 prefixEnd_1995922 := by exact prefixLift 1995922
  have htrace : WordTrace (prefixWord ++ tailWord_1995922) baseStart_1995922 baseEnd_1995922 := by
    simpa [prefixWord, tailWord_1995922, baseEnd_1995922] using wordTrace_append hprefix tailTrace_1995922
  have hstable : (prefixWord ++ tailWord_1995922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995922).length < 2 ^ (prefixWord ++ tailWord_1995922).sum := by decide
  have hdescent : baseEnd_1995922 < baseStart_1995922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995953 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 4]
def baseStart_1995953 : Nat := 118140960795 + 1995953 * 2 ^ 59
def prefixEnd_1995953 : Nat := 4983230072969 + 3 ^ 40 * 1995953 * 2
def baseEnd_1995953 : Nat := 455503667903793137070349

theorem tailTrace_1995953 : CollatzResearch.WordTrace tailWord_1995953 prefixEnd_1995953 455503667903793137070349 := by
  unfold tailWord_1995953
  simp only [CollatzResearch.WordTrace]
  refine ⟨72798386538010637478536513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48532257692007091652357675 72798386538010637478536513)
  ·
    refine ⟨54598789903507978108902385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72798386538010637478536513 54598789903507978108902385)
    ·
      refine ⟨40949092427630983581676789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54598789903507978108902385 40949092427630983581676789)
      ·
        refine ⟨3838977415090404710782199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40949092427630983581676789 3838977415090404710782199)
        ·
          refine ⟨5758466122635607066173299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838977415090404710782199 5758466122635607066173299)
          ·
            refine ⟨8637699183953410599259949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758466122635607066173299 8637699183953410599259949)
            ·
              refine ⟨3239137193982528974722481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8637699183953410599259949 3239137193982528974722481)
              ·
                refine ⟨2429352895486896731041861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239137193982528974722481 2429352895486896731041861)
                ·
                  refine ⟨455503667903793137070349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2429352895486896731041861 455503667903793137070349)
                  ·
                    rfl

theorem cell21_1995953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_1995953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995953 prefixEnd_1995953 := by exact prefixLift 1995953
  have htrace : WordTrace (prefixWord ++ tailWord_1995953) baseStart_1995953 baseEnd_1995953 := by
    simpa [prefixWord, tailWord_1995953, baseEnd_1995953] using wordTrace_append hprefix tailTrace_1995953
  have hstable : (prefixWord ++ tailWord_1995953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995953).length < 2 ^ (prefixWord ++ tailWord_1995953).sum := by decide
  have hdescent : baseEnd_1995953 < baseStart_1995953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1995990 : List Nat := [5, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1995990 : Nat := 118140960795 + 1995990 * 2 ^ 59
def prefixEnd_1995990 : Nat := 4983230072969 + 3 ^ 40 * 1995990 * 2
def baseEnd_1995990 : Nat := 455512111807889294953607

theorem tailTrace_1995990 : CollatzResearch.WordTrace tailWord_1995990 prefixEnd_1995990 455512111807889294953607 := by
  unfold tailWord_1995990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4549983502429787049852089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48533157359251061865088949 4549983502429787049852089)
  ·
    refine ⟨3412487626822340287389067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4549983502429787049852089 3412487626822340287389067)
    ·
      refine ⟨5118731440233510431083601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3412487626822340287389067 5118731440233510431083601)
      ·
        refine ⟨3839048580175132823312701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5118731440233510431083601 3839048580175132823312701)
        ·
          refine ⟨1439643217565674808742263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3839048580175132823312701 1439643217565674808742263)
          ·
            refine ⟨2159464826348512213113395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439643217565674808742263 2159464826348512213113395)
            ·
              refine ⟨3239197239522768319670093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159464826348512213113395 3239197239522768319670093)
              ·
                refine ⟨1214698964821038119876285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3239197239522768319670093 1214698964821038119876285)
                ·
                  refine ⟨455512111807889294953607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214698964821038119876285 455512111807889294953607)
                  ·
                    rfl

theorem cell21_1995990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1995990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1995990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1995990 prefixEnd_1995990 := by exact prefixLift 1995990
  have htrace : WordTrace (prefixWord ++ tailWord_1995990) baseStart_1995990 baseEnd_1995990 := by
    simpa [prefixWord, tailWord_1995990, baseEnd_1995990] using wordTrace_append hprefix tailTrace_1995990
  have hstable : (prefixWord ++ tailWord_1995990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1995990).length < 2 ^ (prefixWord ++ tailWord_1995990).sum := by decide
  have hdescent : baseEnd_1995990 < baseStart_1995990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1995990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996015 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 5]
def baseStart_1996015 : Nat := 118140960795 + 1996015 * 2 ^ 59
def prefixEnd_1996015 : Nat := 4983230072969 + 3 ^ 40 * 1996015 * 2
def baseEnd_1996015 : Nat := 455517817148494807036889

theorem tailTrace_1996015 : CollatzResearch.WordTrace tailWord_1996015 prefixEnd_1996015 455517817148494807036889 := by
  unfold tailWord_1996015
  simp only [CollatzResearch.WordTrace]
  refine ⟨72800647863786022067293499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48533765242524014711528999 72800647863786022067293499)
  ·
    refine ⟨109200971795679033100940249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72800647863786022067293499 109200971795679033100940249)
    ·
      refine ⟨81900728846759274825705187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109200971795679033100940249 81900728846759274825705187)
      ·
        refine ⟨122851093270138912238557781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81900728846759274825705187 122851093270138912238557781)
        ·
          refine ⟨1439661249259440377795599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 122851093270138912238557781 1439661249259440377795599)
          ·
            refine ⟨2159491873889160566693399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439661249259440377795599 2159491873889160566693399)
            ·
              refine ⟨3239237810833740850040099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159491873889160566693399 3239237810833740850040099)
              ·
                refine ⟨4858856716250611275060149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239237810833740850040099 4858856716250611275060149)
                ·
                  refine ⟨455517817148494807036889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4858856716250611275060149 455517817148494807036889)
                  ·
                    rfl

theorem cell21_1996015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 5].length) (baseStart_1996015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996015 prefixEnd_1996015 := by exact prefixLift 1996015
  have htrace : WordTrace (prefixWord ++ tailWord_1996015) baseStart_1996015 baseEnd_1996015 := by
    simpa [prefixWord, tailWord_1996015, baseEnd_1996015] using wordTrace_append hprefix tailTrace_1996015
  have hstable : (prefixWord ++ tailWord_1996015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996015).length < 2 ^ (prefixWord ++ tailWord_1996015).sum := by decide
  have hdescent : baseEnd_1996015 < baseStart_1996015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996026 : List Nat := [3, 1, 1, 1, 1, 4, 4, 6]
def baseStart_1996026 : Nat := 118140960795 + 1996026 * 2 ^ 59
def prefixEnd_1996026 : Nat := 4983230072969 + 3 ^ 40 * 1996026 * 2
def baseEnd_1996026 : Nat := 151840109166120410784511

theorem tailTrace_1996026 : CollatzResearch.WordTrace tailWord_1996026 prefixEnd_1996026 151840109166120410784511 := by
  unfold tailWord_1996026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200262266686542736485983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48534032711164113963962621 18200262266686542736485983)
  ·
    refine ⟨27300393400029814104728975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18200262266686542736485983 27300393400029814104728975)
    ·
      refine ⟨40950590100044721157093463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27300393400029814104728975 40950590100044721157093463)
      ·
        refine ⟨61425885150067081735640195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40950590100044721157093463 61425885150067081735640195)
        ·
          refine ⟨92138827725100622603460293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61425885150067081735640195 92138827725100622603460293)
          ·
            refine ⟨17276030198456366738148805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92138827725100622603460293 17276030198456366738148805)
            ·
              refine ⟨3239255662210568763402901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17276030198456366738148805 3239255662210568763402901)
              ·
                refine ⟨151840109166120410784511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3239255662210568763402901 151840109166120410784511)
                ·
                  rfl

theorem cell21_1996026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_1996026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996026 prefixEnd_1996026 := by exact prefixLift 1996026
  have htrace : WordTrace (prefixWord ++ tailWord_1996026) baseStart_1996026 baseEnd_1996026 := by
    simpa [prefixWord, tailWord_1996026, baseEnd_1996026] using wordTrace_append hprefix tailTrace_1996026
  have hstable : (prefixWord ++ tailWord_1996026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996026).length < 2 ^ (prefixWord ++ tailWord_1996026).sum := by decide
  have hdescent : baseEnd_1996026 < baseStart_1996026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996133 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1996133 : Nat := 118140960795 + 1996133 * 2 ^ 59
def prefixEnd_1996133 : Nat := 4983230072969 + 3 ^ 40 * 1996133 * 2
def baseEnd_1996133 : Nat := 455544746356152824069981

theorem tailTrace_1996133 : CollatzResearch.WordTrace tailWord_1996133 prefixEnd_1996133 455544746356152824069981 := by
  unfold tailWord_1996133
  simp only [CollatzResearch.WordTrace]
  refine ⟨72804951677358528220089053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48536634451572352146726035 72804951677358528220089053)
  ·
    refine ⟨27301856879009448082533395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72804951677358528220089053 27301856879009448082533395)
    ·
      refine ⟨40952785318514172123800093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27301856879009448082533395 40952785318514172123800093)
      ·
        refine ⟨15357294494442814546425035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40952785318514172123800093 15357294494442814546425035)
        ·
          refine ⟨23035941741664221819637553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15357294494442814546425035 23035941741664221819637553)
          ·
            refine ⟨17276956306248166364728165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23035941741664221819637553 17276956306248166364728165)
            ·
              refine ⟨3239429307421531193386531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17276956306248166364728165 3239429307421531193386531)
              ·
                refine ⟨4859143961132296790079797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239429307421531193386531 4859143961132296790079797)
                ·
                  refine ⟨455544746356152824069981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4859143961132296790079797 455544746356152824069981)
                  ·
                    rfl

theorem cell21_1996133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1996133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996133 prefixEnd_1996133 := by exact prefixLift 1996133
  have htrace : WordTrace (prefixWord ++ tailWord_1996133) baseStart_1996133 baseEnd_1996133 := by
    simpa [prefixWord, tailWord_1996133, baseEnd_1996133] using wordTrace_append hprefix tailTrace_1996133
  have hstable : (prefixWord ++ tailWord_1996133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996133).length < 2 ^ (prefixWord ++ tailWord_1996133).sum := by decide
  have hdescent : baseEnd_1996133 < baseStart_1996133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996167 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 3]
def baseStart_1996167 : Nat := 118140960795 + 1996167 * 2 ^ 59
def prefixEnd_1996167 : Nat := 4983230072969 + 3 ^ 40 * 1996167 * 2
def baseEnd_1996167 : Nat := 455552505619376320503245

theorem tailTrace_1996167 : CollatzResearch.WordTrace tailWord_1996167 prefixEnd_1996167 455552505619376320503245 := by
  unfold tailWord_1996167
  simp only [CollatzResearch.WordTrace]
  refine ⟨72806191759235352026826755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48537461172823568017884503 72806191759235352026826755)
  ·
    refine ⟨109209287638853028040240133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72806191759235352026826755 109209287638853028040240133)
    ·
      refine ⟨20476741432284942757545025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109209287638853028040240133 20476741432284942757545025)
      ·
        refine ⟨15357556074213707068158769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20476741432284942757545025 15357556074213707068158769)
        ·
          refine ⟨11518167055660280301119077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15357556074213707068158769 11518167055660280301119077)
          ·
            refine ⟨2159656322936302556459827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11518167055660280301119077 2159656322936302556459827)
            ·
              refine ⟨3239484484404453834689741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2159656322936302556459827 3239484484404453834689741)
              ·
                refine ⟨1214806681651670188008653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3239484484404453834689741 1214806681651670188008653)
                ·
                  refine ⟨455552505619376320503245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214806681651670188008653 455552505619376320503245)
                  ·
                    rfl

theorem cell21_1996167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 3].length) (baseStart_1996167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996167 prefixEnd_1996167 := by exact prefixLift 1996167
  have htrace : WordTrace (prefixWord ++ tailWord_1996167) baseStart_1996167 baseEnd_1996167 := by
    simpa [prefixWord, tailWord_1996167, baseEnd_1996167] using wordTrace_append hprefix tailTrace_1996167
  have hstable : (prefixWord ++ tailWord_1996167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996167).length < 2 ^ (prefixWord ++ tailWord_1996167).sum := by decide
  have hdescent : baseEnd_1996167 < baseStart_1996167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996184 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_1996184 : Nat := 118140960795 + 1996184 * 2 ^ 59
def prefixEnd_1996184 : Nat := 4983230072969 + 3 ^ 40 * 1996184 * 2
def baseEnd_1996184 : Nat := 455556385250988068719877

theorem tailTrace_1996184 : CollatzResearch.WordTrace tailWord_1996184 prefixEnd_1996184 455556385250988068719877 := by
  unfold tailWord_1996184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36403405900086881965097803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48537874533449175953463737 36403405900086881965097803)
  ·
    refine ⟨54605108850130322947646705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36403405900086881965097803 54605108850130322947646705)
    ·
      refine ⟨40953831637597742210735029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54605108850130322947646705 40953831637597742210735029)
      ·
        refine ⟨3839421716024788332256409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40953831637597742210735029 3839421716024788332256409)
        ·
          refine ⟨2879566287018591249192307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839421716024788332256409 2879566287018591249192307)
          ·
            refine ⟨4319349430527886873788461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879566287018591249192307 4319349430527886873788461)
            ·
              refine ⟨1619756036447957577670673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4319349430527886873788461 1619756036447957577670673)
              ·
                refine ⟨1214817027335968183253005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619756036447957577670673 1214817027335968183253005)
                ·
                  refine ⟨455556385250988068719877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214817027335968183253005 455556385250988068719877)
                  ·
                    rfl

theorem cell21_1996184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_1996184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996184 prefixEnd_1996184 := by exact prefixLift 1996184
  have htrace : WordTrace (prefixWord ++ tailWord_1996184) baseStart_1996184 baseEnd_1996184 := by
    simpa [prefixWord, tailWord_1996184, baseEnd_1996184] using wordTrace_append hprefix tailTrace_1996184
  have hstable : (prefixWord ++ tailWord_1996184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996184).length < 2 ^ (prefixWord ++ tailWord_1996184).sum := by decide
  have hdescent : baseEnd_1996184 < baseStart_1996184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996302 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1996302 : Nat := 118140960795 + 1996302 * 2 ^ 59
def prefixEnd_1996302 : Nat := 4983230072969 + 3 ^ 40 * 1996302 * 2
def baseEnd_1996302 : Nat := 455583314458646085752969

theorem tailTrace_1996302 : CollatzResearch.WordTrace tailWord_1996302 prefixEnd_1996302 455583314458646085752969 := by
  unfold tailWord_1996302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101389451718283760373895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48540743742497513388660773 9101389451718283760373895)
  ·
    refine ⟨13652084177577425640560843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9101389451718283760373895 13652084177577425640560843)
    ·
      refine ⟨20478126266366138460841265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13652084177577425640560843 20478126266366138460841265)
      ·
        refine ⟨15358594699774603845630949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20478126266366138460841265 15358594699774603845630949)
        ·
          refine ⟨2879736506207738221055803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15358594699774603845630949 2879736506207738221055803)
          ·
            refine ⟨4319604759311607331583705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879736506207738221055803 4319604759311607331583705)
            ·
              refine ⟨3239703569483705498687779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319604759311607331583705 3239703569483705498687779)
              ·
                refine ⟨4859555354225558248031669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239703569483705498687779 4859555354225558248031669)
                ·
                  refine ⟨455583314458646085752969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4859555354225558248031669 455583314458646085752969)
                  ·
                    rfl

theorem cell21_1996302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1996302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996302 prefixEnd_1996302 := by exact prefixLift 1996302
  have htrace : WordTrace (prefixWord ++ tailWord_1996302) baseStart_1996302 baseEnd_1996302 := by
    simpa [prefixWord, tailWord_1996302, baseEnd_1996302] using wordTrace_append hprefix tailTrace_1996302
  have hstable : (prefixWord ++ tailWord_1996302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996302).length < 2 ^ (prefixWord ++ tailWord_1996302).sum := by decide
  have hdescent : baseEnd_1996302 < baseStart_1996302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996330 : List Nat := [3, 1, 4, 1, 1, 1, 3, 7]
def baseStart_1996330 : Nat := 118140960795 + 1996330 * 2 ^ 59
def prefixEnd_1996330 : Nat := 4983230072969 + 3 ^ 40 * 1996330 * 2
def baseEnd_1996330 : Nat := 151863234813374753095415

theorem tailTrace_1996330 : CollatzResearch.WordTrace tailWord_1996330 prefixEnd_1996330 151863234813374753095415 := by
  unfold tailWord_1996330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18203034214411207716252611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48541424571763220576673629 18203034214411207716252611)
  ·
    refine ⟨27304551321616811574378917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18203034214411207716252611 27304551321616811574378917)
    ·
      refine ⟨5119603372803152170196047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27304551321616811574378917 5119603372803152170196047)
      ·
        refine ⟨7679405059204728255294071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5119603372803152170196047 7679405059204728255294071)
        ·
          refine ⟨11519107588807092382941107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7679405059204728255294071 11519107588807092382941107)
          ·
            refine ⟨17278661383210638574411661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11519107588807092382941107 17278661383210638574411661)
            ·
              refine ⟨6479498018703989465404373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17278661383210638574411661 6479498018703989465404373)
              ·
                refine ⟨151863234813374753095415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6479498018703989465404373 151863234813374753095415)
                ·
                  rfl

theorem cell21_1996330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_1996330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996330 prefixEnd_1996330 := by exact prefixLift 1996330
  have htrace : WordTrace (prefixWord ++ tailWord_1996330) baseStart_1996330 baseEnd_1996330 := by
    simpa [prefixWord, tailWord_1996330, baseEnd_1996330] using wordTrace_append hprefix tailTrace_1996330
  have hstable : (prefixWord ++ tailWord_1996330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996330).length < 2 ^ (prefixWord ++ tailWord_1996330).sum := by decide
  have hdescent : baseEnd_1996330 < baseStart_1996330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996361 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 3]
def baseStart_1996361 : Nat := 118140960795 + 1996361 * 2 ^ 59
def prefixEnd_1996361 : Nat := 4983230072969 + 3 ^ 40 * 1996361 * 2
def baseEnd_1996361 : Nat := 455596779062475094269515

theorem tailTrace_1996361 : CollatzResearch.WordTrace tailWord_1996361 prefixEnd_1996361 455596779062475094269515 := by
  unfold tailWord_1996361
  simp only [CollatzResearch.WordTrace]
  refine ⟨72813267520532523159388937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48542178347021682106259291 72813267520532523159388937)
  ·
    refine ⟨54609950640399392369541703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72813267520532523159388937 54609950640399392369541703)
    ·
      refine ⟨81914925960599088554312555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54609950640399392369541703 81914925960599088554312555)
      ·
        refine ⟨122872388940898632831468833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81914925960599088554312555 122872388940898632831468833)
        ·
          refine ⟨92154291705673974623601625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122872388940898632831468833 92154291705673974623601625)
          ·
            refine ⟨69115718779255480967701219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92154291705673974623601625 69115718779255480967701219)
            ·
              refine ⟨103673578168883221451551829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69115718779255480967701219 103673578168883221451551829)
              ·
                refine ⟨1214924744166600251385373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 103673578168883221451551829 1214924744166600251385373)
                ·
                  refine ⟨455596779062475094269515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1214924744166600251385373 455596779062475094269515)
                  ·
                    rfl

theorem cell21_1996361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_1996361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996361 prefixEnd_1996361 := by exact prefixLift 1996361
  have htrace : WordTrace (prefixWord ++ tailWord_1996361) baseStart_1996361 baseEnd_1996361 := by
    simpa [prefixWord, tailWord_1996361, baseEnd_1996361] using wordTrace_append hprefix tailTrace_1996361
  have hstable : (prefixWord ++ tailWord_1996361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996361).length < 2 ^ (prefixWord ++ tailWord_1996361).sum := by decide
  have hdescent : baseEnd_1996361 < baseStart_1996361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996406 : List Nat := [5, 1, 1, 2, 2, 10]
def baseStart_1996406 : Nat := 118140960795 + 1996406 * 2 ^ 59
def prefixEnd_1996406 : Nat := 4983230072969 + 3 ^ 40 * 1996406 * 2
def baseEnd_1996406 : Nat := 16874335136132037630349

theorem tailTrace_1996406 : CollatzResearch.WordTrace tailWord_1996406 prefixEnd_1996406 16874335136132037630349 := by
  unfold tailWord_1996406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550931800335593490298567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48543272536912997229851381 4550931800335593490298567)
  ·
    refine ⟨6826397700503390235447851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4550931800335593490298567 6826397700503390235447851)
    ·
      refine ⟨10239596550755085353171777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826397700503390235447851 10239596550755085353171777)
      ·
        refine ⟨7679697413066314014878833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10239596550755085353171777 7679697413066314014878833)
        ·
          refine ⟨5759773059799735511159125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7679697413066314014878833 5759773059799735511159125)
          ·
            refine ⟨16874335136132037630349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5759773059799735511159125 16874335136132037630349)
            ·
              rfl

theorem cell21_1996406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 10].length) (baseStart_1996406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996406 prefixEnd_1996406 := by exact prefixLift 1996406
  have htrace : WordTrace (prefixWord ++ tailWord_1996406) baseStart_1996406 baseEnd_1996406 := by
    simpa [prefixWord, tailWord_1996406, baseEnd_1996406] using wordTrace_append hprefix tailTrace_1996406
  have hstable : (prefixWord ++ tailWord_1996406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996406).length < 2 ^ (prefixWord ++ tailWord_1996406).sum := by decide
  have hdescent : baseEnd_1996406 < baseStart_1996406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996527 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 4]
def baseStart_1996527 : Nat := 118140960795 + 1996527 * 2 ^ 59
def prefixEnd_1996527 : Nat := 4983230072969 + 3 ^ 40 * 1996527 * 2
def baseEnd_1996527 : Nat := 455634662524095694502509

theorem tailTrace_1996527 : CollatzResearch.WordTrace tailWord_1996527 prefixEnd_1996527 455634662524095694502509 := by
  unfold tailWord_1996527
  simp only [CollatzResearch.WordTrace]
  refine ⟨72819322037931133509931835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48546214691954089006621223 72819322037931133509931835)
  ·
    refine ⟨109228983056896700264897753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72819322037931133509931835 109228983056896700264897753)
    ·
      refine ⟨81921737292672525198673315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109228983056896700264897753 81921737292672525198673315)
      ·
        refine ⟨122882605939008787798009973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81921737292672525198673315 122882605939008787798009973)
        ·
          refine ⟨11520244306782073856063435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122882605939008787798009973 11520244306782073856063435)
          ·
            refine ⟨17280366460173110784095153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520244306782073856063435 17280366460173110784095153)
            ·
              refine ⟨12960274845129833088071365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17280366460173110784095153 12960274845129833088071365)
              ·
                refine ⟨2430051533461843704013381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12960274845129833088071365 2430051533461843704013381)
                ·
                  refine ⟨455634662524095694502509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430051533461843704013381 455634662524095694502509)
                  ·
                    rfl

theorem cell21_1996527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_1996527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996527 prefixEnd_1996527 := by exact prefixLift 1996527
  have htrace : WordTrace (prefixWord ++ tailWord_1996527) baseStart_1996527 baseEnd_1996527 := by
    simpa [prefixWord, tailWord_1996527, baseEnd_1996527] using wordTrace_append hprefix tailTrace_1996527
  have hstable : (prefixWord ++ tailWord_1996527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996527).length < 2 ^ (prefixWord ++ tailWord_1996527).sum := by decide
  have hdescent : baseEnd_1996527 < baseStart_1996527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996769 : List Nat := [1, 2, 3, 1, 2, 1, 5, 6]
def baseStart_1996769 : Nat := 118140960795 + 1996769 * 2 ^ 59
def prefixEnd_1996769 : Nat := 4983230072969 + 3 ^ 40 * 1996769 * 2
def baseEnd_1996769 : Nat := 151896630073719017156227

theorem tailTrace_1996769 : CollatzResearch.WordTrace tailWord_1996769 prefixEnd_1996769 151896630073719017156227 := by
  unfold tailWord_1996769
  simp only [CollatzResearch.WordTrace]
  refine ⟨72828148503054408840241361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48552099002036272560160907 72828148503054408840241361)
  ·
    refine ⟨54621111377290806630181021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72828148503054408840241361 54621111377290806630181021)
    ·
      refine ⟨20482916766484052486317883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54621111377290806630181021 20482916766484052486317883)
      ·
        refine ⟨30724375149726078729476825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20482916766484052486317883 30724375149726078729476825)
        ·
          refine ⟨23043281362294559047107619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30724375149726078729476825 23043281362294559047107619)
          ·
            refine ⟨34564922043441838570661429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23043281362294559047107619 34564922043441838570661429)
            ·
              refine ⟨3240461441572672365999509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34564922043441838570661429 3240461441572672365999509)
              ·
                refine ⟨151896630073719017156227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3240461441572672365999509 151896630073719017156227)
                ·
                  rfl

theorem cell21_1996769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 6].length) (baseStart_1996769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996769 prefixEnd_1996769 := by exact prefixLift 1996769
  have htrace : WordTrace (prefixWord ++ tailWord_1996769) baseStart_1996769 baseEnd_1996769 := by
    simpa [prefixWord, tailWord_1996769, baseEnd_1996769] using wordTrace_append hprefix tailTrace_1996769
  have hstable : (prefixWord ++ tailWord_1996769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996769).length < 2 ^ (prefixWord ++ tailWord_1996769).sum := by decide
  have hdescent : baseEnd_1996769 < baseStart_1996769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996876 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_1996876 : Nat := 118140960795 + 1996876 * 2 ^ 59
def prefixEnd_1996876 : Nat := 4983230072969 + 3 ^ 40 * 1996876 * 2
def baseEnd_1996876 : Nat := 455714309078948643185129

theorem tailTrace_1996876 : CollatzResearch.WordTrace tailWord_1996876 prefixEnd_1996876 455714309078948643185129 := by
  unfold tailWord_1996876
  simp only [CollatzResearch.WordTrace]
  refine ⟨36416025556833383057193241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48554700742444510742924321 36416025556833383057193241)
  ·
    refine ⟨27312019167625037292894931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36416025556833383057193241 27312019167625037292894931)
    ·
      refine ⟨40968028751437555939342397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27312019167625037292894931 40968028751437555939342397)
      ·
        refine ⟨15363010781789083477253399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40968028751437555939342397 15363010781789083477253399)
        ·
          refine ⟨23044516172683625215880099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15363010781789083477253399 23044516172683625215880099)
          ·
            refine ⟨34566774259025437823820149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23044516172683625215880099 34566774259025437823820149)
            ·
              refine ⟨3240635086783634795983139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34566774259025437823820149 3240635086783634795983139)
              ·
                refine ⟨4860952630175452193974709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240635086783634795983139 4860952630175452193974709)
                ·
                  refine ⟨455714309078948643185129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4860952630175452193974709 455714309078948643185129)
                  ·
                    rfl

theorem cell21_1996876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_1996876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996876 prefixEnd_1996876 := by exact prefixLift 1996876
  have htrace : WordTrace (prefixWord ++ tailWord_1996876) baseStart_1996876 baseEnd_1996876 := by
    simpa [prefixWord, tailWord_1996876, baseEnd_1996876] using wordTrace_append hprefix tailTrace_1996876
  have hstable : (prefixWord ++ tailWord_1996876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996876).length < 2 ^ (prefixWord ++ tailWord_1996876).sum := by decide
  have hdescent : baseEnd_1996876 < baseStart_1996876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996882 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_1996882 : Nat := 118140960795 + 1996882 * 2 ^ 59
def prefixEnd_1996882 : Nat := 4983230072969 + 3 ^ 40 * 1996882 * 2
def baseEnd_1996882 : Nat := 455715678360693966085117

theorem tailTrace_1996882 : CollatzResearch.WordTrace tailWord_1996882 prefixEnd_1996882 455715678360693966085117 := by
  unfold tailWord_1996882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18208067487911257284776225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48554846634430019426069933 18208067487911257284776225)
  ·
    refine ⟨13656050615933442963582169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18208067487911257284776225 13656050615933442963582169)
    ·
      refine ⟨10242037961950082222686627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13656050615933442963582169 10242037961950082222686627)
      ·
        refine ⟨15363056942925123334029941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242037961950082222686627 15363056942925123334029941)
        ·
          refine ⟨1440286588399230312565307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15363056942925123334029941 1440286588399230312565307)
          ·
            refine ⟨2160429882598845468847961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440286588399230312565307 2160429882598845468847961)
            ·
              refine ⟨1620322411949134101635971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2160429882598845468847961 1620322411949134101635971)
              ·
                refine ⟨2430483617923701152453957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620322411949134101635971 2430483617923701152453957)
                ·
                  refine ⟨455715678360693966085117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430483617923701152453957 455715678360693966085117)
                  ·
                    rfl

theorem cell21_1996882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_1996882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996882 prefixEnd_1996882 := by exact prefixLift 1996882
  have htrace : WordTrace (prefixWord ++ tailWord_1996882) baseStart_1996882 baseEnd_1996882 := by
    simpa [prefixWord, tailWord_1996882, baseEnd_1996882] using wordTrace_append hprefix tailTrace_1996882
  have hstable : (prefixWord ++ tailWord_1996882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996882).length < 2 ^ (prefixWord ++ tailWord_1996882).sum := by decide
  have hdescent : baseEnd_1996882 < baseStart_1996882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996938 : List Nat := [3, 1, 2, 3, 1, 4, 1, 6]
def baseStart_1996938 : Nat := 118140960795 + 1996938 * 2 ^ 59
def prefixEnd_1996938 : Nat := 4983230072969 + 3 ^ 40 * 1996938 * 2
def baseEnd_1996938 : Nat := 151909486107883437717223

theorem tailTrace_1996938 : CollatzResearch.WordTrace tailWord_1996938 prefixEnd_1996938 151909486107883437717223 := by
  unfold tailWord_1996938
  simp only [CollatzResearch.WordTrace]
  refine ⟨18208578109860537675785867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48556208292961433802095645 18208578109860537675785867)
  ·
    refine ⟨27312867164790806513678801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18208578109860537675785867 27312867164790806513678801)
    ·
      refine ⟨20484650373593104885259101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27312867164790806513678801 20484650373593104885259101)
      ·
        refine ⟨7681743890097414331972163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20484650373593104885259101 7681743890097414331972163)
        ·
          refine ⟨11522615835146121497958245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681743890097414331972163 11522615835146121497958245)
          ·
            refine ⟨2160490469089897780867171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11522615835146121497958245 2160490469089897780867171)
            ·
              refine ⟨3240735703634846671300757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160490469089897780867171 3240735703634846671300757)
              ·
                refine ⟨151909486107883437717223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3240735703634846671300757 151909486107883437717223)
                ·
                  rfl

theorem cell21_1996938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_1996938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996938 prefixEnd_1996938 := by exact prefixLift 1996938
  have htrace : WordTrace (prefixWord ++ tailWord_1996938) baseStart_1996938 baseEnd_1996938 := by
    simpa [prefixWord, tailWord_1996938, baseEnd_1996938] using wordTrace_append hprefix tailTrace_1996938
  have hstable : (prefixWord ++ tailWord_1996938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996938).length < 2 ^ (prefixWord ++ tailWord_1996938).sum := by decide
  have hdescent : baseEnd_1996938 < baseStart_1996938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1996983 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 4]
def baseStart_1996983 : Nat := 118140960795 + 1996983 * 2 ^ 59
def prefixEnd_1996983 : Nat := 4983230072969 + 3 ^ 40 * 1996983 * 2
def baseEnd_1996983 : Nat := 455738727936740234901577

theorem tailTrace_1996983 : CollatzResearch.WordTrace tailWord_1996983 prefixEnd_1996983 455738727936740234901577 := by
  unfold tailWord_1996983
  simp only [CollatzResearch.WordTrace]
  refine ⟨72835953724279123388531603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48557302482852748925687735 72835953724279123388531603)
  ·
    refine ⟨109253930586418685082797405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72835953724279123388531603 109253930586418685082797405)
    ·
      refine ⟨40970223969907006906049027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109253930586418685082797405 40970223969907006906049027)
      ·
        refine ⟨61455335954860510359073541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40970223969907006906049027 61455335954860510359073541)
        ·
          refine ⟨11522875491536345692326289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61455335954860510359073541 11522875491536345692326289)
          ·
            refine ⟨8642156618652259269244717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11522875491536345692326289 8642156618652259269244717)
            ·
              refine ⟨3240808731994597225966769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8642156618652259269244717 3240808731994597225966769)
              ·
                refine ⟨2430606548995947919475077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240808731994597225966769 2430606548995947919475077)
                ·
                  refine ⟨455738727936740234901577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430606548995947919475077 455738727936740234901577)
                  ·
                    rfl

theorem cell21_1996983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_1996983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1996983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1996983 prefixEnd_1996983 := by exact prefixLift 1996983
  have htrace : WordTrace (prefixWord ++ tailWord_1996983) baseStart_1996983 baseEnd_1996983 := by
    simpa [prefixWord, tailWord_1996983, baseEnd_1996983] using wordTrace_append hprefix tailTrace_1996983
  have hstable : (prefixWord ++ tailWord_1996983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1996983).length < 2 ^ (prefixWord ++ tailWord_1996983).sum := by decide
  have hdescent : baseEnd_1996983 < baseStart_1996983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1996983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997020 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_1997020 : Nat := 118140960795 + 1997020 * 2 ^ 59
def prefixEnd_1997020 : Nat := 4983230072969 + 3 ^ 40 * 1997020 * 2
def baseEnd_1997020 : Nat := 455747171840836392784835

theorem tailTrace_1997020 : CollatzResearch.WordTrace tailWord_1997020 prefixEnd_1997020 455747171840836392784835 := by
  unfold tailWord_1997020
  simp only [CollatzResearch.WordTrace]
  refine ⟨36418651612572539353814257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48558202150096719138419009 36418651612572539353814257)
  ·
    refine ⟨27313988709429404515360693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36418651612572539353814257 27313988709429404515360693)
    ·
      refine ⟨2560686441509006673315065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27313988709429404515360693 2560686441509006673315065)
      ·
        refine ⟨1920514831131755004986299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2560686441509006673315065 1920514831131755004986299)
        ·
          refine ⟨2880772246697632507479449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1920514831131755004986299 2880772246697632507479449)
          ·
            refine ⟨2160579185023224380609587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880772246697632507479449 2160579185023224380609587)
            ·
              refine ⟨3240868777534836570914381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160579185023224380609587 3240868777534836570914381)
              ·
                refine ⟨1215325791575563714092893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3240868777534836570914381 1215325791575563714092893)
                ·
                  refine ⟨455747171840836392784835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215325791575563714092893 455747171840836392784835)
                  ·
                    rfl

theorem cell21_1997020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_1997020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997020 prefixEnd_1997020 := by exact prefixLift 1997020
  have htrace : WordTrace (prefixWord ++ tailWord_1997020) baseStart_1997020 baseEnd_1997020 := by
    simpa [prefixWord, tailWord_1997020, baseEnd_1997020] using wordTrace_append hprefix tailTrace_1997020
  have hstable : (prefixWord ++ tailWord_1997020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997020).length < 2 ^ (prefixWord ++ tailWord_1997020).sum := by decide
  have hdescent : baseEnd_1997020 < baseStart_1997020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997056 : List Nat := [2, 1, 1, 2, 1, 1, 5, 8]
def baseStart_1997056 : Nat := 118140960795 + 1997056 * 2 ^ 59
def prefixEnd_1997056 : Nat := 4983230072969 + 3 ^ 40 * 1997056 * 2
def baseEnd_1997056 : Nat := 151918462510436110061587

theorem tailTrace_1997056 : CollatzResearch.WordTrace tailWord_1997056 prefixEnd_1997056 151918462510436110061587 := by
  unfold tailWord_1997056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36419308126507328427969511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48559077502009771237292681 36419308126507328427969511)
  ·
    refine ⟨54628962189760992641954267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36419308126507328427969511 54628962189760992641954267)
    ·
      refine ⟨81943443284641488962931401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54628962189760992641954267 81943443284641488962931401)
      ·
        refine ⟨61457582463481116722198551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81943443284641488962931401 61457582463481116722198551)
        ·
          refine ⟨92186373695221675083297827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61457582463481116722198551 92186373695221675083297827)
          ·
            refine ⟨138279560542832512624946741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92186373695221675083297827 138279560542832512624946741)
            ·
              refine ⟨12963708800890548058588757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138279560542832512624946741 12963708800890548058588757)
              ·
                refine ⟨151918462510436110061587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12963708800890548058588757 151918462510436110061587)
                ·
                  rfl

theorem cell21_1997056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_1997056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997056 prefixEnd_1997056 := by exact prefixLift 1997056
  have htrace : WordTrace (prefixWord ++ tailWord_1997056) baseStart_1997056 baseEnd_1997056 := by
    simpa [prefixWord, tailWord_1997056, baseEnd_1997056] using wordTrace_append hprefix tailTrace_1997056
  have hstable : (prefixWord ++ tailWord_1997056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997056).length < 2 ^ (prefixWord ++ tailWord_1997056).sum := by decide
  have hdescent : baseEnd_1997056 < baseStart_1997056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997096 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_1997096 : Nat := 118140960795 + 1997096 * 2 ^ 59
def prefixEnd_1997096 : Nat := 4983230072969 + 3 ^ 40 * 1997096 * 2
def baseEnd_1997096 : Nat := 455764516076277149518013

theorem tailTrace_1997096 : CollatzResearch.WordTrace tailWord_1997096 prefixEnd_1997096 455764516076277149518013 := by
  unfold tailWord_1997096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36420037586434871843697571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48560050115246495791596761 36420037586434871843697571)
  ·
    refine ⟨54630056379652307765546357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36420037586434871843697571 54630056379652307765546357)
    ·
      refine ⟨5121567785592403853019971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54630056379652307765546357 5121567785592403853019971)
      ·
        refine ⟨7682351678388605779529957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121567785592403853019971 7682351678388605779529957)
        ·
          refine ⟨1440440939697863583661867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7682351678388605779529957 1440440939697863583661867)
          ·
            refine ⟨2160661409546795375492801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440440939697863583661867 2160661409546795375492801)
            ·
              refine ⟨1620496057160096531619601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2160661409546795375492801 1620496057160096531619601)
              ·
                refine ⟨1215372042870072398714701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1620496057160096531619601 1215372042870072398714701)
                ·
                  refine ⟨455764516076277149518013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215372042870072398714701 455764516076277149518013)
                  ·
                    rfl

theorem cell21_1997096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_1997096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997096 prefixEnd_1997096 := by exact prefixLift 1997096
  have htrace : WordTrace (prefixWord ++ tailWord_1997096) baseStart_1997096 baseEnd_1997096 := by
    simpa [prefixWord, tailWord_1997096, baseEnd_1997096] using wordTrace_append hprefix tailTrace_1997096
  have hstable : (prefixWord ++ tailWord_1997096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997096).length < 2 ^ (prefixWord ++ tailWord_1997096).sum := by decide
  have hdescent : baseEnd_1997096 < baseStart_1997096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997121 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 5]
def baseStart_1997121 : Nat := 118140960795 + 1997121 * 2 ^ 59
def prefixEnd_1997121 : Nat := 4983230072969 + 3 ^ 40 * 1997121 * 2
def baseEnd_1997121 : Nat := 455770221416882661601295

theorem tailTrace_1997121 : CollatzResearch.WordTrace tailWord_1997121 prefixEnd_1997121 455770221416882661601295 := by
  unfold tailWord_1997121
  simp only [CollatzResearch.WordTrace]
  refine ⟨72840986997779172957055217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48560657998519448638036811 72840986997779172957055217)
  ·
    refine ⟨54630740248334379717791413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72840986997779172957055217 54630740248334379717791413)
    ·
      refine ⟨5121631898281348098542945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54630740248334379717791413 5121631898281348098542945)
      ·
        refine ⟨3841223923711011073907209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121631898281348098542945 3841223923711011073907209)
        ·
          refine ⟨2880917942783258305430407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3841223923711011073907209 2880917942783258305430407)
          ·
            refine ⟨4321376914174887458145611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880917942783258305430407 4321376914174887458145611)
            ·
              refine ⟨6482065371262331187218417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321376914174887458145611 6482065371262331187218417)
              ·
                refine ⟨4861549028446748390413813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6482065371262331187218417 4861549028446748390413813)
                ·
                  refine ⟨455770221416882661601295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4861549028446748390413813 455770221416882661601295)
                  ·
                    rfl

theorem cell21_1997121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_1997121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997121 prefixEnd_1997121 := by exact prefixLift 1997121
  have htrace : WordTrace (prefixWord ++ tailWord_1997121) baseStart_1997121 baseEnd_1997121 := by
    simpa [prefixWord, tailWord_1997121, baseEnd_1997121] using wordTrace_append hprefix tailTrace_1997121
  have hstable : (prefixWord ++ tailWord_1997121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997121).length < 2 ^ (prefixWord ++ tailWord_1997121).sum := by decide
  have hdescent : baseEnd_1997121 < baseStart_1997121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997152 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_1997152 : Nat := 118140960795 + 1997152 * 2 ^ 59
def prefixEnd_1997152 : Nat := 4983230072969 + 3 ^ 40 * 1997152 * 2
def baseEnd_1997152 : Nat := 455777296039233496584565

theorem tailTrace_1997152 : CollatzResearch.WordTrace tailWord_1997152 prefixEnd_1997152 455777296039233496584565 := by
  unfold tailWord_1997152
  simp only [CollatzResearch.WordTrace]
  refine ⟨36421058830333432625716855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48561411773777910167622473 36421058830333432625716855)
  ·
    refine ⟨54631588245500148938575283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36421058830333432625716855 54631588245500148938575283)
    ·
      refine ⟨81947382368250223407862925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54631588245500148938575283 81947382368250223407862925)
      ·
        refine ⟨30730268388093833777948597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81947382368250223407862925 30730268388093833777948597)
        ·
          refine ⟨2880962661383796916682681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30730268388093833777948597 2880962661383796916682681)
          ·
            refine ⟨2160721996037847687512011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2880962661383796916682681 2160721996037847687512011)
            ·
              refine ⟨3241082994056771531268017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160721996037847687512011 3241082994056771531268017)
              ·
                refine ⟨2430812245542578648451013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241082994056771531268017 2430812245542578648451013)
                ·
                  refine ⟨455777296039233496584565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2430812245542578648451013 455777296039233496584565)
                  ·
                    rfl

theorem cell21_1997152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_1997152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997152 prefixEnd_1997152 := by exact prefixLift 1997152
  have htrace : WordTrace (prefixWord ++ tailWord_1997152) baseStart_1997152 baseEnd_1997152 := by
    simpa [prefixWord, tailWord_1997152, baseEnd_1997152] using wordTrace_append hprefix tailTrace_1997152
  have hstable : (prefixWord ++ tailWord_1997152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997152).length < 2 ^ (prefixWord ++ tailWord_1997152).sum := by decide
  have hdescent : baseEnd_1997152 < baseStart_1997152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997214 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1997214 : Nat := 118140960795 + 1997214 * 2 ^ 59
def prefixEnd_1997214 : Nat := 4983230072969 + 3 ^ 40 * 1997214 * 2
def baseEnd_1997214 : Nat := 455791445283935166551105

theorem tailTrace_1997214 : CollatzResearch.WordTrace tailWord_1997214 prefixEnd_1997214 455791445283935166551105 := by
  unfold tailWord_1997214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105547373305281230023837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48562919324294833226793797 9105547373305281230023837)
  ·
    refine ⟨3414580264989480461258939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9105547373305281230023837 3414580264989480461258939)
    ·
      refine ⟨5121870397484220691888409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414580264989480461258939 5121870397484220691888409)
      ·
        refine ⟨3841402798113165518916307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121870397484220691888409 3841402798113165518916307)
        ·
          refine ⟨5762104197169748278374461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841402798113165518916307 5762104197169748278374461)
          ·
            refine ⟨2160789073938655604390423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5762104197169748278374461 2160789073938655604390423)
            ·
              refine ⟨3241183610907983406585635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160789073938655604390423 3241183610907983406585635)
              ·
                refine ⟨4861775416361975109878453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241183610907983406585635 4861775416361975109878453)
                ·
                  refine ⟨455791445283935166551105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4861775416361975109878453 455791445283935166551105)
                  ·
                    rfl

theorem cell21_1997214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1997214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997214 prefixEnd_1997214 := by exact prefixLift 1997214
  have htrace : WordTrace (prefixWord ++ tailWord_1997214) baseStart_1997214 baseEnd_1997214 := by
    simpa [prefixWord, tailWord_1997214, baseEnd_1997214] using wordTrace_append hprefix tailTrace_1997214
  have hstable : (prefixWord ++ tailWord_1997214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997214).length < 2 ^ (prefixWord ++ tailWord_1997214).sum := by decide
  have hdescent : baseEnd_1997214 < baseStart_1997214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997366 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1997366 : Nat := 118140960795 + 1997366 * 2 ^ 59
def prefixEnd_1997366 : Nat := 4983230072969 + 3 ^ 40 * 1997366 * 2
def baseEnd_1997366 : Nat := 455826133754816680017461

theorem tailTrace_1997366 : CollatzResearch.WordTrace tailWord_1997366 prefixEnd_1997366 455826133754816680017461 := by
  unfold tailWord_1997366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4553120180118223737482747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48566615254594386533149301 4553120180118223737482747)
  ·
    refine ⟨6829680270177335606224121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4553120180118223737482747 6829680270177335606224121)
    ·
      refine ⟨5122260202633001704668091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6829680270177335606224121 5122260202633001704668091)
      ·
        refine ⟨7683390303949502557002137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122260202633001704668091 7683390303949502557002137)
        ·
          refine ⟨5762542727962126917751603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7683390303949502557002137 5762542727962126917751603)
          ·
            refine ⟨8643814091943190376627405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762542727962126917751603 8643814091943190376627405)
            ·
              refine ⟨3241430284478696391235277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8643814091943190376627405 3241430284478696391235277)
              ·
                refine ⟨1215536356679511146713229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3241430284478696391235277 1215536356679511146713229)
                ·
                  refine ⟨455826133754816680017461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215536356679511146713229 455826133754816680017461)
                  ·
                    rfl

theorem cell21_1997366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1997366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997366 prefixEnd_1997366 := by exact prefixLift 1997366
  have htrace : WordTrace (prefixWord ++ tailWord_1997366) baseStart_1997366 baseEnd_1997366 := by
    simpa [prefixWord, tailWord_1997366, baseEnd_1997366] using wordTrace_append hprefix tailTrace_1997366
  have hstable : (prefixWord ++ tailWord_1997366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997366).length < 2 ^ (prefixWord ++ tailWord_1997366).sum := by decide
  have hdescent : baseEnd_1997366 < baseStart_1997366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997377 : List Nat := [1, 2, 5, 1, 1, 4, 7]
def baseStart_1997377 : Nat := 118140960795 + 1997377 * 2 ^ 59
def prefixEnd_1997377 : Nat := 4983230072969 + 3 ^ 40 * 1997377 * 2
def baseEnd_1997377 : Nat := 50647627122742567259345

theorem tailTrace_1997377 : CollatzResearch.WordTrace tailWord_1997377 prefixEnd_1997377 50647627122742567259345 := by
  unfold tailWord_1997377
  simp only [CollatzResearch.WordTrace]
  refine ⟨72850324084851728678374385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48566882723234485785582923 72850324084851728678374385)
  ·
    refine ⟨54637743063638796508780789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72850324084851728678374385 54637743063638796508780789)
    ·
      refine ⟨5122288412216137172698199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54637743063638796508780789 5122288412216137172698199)
      ·
        refine ⟨7683432618324205759047299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122288412216137172698199 7683432618324205759047299)
        ·
          refine ⟨11525148927486308638570949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683432618324205759047299 11525148927486308638570949)
          ·
            refine ⟨2160965423903682869732053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11525148927486308638570949 2160965423903682869732053)
            ·
              refine ⟨50647627122742567259345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2160965423903682869732053 50647627122742567259345)
              ·
                rfl

theorem cell21_1997377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 7].length) (baseStart_1997377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997377 prefixEnd_1997377 := by exact prefixLift 1997377
  have htrace : WordTrace (prefixWord ++ tailWord_1997377) baseStart_1997377 baseEnd_1997377 := by
    simpa [prefixWord, tailWord_1997377, baseEnd_1997377] using wordTrace_append hprefix tailTrace_1997377
  have hstable : (prefixWord ++ tailWord_1997377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997377).length < 2 ^ (prefixWord ++ tailWord_1997377).sum := by decide
  have hdescent : baseEnd_1997377 < baseStart_1997377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997391 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 5]
def baseStart_1997391 : Nat := 118140960795 + 1997391 * 2 ^ 59
def prefixEnd_1997391 : Nat := 4983230072969 + 3 ^ 40 * 1997391 * 2
def baseEnd_1997391 : Nat := 455831839095422192100743

theorem tailTrace_1997391 : CollatzResearch.WordTrace tailWord_1997391 prefixEnd_1997391 455831839095422192100743 := by
  unfold tailWord_1997391
  simp only [CollatzResearch.WordTrace]
  refine ⟨72850834706801009069384027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48567223137867339379589351 72850834706801009069384027)
  ·
    refine ⟨109276252060201513604076041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72850834706801009069384027 109276252060201513604076041)
    ·
      refine ⟨81957189045151135203057031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109276252060201513604076041 81957189045151135203057031)
      ·
        refine ⟨122935783567726702804585547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81957189045151135203057031 122935783567726702804585547)
        ·
          refine ⟨184403675351590054206878321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122935783567726702804585547 184403675351590054206878321)
          ·
            refine ⟨138302756513692540655158741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184403675351590054206878321 138302756513692540655158741)
            ·
              refine ⟨3241470855789668921605283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 138302756513692540655158741 3241470855789668921605283)
              ·
                refine ⟨4862206283684503382407925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241470855789668921605283 4862206283684503382407925)
                ·
                  refine ⟨455831839095422192100743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4862206283684503382407925 455831839095422192100743)
                  ·
                    rfl

theorem cell21_1997391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_1997391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997391 prefixEnd_1997391 := by exact prefixLift 1997391
  have htrace : WordTrace (prefixWord ++ tailWord_1997391) baseStart_1997391 baseEnd_1997391 := by
    simpa [prefixWord, tailWord_1997391, baseEnd_1997391] using wordTrace_append hprefix tailTrace_1997391
  have hstable : (prefixWord ++ tailWord_1997391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997391).length < 2 ^ (prefixWord ++ tailWord_1997391).sum := by decide
  have hdescent : baseEnd_1997391 < baseStart_1997391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997470 : List Nat := [4, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1997470 : Nat := 118140960795 + 1997470 * 2 ^ 59
def prefixEnd_1997470 : Nat := 4983230072969 + 3 ^ 40 * 1997470 * 2
def baseEnd_1997470 : Nat := 151949955990578536761305

theorem tailTrace_1997470 : CollatzResearch.WordTrace tailWord_1997470 prefixEnd_1997470 151949955990578536761305 := by
  unfold tailWord_1997470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106714509189350695188733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48569144049009870374339909 9106714509189350695188733)
  ·
    refine ⟨3415017940946006510695775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9106714509189350695188733 3415017940946006510695775)
    ·
      refine ⟨5122526911419009766043663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415017940946006510695775 5122526911419009766043663)
      ·
        refine ⟨7683790367128514649065495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122526911419009766043663 7683790367128514649065495)
        ·
          refine ⟨11525685550692771973598243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683790367128514649065495 11525685550692771973598243)
          ·
            refine ⟨17288528326039157960397365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525685550692771973598243 17288528326039157960397365)
            ·
              refine ⟨1620799530566171058787253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17288528326039157960397365 1620799530566171058787253)
              ·
                refine ⟨151949955990578536761305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1620799530566171058787253 151949955990578536761305)
                ·
                  rfl

theorem cell21_1997470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1997470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997470 prefixEnd_1997470 := by exact prefixLift 1997470
  have htrace : WordTrace (prefixWord ++ tailWord_1997470) baseStart_1997470 baseEnd_1997470 := by
    simpa [prefixWord, tailWord_1997470, baseEnd_1997470] using wordTrace_append hprefix tailTrace_1997470
  have hstable : (prefixWord ++ tailWord_1997470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997470).length < 2 ^ (prefixWord ++ tailWord_1997470).sum := by decide
  have hdescent : baseEnd_1997470 < baseStart_1997470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997667 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 4]
def baseStart_1997667 : Nat := 118140960795 + 1997667 * 2 ^ 59
def prefixEnd_1997667 : Nat := 4983230072969 + 3 ^ 40 * 1997667 * 2
def baseEnd_1997667 : Nat := 455894826055707045500179

theorem tailTrace_1997667 : CollatzResearch.WordTrace tailWord_1997667 prefixEnd_1997667 455894826055707045500179 := by
  unfold tailWord_1997667
  simp only [CollatzResearch.WordTrace]
  refine ⟨72860901253801108206431255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48573934169200738804287503 72860901253801108206431255)
  ·
    refine ⟨109291351880701662309646883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72860901253801108206431255 109291351880701662309646883)
    ·
      refine ⟨163937027821052493464470325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109291351880701662309646883 163937027821052493464470325)
      ·
        refine ⟨15369096358223671262294093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163937027821052493464470325 15369096358223671262294093)
        ·
          refine ⟨5763411134333876723360285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15369096358223671262294093 5763411134333876723360285)
          ·
            refine ⟨2161279175375203771260107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5763411134333876723360285 2161279175375203771260107)
            ·
              refine ⟨3241918763062805656890161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161279175375203771260107 3241918763062805656890161)
              ·
                refine ⟨2431439072297104242667621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241918763062805656890161 2431439072297104242667621)
                ·
                  refine ⟨455894826055707045500179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431439072297104242667621 455894826055707045500179)
                  ·
                    rfl

theorem cell21_1997667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 4].length) (baseStart_1997667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997667 prefixEnd_1997667 := by exact prefixLift 1997667
  have htrace : WordTrace (prefixWord ++ tailWord_1997667) baseStart_1997667 baseEnd_1997667 := by
    simpa [prefixWord, tailWord_1997667, baseEnd_1997667] using wordTrace_append hprefix tailTrace_1997667
  have hstable : (prefixWord ++ tailWord_1997667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997667).length < 2 ^ (prefixWord ++ tailWord_1997667).sum := by decide
  have hdescent : baseEnd_1997667 < baseStart_1997667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997754 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1997754 : Nat := 118140960795 + 1997754 * 2 ^ 59
def prefixEnd_1997754 : Nat := 4983230072969 + 3 ^ 40 * 1997754 * 2
def baseEnd_1997754 : Nat := 455914680641014227550001

theorem tailTrace_1997754 : CollatzResearch.WordTrace tailWord_1997754 prefixEnd_1997754 455914680641014227550001 := by
  unfold tailWord_1997754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216018601121480516212079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48576049602990614709898877 18216018601121480516212079)
  ·
    refine ⟨27324027901682220774318119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18216018601121480516212079 27324027901682220774318119)
    ·
      refine ⟨40986041852523331161477179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27324027901682220774318119 40986041852523331161477179)
      ·
        refine ⟨61479062778784996742215769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40986041852523331161477179 61479062778784996742215769)
        ·
          refine ⟨46109297084088747556661827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61479062778784996742215769 46109297084088747556661827)
          ·
            refine ⟨69163945626133121334992741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46109297084088747556661827 69163945626133121334992741)
            ·
              refine ⟨12968239804899960250311139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69163945626133121334992741 12968239804899960250311139)
              ·
                refine ⟨19452359707349940375466709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968239804899960250311139 19452359707349940375466709)
                ·
                  refine ⟨455914680641014227550001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19452359707349940375466709 455914680641014227550001)
                  ·
                    rfl

theorem cell21_1997754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1997754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997754 prefixEnd_1997754 := by exact prefixLift 1997754
  have htrace : WordTrace (prefixWord ++ tailWord_1997754) baseStart_1997754 baseEnd_1997754 := by
    simpa [prefixWord, tailWord_1997754, baseEnd_1997754] using wordTrace_append hprefix tailTrace_1997754
  have hstable : (prefixWord ++ tailWord_1997754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997754).length < 2 ^ (prefixWord ++ tailWord_1997754).sum := by decide
  have hdescent : baseEnd_1997754 < baseStart_1997754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997802 : List Nat := [3, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1997802 : Nat := 118140960795 + 1997802 * 2 ^ 59
def prefixEnd_1997802 : Nat := 4983230072969 + 3 ^ 40 * 1997802 * 2
def baseEnd_1997802 : Nat := 455925634894976810749903

theorem tailTrace_1997802 : CollatzResearch.WordTrace tailWord_1997802 prefixEnd_1997802 455925634894976810749903 := by
  unfold tailWord_1997802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216456277078006565648915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48577216738874684175063773 18216456277078006565648915)
  ·
    refine ⟨27324684415617009848473373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18216456277078006565648915 27324684415617009848473373)
    ·
      refine ⟨10246756655856378693177515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27324684415617009848473373 10246756655856378693177515)
      ·
        refine ⟨15370134983784568039766273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10246756655856378693177515 15370134983784568039766273)
        ·
          refine ⟨11527601237838426029824705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15370134983784568039766273 11527601237838426029824705)
          ·
            refine ⟨8645700928378819522368529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11527601237838426029824705 8645700928378819522368529)
            ·
              refine ⟨6484275696284114641776397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8645700928378819522368529 6484275696284114641776397)
              ·
                refine ⟨2431603386106542990666149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6484275696284114641776397 2431603386106542990666149)
                ·
                  refine ⟨455925634894976810749903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431603386106542990666149 455925634894976810749903)
                  ·
                    rfl

theorem cell21_1997802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1997802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997802 prefixEnd_1997802 := by exact prefixLift 1997802
  have htrace : WordTrace (prefixWord ++ tailWord_1997802) baseStart_1997802 baseEnd_1997802 := by
    simpa [prefixWord, tailWord_1997802, baseEnd_1997802] using wordTrace_append hprefix tailTrace_1997802
  have hstable : (prefixWord ++ tailWord_1997802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997802).length < 2 ^ (prefixWord ++ tailWord_1997802).sum := by decide
  have hdescent : baseEnd_1997802 < baseStart_1997802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997822 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1997822 : Nat := 118140960795 + 1997822 * 2 ^ 59
def prefixEnd_1997822 : Nat := 4983230072969 + 3 ^ 40 * 1997822 * 2
def baseEnd_1997822 : Nat := 455930199167461220416529

theorem tailTrace_1997822 : CollatzResearch.WordTrace tailWord_1997822 prefixEnd_1997822 455930199167461220416529 := by
  unfold tailWord_1997822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108319321029946209790465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48577703045493046452215813 9108319321029946209790465)
  ·
    refine ⟨6831239490772459657342849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9108319321029946209790465 6831239490772459657342849)
    ·
      refine ⟨5123429618079344743007137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6831239490772459657342849 5123429618079344743007137)
      ·
        refine ⟨3842572213559508557255353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5123429618079344743007137 3842572213559508557255353)
        ·
          refine ⟨2881929160169631417941515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3842572213559508557255353 2881929160169631417941515)
          ·
            refine ⟨4322893740254447126912273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881929160169631417941515 4322893740254447126912273)
            ·
              refine ⟨3242170305190835345184205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322893740254447126912273 3242170305190835345184205)
              ·
                refine ⟨1215813864446563254444077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3242170305190835345184205 1215813864446563254444077)
                ·
                  refine ⟨455930199167461220416529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215813864446563254444077 455930199167461220416529)
                  ·
                    rfl

theorem cell21_1997822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1997822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997822 prefixEnd_1997822 := by exact prefixLift 1997822
  have htrace : WordTrace (prefixWord ++ tailWord_1997822) baseStart_1997822 baseEnd_1997822 := by
    simpa [prefixWord, tailWord_1997822, baseEnd_1997822] using wordTrace_append hprefix tailTrace_1997822
  have hstable : (prefixWord ++ tailWord_1997822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997822).length < 2 ^ (prefixWord ++ tailWord_1997822).sum := by decide
  have hdescent : baseEnd_1997822 < baseStart_1997822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997847 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 5]
def baseStart_1997847 : Nat := 118140960795 + 1997847 * 2 ^ 59
def prefixEnd_1997847 : Nat := 4983230072969 + 3 ^ 40 * 1997847 * 2
def baseEnd_1997847 : Nat := 455935904508066732499811

theorem tailTrace_1997847 : CollatzResearch.WordTrace tailWord_1997847 prefixEnd_1997847 455935904508066732499811 := by
  unfold tailWord_1997847
  simp only [CollatzResearch.WordTrace]
  refine ⟨72867466393148998947983795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48578310928765999298655863 72867466393148998947983795)
  ·
    refine ⟨109301199589723498421975693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72867466393148998947983795 109301199589723498421975693)
    ·
      refine ⟨40987949846146311908240885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109301199589723498421975693 40987949846146311908240885)
      ·
        refine ⟨3842620298076216741397583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40987949846146311908240885 3842620298076216741397583)
        ·
          refine ⟨5763930447114325112096375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842620298076216741397583 5763930447114325112096375)
          ·
            refine ⟨8645895670671487668144563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763930447114325112096375 8645895670671487668144563)
            ·
              refine ⟨12968843506007231502216845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645895670671487668144563 12968843506007231502216845)
              ·
                refine ⟨4863316314752711813331317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12968843506007231502216845 4863316314752711813331317)
                ·
                  refine ⟨455935904508066732499811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4863316314752711813331317 455935904508066732499811)
                  ·
                    rfl

theorem cell21_1997847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_1997847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997847 prefixEnd_1997847 := by exact prefixLift 1997847
  have htrace : WordTrace (prefixWord ++ tailWord_1997847) baseStart_1997847 baseEnd_1997847 := by
    simpa [prefixWord, tailWord_1997847, baseEnd_1997847] using wordTrace_append hprefix tailTrace_1997847
  have hstable : (prefixWord ++ tailWord_1997847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997847).length < 2 ^ (prefixWord ++ tailWord_1997847).sum := by decide
  have hdescent : baseEnd_1997847 < baseStart_1997847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997878 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1997878 : Nat := 118140960795 + 1997878 * 2 ^ 59
def prefixEnd_1997878 : Nat := 4983230072969 + 3 ^ 40 * 1997878 * 2
def baseEnd_1997878 : Nat := 455942979130417567483081

theorem tailTrace_1997878 : CollatzResearch.WordTrace tailWord_1997878 prefixEnd_1997878 455942979130417567483081 := by
  unfold tailWord_1997878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4554287316002293202647643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48579064704024460828241525 4554287316002293202647643)
  ·
    refine ⟨6831430974003439803971465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4554287316002293202647643 6831430974003439803971465)
    ·
      refine ⟨5123573230502579852978599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6831430974003439803971465 5123573230502579852978599)
      ·
        refine ⟨7685359845753869779467899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5123573230502579852978599 7685359845753869779467899)
        ·
          refine ⟨11528039768630804669201849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7685359845753869779467899 11528039768630804669201849)
          ·
            refine ⟨8646029826473103501901387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11528039768630804669201849 8646029826473103501901387)
            ·
              refine ⟨12969044739709655252852081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646029826473103501901387 12969044739709655252852081)
              ·
                refine ⟨9726783554782241439639061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12969044739709655252852081 9726783554782241439639061)
                ·
                  refine ⟨455942979130417567483081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9726783554782241439639061 455942979130417567483081)
                  ·
                    rfl

theorem cell21_1997878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1997878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997878 prefixEnd_1997878 := by exact prefixLift 1997878
  have htrace : WordTrace (prefixWord ++ tailWord_1997878) baseStart_1997878 baseEnd_1997878 := by
    simpa [prefixWord, tailWord_1997878, baseEnd_1997878] using wordTrace_append hprefix tailTrace_1997878
  have hstable : (prefixWord ++ tailWord_1997878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997878).length < 2 ^ (prefixWord ++ tailWord_1997878).sum := by decide
  have hdescent : baseEnd_1997878 < baseStart_1997878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997881 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 3]
def baseStart_1997881 : Nat := 118140960795 + 1997881 * 2 ^ 59
def prefixEnd_1997881 : Nat := 4983230072969 + 3 ^ 40 * 1997881 * 2
def baseEnd_1997881 : Nat := 455943663771290228933075

theorem tailTrace_1997881 : CollatzResearch.WordTrace tailWord_1997881 prefixEnd_1997881 455943663771290228933075 := by
  unfold tailWord_1997881
  simp only [CollatzResearch.WordTrace]
  refine ⟨72868706475025822754721497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48579137650017215169814331 72868706475025822754721497)
  ·
    refine ⟨54651529856269367066041123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72868706475025822754721497 54651529856269367066041123)
    ·
      refine ⟨81977294784404050599061685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54651529856269367066041123 81977294784404050599061685)
      ·
        refine ⟨7685371386037879743662033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81977294784404050599061685 7685371386037879743662033)
        ·
          refine ⟨5764028539528409807746525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7685371386037879743662033 5764028539528409807746525)
          ·
            refine ⟨2161510702323153677904947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5764028539528409807746525 2161510702323153677904947)
            ·
              refine ⟨3242266053484730516857421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161510702323153677904947 3242266053484730516857421)
              ·
                refine ⟨1215849770056773943821533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3242266053484730516857421 1215849770056773943821533)
                ·
                  refine ⟨455943663771290228933075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215849770056773943821533 455943663771290228933075)
                  ·
                    rfl

theorem cell21_1997881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_1997881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997881 prefixEnd_1997881 := by exact prefixLift 1997881
  have htrace : WordTrace (prefixWord ++ tailWord_1997881) baseStart_1997881 baseEnd_1997881 := by
    simpa [prefixWord, tailWord_1997881, baseEnd_1997881] using wordTrace_append hprefix tailTrace_1997881
  have hstable : (prefixWord ++ tailWord_1997881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997881).length < 2 ^ (prefixWord ++ tailWord_1997881).sum := by decide
  have hdescent : baseEnd_1997881 < baseStart_1997881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1997999 : List Nat := [1, 1, 2, 1, 2, 3, 3, 5, 3]
def baseStart_1997999 : Nat := 118140960795 + 1997999 * 2 ^ 59
def prefixEnd_1997999 : Nat := 4983230072969 + 3 ^ 40 * 1997999 * 2
def baseEnd_1997999 : Nat := 455970592978948245966167

theorem tailTrace_1997999 : CollatzResearch.WordTrace tailWord_1997999 prefixEnd_1997999 455970592978948245966167 := by
  unfold tailWord_1997999
  simp only [CollatzResearch.WordTrace]
  refine ⟨72873010288598328907517051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48582006859065552605011367 72873010288598328907517051)
  ·
    refine ⟨109309515432897493361275577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72873010288598328907517051 109309515432897493361275577)
    ·
      refine ⟨81982136574673120020956683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109309515432897493361275577 81982136574673120020956683)
      ·
        refine ⟨122973204862009680031435025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81982136574673120020956683 122973204862009680031435025)
        ·
          refine ⟨92229903646507260023576269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122973204862009680031435025 92229903646507260023576269)
          ·
            refine ⟨34586213867440222508841101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92229903646507260023576269 34586213867440222508841101)
            ·
              refine ⟨12969830200290083440815413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34586213867440222508841101 12969830200290083440815413)
              ·
                refine ⟨1215921581277195322576445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12969830200290083440815413 1215921581277195322576445)
                ·
                  refine ⟨455970592978948245966167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1215921581277195322576445 455970592978948245966167)
                  ·
                    rfl

theorem cell21_1997999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 3].length) (baseStart_1997999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1997999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1997999 prefixEnd_1997999 := by exact prefixLift 1997999
  have htrace : WordTrace (prefixWord ++ tailWord_1997999) baseStart_1997999 baseEnd_1997999 := by
    simpa [prefixWord, tailWord_1997999, baseEnd_1997999] using wordTrace_append hprefix tailTrace_1997999
  have hstable : (prefixWord ++ tailWord_1997999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1997999).length < 2 ^ (prefixWord ++ tailWord_1997999).sum := by decide
  have hdescent : baseEnd_1997999 < baseStart_1997999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1997999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998022 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1998022 : Nat := 118140960795 + 1998022 * 2 ^ 59
def prefixEnd_1998022 : Nat := 4983230072969 + 3 ^ 40 * 1998022 * 2
def baseEnd_1998022 : Nat := 455975841892305317082787

theorem tailTrace_1998022 : CollatzResearch.WordTrace tailWord_1998022 prefixEnd_1998022 455975841892305317082787 := by
  unfold tailWord_1998022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277307786484843869862635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48582566111676669223736213 2277307786484843869862635)
  ·
    refine ⟨3415961679727265804793953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2277307786484843869862635 3415961679727265804793953)
    ·
      refine ⟨2561971259795449353595465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3415961679727265804793953 2561971259795449353595465)
      ·
        refine ⟨1921478444846587015196599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2561971259795449353595465 1921478444846587015196599)
        ·
          refine ⟨2882217667269880522794899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921478444846587015196599 2882217667269880522794899)
          ·
            refine ⟨4323326500904820784192349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882217667269880522794899 4323326500904820784192349)
            ·
              refine ⟨1621247437839307794072131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4323326500904820784192349 1621247437839307794072131)
              ·
                refine ⟨2431871156758961691108197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1621247437839307794072131 2431871156758961691108197)
                ·
                  refine ⟨455975841892305317082787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431871156758961691108197 455975841892305317082787)
                  ·
                    rfl

theorem cell21_1998022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1998022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998022 prefixEnd_1998022 := by exact prefixLift 1998022
  have htrace : WordTrace (prefixWord ++ tailWord_1998022) baseStart_1998022 baseEnd_1998022 := by
    simpa [prefixWord, tailWord_1998022, baseEnd_1998022] using wordTrace_append hprefix tailTrace_1998022
  have hstable : (prefixWord ++ tailWord_1998022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998022).length < 2 ^ (prefixWord ++ tailWord_1998022).sum := by decide
  have hdescent : baseEnd_1998022 < baseStart_1998022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998089 : List Nat := [1, 2, 1, 1, 3, 3, 3, 3, 4]
def baseStart_1998089 : Nat := 118140960795 + 1998089 * 2 ^ 59
def prefixEnd_1998089 : Nat := 4983230072969 + 3 ^ 40 * 1998089 * 2
def baseEnd_1998089 : Nat := 455991132205128089465983

theorem tailTrace_1998089 : CollatzResearch.WordTrace tailWord_1998089 prefixEnd_1998089 455991132205128089465983 := by
  unfold tailWord_1998089
  simp only [CollatzResearch.WordTrace]
  refine ⟨72876292858272274278293321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48584195238848182852195547 72876292858272274278293321)
  ·
    refine ⟨54657219643704205708719991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72876292858272274278293321 54657219643704205708719991)
    ·
      refine ⟨81985829465556308563079987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54657219643704205708719991 81985829465556308563079987)
      ·
        refine ⟨122978744198334462844619981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81985829465556308563079987 122978744198334462844619981)
        ·
          refine ⟨46117029074375423566732493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122978744198334462844619981 46117029074375423566732493)
          ·
            refine ⟨17293885902890783837524685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46117029074375423566732493 17293885902890783837524685)
            ·
              refine ⟨6485207213584043939071757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17293885902890783837524685 6485207213584043939071757)
              ·
                refine ⟨2431952705094016477151909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6485207213584043939071757 2431952705094016477151909)
                ·
                  refine ⟨455991132205128089465983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2431952705094016477151909 455991132205128089465983)
                  ·
                    rfl

theorem cell21_1998089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_1998089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998089 prefixEnd_1998089 := by exact prefixLift 1998089
  have htrace : WordTrace (prefixWord ++ tailWord_1998089) baseStart_1998089 baseEnd_1998089 := by
    simpa [prefixWord, tailWord_1998089, baseEnd_1998089] using wordTrace_append hprefix tailTrace_1998089
  have hstable : (prefixWord ++ tailWord_1998089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998089).length < 2 ^ (prefixWord ++ tailWord_1998089).sum := by decide
  have hdescent : baseEnd_1998089 < baseStart_1998089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998103 : List Nat := [1, 1, 3, 4, 1, 1, 1, 9]
def baseStart_1998103 : Nat := 118140960795 + 1998103 * 2 ^ 59
def prefixEnd_1998103 : Nat := 4983230072969 + 3 ^ 40 * 1998103 * 2
def baseEnd_1998103 : Nat := 151998109065289058744207

theorem tailTrace_1998103 : CollatzResearch.WordTrace tailWord_1998103 prefixEnd_1998103 151998109065289058744207 := by
  unfold tailWord_1998103
  simp only [CollatzResearch.WordTrace]
  refine ⟨72876803480221554669302963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48584535653481036446201975 72876803480221554669302963)
  ·
    refine ⟨109315205220332332003954445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72876803480221554669302963 109315205220332332003954445)
    ·
      refine ⟨40993201957624624501482917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109315205220332332003954445 40993201957624624501482917)
      ·
        refine ⟨7686225367054617094028047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40993201957624624501482917 7686225367054617094028047)
        ·
          refine ⟨11529338050581925641042071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686225367054617094028047 11529338050581925641042071)
          ·
            refine ⟨17294007075872888461563107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529338050581925641042071 17294007075872888461563107)
            ·
              refine ⟨25941010613809332692344661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17294007075872888461563107 25941010613809332692344661)
              ·
                refine ⟨151998109065289058744207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25941010613809332692344661 151998109065289058744207)
                ·
                  rfl

theorem cell21_1998103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_1998103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998103 prefixEnd_1998103 := by exact prefixLift 1998103
  have htrace : WordTrace (prefixWord ++ tailWord_1998103) baseStart_1998103 baseEnd_1998103 := by
    simpa [prefixWord, tailWord_1998103, baseEnd_1998103] using wordTrace_append hprefix tailTrace_1998103
  have hstable : (prefixWord ++ tailWord_1998103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998103).length < 2 ^ (prefixWord ++ tailWord_1998103).sum := by decide
  have hdescent : baseEnd_1998103 < baseStart_1998103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998137 : List Nat := [1, 2, 1, 6, 2, 2, 1, 6]
def baseStart_1998137 : Nat := 118140960795 + 1998137 * 2 ^ 59
def prefixEnd_1998137 : Nat := 4983230072969 + 3 ^ 40 * 1998137 * 2
def baseEnd_1998137 : Nat := 152000695486363557555295

theorem tailTrace_1998137 : CollatzResearch.WordTrace tailWord_1998137 prefixEnd_1998137 152000695486363557555295 := by
  unfold tailWord_1998137
  simp only [CollatzResearch.WordTrace]
  refine ⟨72878043562098378476040665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48585362374732252317360443 72878043562098378476040665)
  ·
    refine ⟨54658532671573783857030499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72878043562098378476040665 54658532671573783857030499)
    ·
      refine ⟨81987799007360675785545749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54658532671573783857030499 81987799007360675785545749)
      ·
        refine ⟨3843178078470031677447457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81987799007360675785545749 3843178078470031677447457)
        ·
          refine ⟨2882383558852523758085593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3843178078470031677447457 2882383558852523758085593)
          ·
            refine ⟨2161787669139392818564195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2882383558852523758085593 2161787669139392818564195)
            ·
              refine ⟨3242681503709089227846293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2161787669139392818564195 3242681503709089227846293)
              ·
                refine ⟨152000695486363557555295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3242681503709089227846293 152000695486363557555295)
                ·
                  rfl

theorem cell21_1998137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 6].length) (baseStart_1998137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998137 prefixEnd_1998137 := by exact prefixLift 1998137
  have htrace : WordTrace (prefixWord ++ tailWord_1998137) baseStart_1998137 baseEnd_1998137 := by
    simpa [prefixWord, tailWord_1998137, baseEnd_1998137] using wordTrace_append hprefix tailTrace_1998137
  have hstable : (prefixWord ++ tailWord_1998137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998137).length < 2 ^ (prefixWord ++ tailWord_1998137).sum := by decide
  have hdescent : baseEnd_1998137 < baseStart_1998137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998179 : List Nat := [1, 1, 1, 5, 2, 3, 8]
def baseStart_1998179 : Nat := 118140960795 + 1998179 * 2 ^ 59
def prefixEnd_1998179 : Nat := 4983230072969 + 3 ^ 40 * 1998179 * 2
def baseEnd_1998179 : Nat := 50667963492367548107311

theorem tailTrace_1998179 : CollatzResearch.WordTrace tailWord_1998179 prefixEnd_1998179 50667963492367548107311 := by
  unfold tailWord_1998179
  simp only [CollatzResearch.WordTrace]
  refine ⟨72879575427946219649069591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48586383618630813099379727 72879575427946219649069591)
  ·
    refine ⟨109319363141919329473604387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72879575427946219649069591 109319363141919329473604387)
    ·
      refine ⟨163979044712878994210406581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109319363141919329473604387 163979044712878994210406581)
      ·
        refine ⟨15373035441832405707225617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163979044712878994210406581 15373035441832405707225617)
        ·
          refine ⟨11529776581374304280419213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15373035441832405707225617 11529776581374304280419213)
          ·
            refine ⟨4323666218015364105157205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11529776581374304280419213 4323666218015364105157205)
            ·
              refine ⟨50667963492367548107311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4323666218015364105157205 50667963492367548107311)
              ·
                rfl

theorem cell21_1998179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 8].length) (baseStart_1998179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998179 prefixEnd_1998179 := by exact prefixLift 1998179
  have htrace : WordTrace (prefixWord ++ tailWord_1998179) baseStart_1998179 baseEnd_1998179 := by
    simpa [prefixWord, tailWord_1998179, baseEnd_1998179] using wordTrace_append hprefix tailTrace_1998179
  have hstable : (prefixWord ++ tailWord_1998179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998179).length < 2 ^ (prefixWord ++ tailWord_1998179).sum := by decide
  have hdescent : baseEnd_1998179 < baseStart_1998179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998303 : List Nat := [1, 1, 2, 3, 3, 1, 3, 4, 3]
def baseStart_1998303 : Nat := 118140960795 + 1998303 * 2 ^ 59
def prefixEnd_1998303 : Nat := 4983230072969 + 3 ^ 40 * 1998303 * 2
def baseEnd_1998303 : Nat := 456039969920711272898879

theorem tailTrace_1998303 : CollatzResearch.WordTrace tailWord_1998303 prefixEnd_1998303 456039969920711272898879 := by
  unfold tailWord_1998303
  simp only [CollatzResearch.WordTrace]
  refine ⟨72884098079496988826583563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48589398719664659217722375 72884098079496988826583563)
  ·
    refine ⟨109326147119245483239875345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72884098079496988826583563 109326147119245483239875345)
    ·
      refine ⟨81994610339434112429906509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109326147119245483239875345 81994610339434112429906509)
      ·
        refine ⟨30747978877287792161214941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81994610339434112429906509 30747978877287792161214941)
        ·
          refine ⟨11530492078982922060455603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30747978877287792161214941 11530492078982922060455603)
          ·
            refine ⟨17295738118474383090683405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11530492078982922060455603 17295738118474383090683405)
            ·
              refine ⟨6485901794427893659006277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17295738118474383090683405 6485901794427893659006277)
              ·
                refine ⟨1216106586455230061063677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6485901794427893659006277 1216106586455230061063677)
                ·
                  refine ⟨456039969920711272898879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216106586455230061063677 456039969920711272898879)
                  ·
                    rfl

theorem cell21_1998303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 3].length) (baseStart_1998303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998303 prefixEnd_1998303 := by exact prefixLift 1998303
  have htrace : WordTrace (prefixWord ++ tailWord_1998303) baseStart_1998303 baseEnd_1998303 := by
    simpa [prefixWord, tailWord_1998303, baseEnd_1998303] using wordTrace_append hprefix tailTrace_1998303
  have hstable : (prefixWord ++ tailWord_1998303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998303).length < 2 ^ (prefixWord ++ tailWord_1998303).sum := by decide
  have hdescent : baseEnd_1998303 < baseStart_1998303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998345 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_1998345 : Nat := 118140960795 + 1998345 * 2 ^ 59
def prefixEnd_1998345 : Nat := 4983230072969 + 3 ^ 40 * 1998345 * 2
def baseEnd_1998345 : Nat := 456049554892928533198793

theorem tailTrace_1998345 : CollatzResearch.WordTrace tailWord_1998345 prefixEnd_1998345 456049554892928533198793 := by
  unfold tailWord_1998345
  simp only [CollatzResearch.WordTrace]
  refine ⟨72885629945344829999612489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48590419963563219999741659 72885629945344829999612489)
  ·
    refine ⟨54664222459008622499709367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72885629945344829999612489 54664222459008622499709367)
    ·
      refine ⟨81996333688512933749564051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54664222459008622499709367 81996333688512933749564051)
      ·
        refine ⟨122994500532769400624346077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81996333688512933749564051 122994500532769400624346077)
        ·
          refine ⟨46122937699788525234129779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122994500532769400624346077 46122937699788525234129779)
          ·
            refine ⟨69184406549682787851194669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46122937699788525234129779 69184406549682787851194669)
            ·
              refine ⟨25944152456131045444198001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69184406549682787851194669 25944152456131045444198001)
              ·
                refine ⟨19458114342098284083148501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25944152456131045444198001 19458114342098284083148501)
                ·
                  refine ⟨456049554892928533198793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19458114342098284083148501 456049554892928533198793)
                  ·
                    rfl

theorem cell21_1998345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_1998345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998345 prefixEnd_1998345 := by exact prefixLift 1998345
  have htrace : WordTrace (prefixWord ++ tailWord_1998345) baseStart_1998345 baseEnd_1998345 := by
    simpa [prefixWord, tailWord_1998345, baseEnd_1998345] using wordTrace_append hprefix tailTrace_1998345
  have hstable : (prefixWord ++ tailWord_1998345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998345).length < 2 ^ (prefixWord ++ tailWord_1998345).sum := by decide
  have hdescent : baseEnd_1998345 < baseStart_1998345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998413 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1998413 : Nat := 118140960795 + 1998413 * 2 ^ 59
def prefixEnd_1998413 : Nat := 4983230072969 + 3 ^ 40 * 1998413 * 2
def baseEnd_1998413 : Nat := 456065073419375526065321

theorem tailTrace_1998413 : CollatzResearch.WordTrace tailWord_1998413 prefixEnd_1998413 456065073419375526065321 := by
  unfold tailWord_1998413
  simp only [CollatzResearch.WordTrace]
  refine ⟨72888110109098477613087893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48592073406065651742058595 72888110109098477613087893)
  ·
    refine ⟨3416630161363991138113495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72888110109098477613087893 3416630161363991138113495)
    ·
      refine ⟨5124945242045986707170243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3416630161363991138113495 5124945242045986707170243)
      ·
        refine ⟨7687417863068980060755365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124945242045986707170243 7687417863068980060755365)
        ·
          refine ⟨1441390849325433761391631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7687417863068980060755365 1441390849325433761391631)
          ·
            refine ⟨2162086273988150642087447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441390849325433761391631 2162086273988150642087447)
            ·
              refine ⟨3243129410982225963131171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162086273988150642087447 3243129410982225963131171)
              ·
                refine ⟨4864694116473338944696757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243129410982225963131171 4864694116473338944696757)
                ·
                  refine ⟨456065073419375526065321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4864694116473338944696757 456065073419375526065321)
                  ·
                    rfl

theorem cell21_1998413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1998413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998413 prefixEnd_1998413 := by exact prefixLift 1998413
  have htrace : WordTrace (prefixWord ++ tailWord_1998413) baseStart_1998413 baseEnd_1998413 := by
    simpa [prefixWord, tailWord_1998413, baseEnd_1998413] using wordTrace_append hprefix tailTrace_1998413
  have hstable : (prefixWord ++ tailWord_1998413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998413).length < 2 ^ (prefixWord ++ tailWord_1998413).sum := by decide
  have hdescent : baseEnd_1998413 < baseStart_1998413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998469 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 4]
def baseStart_1998469 : Nat := 118140960795 + 1998469 * 2 ^ 59
def prefixEnd_1998469 : Nat := 4983230072969 + 3 ^ 40 * 1998469 * 2
def baseEnd_1998469 : Nat := 456077853382331873131873

theorem tailTrace_1998469 : CollatzResearch.WordTrace tailWord_1998469 prefixEnd_1998469 456077853382331873131873 := by
  unfold tailWord_1998469
  simp only [CollatzResearch.WordTrace]
  refine ⟨72890152596895599177126461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48593435064597066118084307 72890152596895599177126461)
  ·
    refine ⟨27333807223835849691422423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72890152596895599177126461 27333807223835849691422423)
    ·
      refine ⟨41000710835753774537133635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27333807223835849691422423 41000710835753774537133635)
      ·
        refine ⟨61501066253630661805700453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41000710835753774537133635 61501066253630661805700453)
        ·
          refine ⟨11531449922555749088568835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61501066253630661805700453 11531449922555749088568835)
          ·
            refine ⟨17297174883833623632853253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11531449922555749088568835 17297174883833623632853253)
            ·
              refine ⟨3243220290718804431159985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17297174883833623632853253 3243220290718804431159985)
              ·
                refine ⟨2432415218039103323369989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243220290718804431159985 2432415218039103323369989)
                ·
                  refine ⟨456077853382331873131873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432415218039103323369989 456077853382331873131873)
                  ·
                    rfl

theorem cell21_1998469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_1998469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998469 prefixEnd_1998469 := by exact prefixLift 1998469
  have htrace : WordTrace (prefixWord ++ tailWord_1998469) baseStart_1998469 baseEnd_1998469 := by
    simpa [prefixWord, tailWord_1998469, baseEnd_1998469] using wordTrace_append hprefix tailTrace_1998469
  have hstable : (prefixWord ++ tailWord_1998469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998469).length < 2 ^ (prefixWord ++ tailWord_1998469).sum := by decide
  have hdescent : baseEnd_1998469 < baseStart_1998469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998500 : List Nat := [2, 3, 1, 2, 2, 3, 3, 5]
def baseStart_1998500 : Nat := 118140960795 + 1998500 * 2 ^ 59
def prefixEnd_1998500 : Nat := 4983230072969 + 3 ^ 40 * 1998500 * 2
def baseEnd_1998500 : Nat := 152028309334894236038381

theorem tailTrace_1998500 : CollatzResearch.WordTrace tailWord_1998500 prefixEnd_1998500 152028309334894236038381 := by
  unfold tailWord_1998500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36445641629891645735752477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48594188839855527647669969 36445641629891645735752477)
  ·
    refine ⟨13667115611209367150907179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36445641629891645735752477 13667115611209367150907179)
    ·
      refine ⟨20500673416814050726360769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13667115611209367150907179 20500673416814050726360769)
      ·
        refine ⟨15375505062610538044770577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20500673416814050726360769 15375505062610538044770577)
        ·
          refine ⟨11531628796957903533577933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15375505062610538044770577 11531628796957903533577933)
          ·
            refine ⟨4324360798859213825091725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11531628796957903533577933 4324360798859213825091725)
            ·
              refine ⟨1621635299572205184409397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4324360798859213825091725 1621635299572205184409397)
              ·
                refine ⟨152028309334894236038381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1621635299572205184409397 152028309334894236038381)
                ·
                  rfl

theorem cell21_1998500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_1998500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998500 prefixEnd_1998500 := by exact prefixLift 1998500
  have htrace : WordTrace (prefixWord ++ tailWord_1998500) baseStart_1998500 baseEnd_1998500 := by
    simpa [prefixWord, tailWord_1998500, baseEnd_1998500] using wordTrace_append hprefix tailTrace_1998500
  have hstable : (prefixWord ++ tailWord_1998500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998500).length < 2 ^ (prefixWord ++ tailWord_1998500).sum := by decide
  have hdescent : baseEnd_1998500 < baseStart_1998500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998528 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_1998528 : Nat := 118140960795 + 1998528 * 2 ^ 59
def prefixEnd_1998528 : Nat := 4983230072969 + 3 ^ 40 * 1998528 * 2
def baseEnd_1998528 : Nat := 456091317986160881648419

theorem tailTrace_1998528 : CollatzResearch.WordTrace tailWord_1998528 prefixEnd_1998528 456091317986160881648419 := by
  unfold tailWord_1998528
  simp only [CollatzResearch.WordTrace]
  refine ⟨36446152251840926126762119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48594869669121234835682825 36446152251840926126762119)
  ·
    refine ⟨54669228377761389190143179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36446152251840926126762119 54669228377761389190143179)
    ·
      refine ⟨82003842566642083785214769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54669228377761389190143179 82003842566642083785214769)
      ·
        refine ⟨61502881924981562838911077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82003842566642083785214769 61502881924981562838911077)
        ·
          refine ⟨11531790360934043032295827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61502881924981562838911077 11531790360934043032295827)
          ·
            refine ⟨17297685541401064548443741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11531790360934043032295827 17297685541401064548443741)
            ·
              refine ⟨6486632078025399205666403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17297685541401064548443741 6486632078025399205666403)
              ·
                refine ⟨9729948117038098808499605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486632078025399205666403 9729948117038098808499605)
                ·
                  refine ⟨456091317986160881648419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9729948117038098808499605 456091317986160881648419)
                  ·
                    rfl

theorem cell21_1998528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_1998528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998528 prefixEnd_1998528 := by exact prefixLift 1998528
  have htrace : WordTrace (prefixWord ++ tailWord_1998528) baseStart_1998528 baseEnd_1998528 := by
    simpa [prefixWord, tailWord_1998528, baseEnd_1998528] using wordTrace_append hprefix tailTrace_1998528
  have hstable : (prefixWord ++ tailWord_1998528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998528).length < 2 ^ (prefixWord ++ tailWord_1998528).sum := by decide
  have hdescent : baseEnd_1998528 < baseStart_1998528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998669 : List Nat := [1, 6, 1, 2, 1, 2, 3, 5]
def baseStart_1998669 : Nat := 118140960795 + 1998669 * 2 ^ 59
def prefixEnd_1998669 : Nat := 4983230072969 + 3 ^ 40 * 1998669 * 2
def baseEnd_1998669 : Nat := 152041165369058656599377

theorem tailTrace_1998669 : CollatzResearch.WordTrace tailWord_1998669 prefixEnd_1998669 152041165369058656599377 := by
  unfold tailWord_1998669
  simp only [CollatzResearch.WordTrace]
  refine ⟨72897447196171033334407061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48598298130780688889604707 72897447196171033334407061)
  ·
    refine ⟨3417067837320517187550331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72897447196171033334407061 3417067837320517187550331)
    ·
      refine ⟨5125601755980775781325497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417067837320517187550331 5125601755980775781325497)
      ·
        refine ⟨3844201316985581835994123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5125601755980775781325497 3844201316985581835994123)
        ·
          refine ⟨5766301975478372753991185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844201316985581835994123 5766301975478372753991185)
          ·
            refine ⟨4324726481608779565493389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5766301975478372753991185 4324726481608779565493389)
            ·
              refine ⟨1621772430603292337060021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4324726481608779565493389 1621772430603292337060021)
              ·
                refine ⟨152041165369058656599377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1621772430603292337060021 152041165369058656599377)
                ·
                  rfl

theorem cell21_1998669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 5].length) (baseStart_1998669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998669 prefixEnd_1998669 := by exact prefixLift 1998669
  have htrace : WordTrace (prefixWord ++ tailWord_1998669) baseStart_1998669 baseEnd_1998669 := by
    simpa [prefixWord, tailWord_1998669, baseEnd_1998669] using wordTrace_append hprefix tailTrace_1998669
  have hstable : (prefixWord ++ tailWord_1998669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998669).length < 2 ^ (prefixWord ++ tailWord_1998669).sum := by decide
  have hdescent : baseEnd_1998669 < baseStart_1998669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998725 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1998725 : Nat := 118140960795 + 1998725 * 2 ^ 59
def prefixEnd_1998725 : Nat := 4983230072969 + 3 ^ 40 * 1998725 * 2
def baseEnd_1998725 : Nat := 456136276070132316864683

theorem tailTrace_1998725 : CollatzResearch.WordTrace tailWord_1998725 prefixEnd_1998725 456136276070132316864683 := by
  unfold tailWord_1998725
  simp only [CollatzResearch.WordTrace]
  refine ⟨72899489683968154898445629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48599659789312103265630419 72899489683968154898445629)
  ·
    refine ⟨27337308631488058086917111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72899489683968154898445629 27337308631488058086917111)
    ·
      refine ⟨41005962947232087130375667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27337308631488058086917111 41005962947232087130375667)
      ·
        refine ⟨61508944420848130695563501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41005962947232087130375667 61508944420848130695563501)
        ·
          refine ⟨23065854157818049010836313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61508944420848130695563501 23065854157818049010836313)
          ·
            refine ⟨17299390618363536758127235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23065854157818049010836313 17299390618363536758127235)
            ·
              refine ⟨25949085927545305137190853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299390618363536758127235 25949085927545305137190853)
              ·
                refine ⟨4865453611414744713223285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25949085927545305137190853 4865453611414744713223285)
                ·
                  refine ⟨456136276070132316864683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865453611414744713223285 456136276070132316864683)
                  ·
                    rfl

theorem cell21_1998725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1998725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998725 prefixEnd_1998725 := by exact prefixLift 1998725
  have htrace : WordTrace (prefixWord ++ tailWord_1998725) baseStart_1998725 baseEnd_1998725 := by
    simpa [prefixWord, tailWord_1998725, baseEnd_1998725] using wordTrace_append hprefix tailTrace_1998725
  have hstable : (prefixWord ++ tailWord_1998725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998725).length < 2 ^ (prefixWord ++ tailWord_1998725).sum := by decide
  have hdescent : baseEnd_1998725 < baseStart_1998725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998734 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_1998734 : Nat := 118140960795 + 1998734 * 2 ^ 59
def prefixEnd_1998734 : Nat := 4983230072969 + 3 ^ 40 * 1998734 * 2
def baseEnd_1998734 : Nat := 456138329992750301214665

theorem tailTrace_1998734 : CollatzResearch.WordTrace tailWord_1998734 prefixEnd_1998734 456138329992750301214665 := by
  unfold tailWord_1998734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112477242616943679440407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48599878627290366290348837 9112477242616943679440407)
  ·
    refine ⟨13668715863925415519160611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9112477242616943679440407 13668715863925415519160611)
    ·
      refine ⟨20503073795888123278740917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13668715863925415519160611 20503073795888123278740917)
      ·
        refine ⟨1922163168364511557381961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20503073795888123278740917 1922163168364511557381961)
        ·
          refine ⟨1441622376273383668036471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1922163168364511557381961 1441622376273383668036471)
          ·
            refine ⟨2162433564410075502054707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441622376273383668036471 2162433564410075502054707)
            ·
              refine ⟨3243650346615113253082061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162433564410075502054707 3243650346615113253082061)
              ·
                refine ⟨1216368879980667469905773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3243650346615113253082061 1216368879980667469905773)
                ·
                  refine ⟨456138329992750301214665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216368879980667469905773 456138329992750301214665)
                  ·
                    rfl

theorem cell21_1998734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_1998734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998734 prefixEnd_1998734 := by exact prefixLift 1998734
  have htrace : WordTrace (prefixWord ++ tailWord_1998734) baseStart_1998734 baseEnd_1998734 := by
    simpa [prefixWord, tailWord_1998734, baseEnd_1998734] using wordTrace_append hprefix tailTrace_1998734
  have hstable : (prefixWord ++ tailWord_1998734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998734).length < 2 ^ (prefixWord ++ tailWord_1998734).sum := by decide
  have hdescent : baseEnd_1998734 < baseStart_1998734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998756 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1998756 : Nat := 118140960795 + 1998756 * 2 ^ 59
def prefixEnd_1998756 : Nat := 4983230072969 + 3 ^ 40 * 1998756 * 2
def baseEnd_1998756 : Nat := 456143350692483151847953

theorem tailTrace_1998756 : CollatzResearch.WordTrace tailWord_1998756 prefixEnd_1998756 456143350692483151847953 := by
  unfold tailWord_1998756
  simp only [CollatzResearch.WordTrace]
  refine ⟨36450310173427923596412061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48600413564570564795216081 36450310173427923596412061)
  ·
    refine ⟨13668866315035471348654523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36450310173427923596412061 13668866315035471348654523)
    ·
      refine ⟨20503299472553207022981785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13668866315035471348654523 20503299472553207022981785)
      ·
        refine ⟨15377474604414905267236339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20503299472553207022981785 15377474604414905267236339)
        ·
          refine ⟨23066211906622357900854509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15377474604414905267236339 23066211906622357900854509)
          ·
            refine ⟨8649829464983384212820441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23066211906622357900854509 8649829464983384212820441)
            ·
              refine ⟨6487372098737538159615331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8649829464983384212820441 6487372098737538159615331)
              ·
                refine ⟨9731058148106307239422997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487372098737538159615331 9731058148106307239422997)
                ·
                  refine ⟨456143350692483151847953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9731058148106307239422997 456143350692483151847953)
                  ·
                    rfl

theorem cell21_1998756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1998756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998756 prefixEnd_1998756 := by exact prefixLift 1998756
  have htrace : WordTrace (prefixWord ++ tailWord_1998756) baseStart_1998756 baseEnd_1998756 := by
    simpa [prefixWord, tailWord_1998756, baseEnd_1998756] using wordTrace_append hprefix tailTrace_1998756
  have hstable : (prefixWord ++ tailWord_1998756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998756).length < 2 ^ (prefixWord ++ tailWord_1998756).sum := by decide
  have hdescent : baseEnd_1998756 < baseStart_1998756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998759 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 5]
def baseStart_1998759 : Nat := 118140960795 + 1998759 * 2 ^ 59
def prefixEnd_1998759 : Nat := 4983230072969 + 3 ^ 40 * 1998759 * 2
def baseEnd_1998759 : Nat := 456144035333355813297947

theorem tailTrace_1998759 : CollatzResearch.WordTrace tailWord_1998759 prefixEnd_1998759 456144035333355813297947 := by
  unfold tailWord_1998759
  simp only [CollatzResearch.WordTrace]
  refine ⟨72900729765844978705183331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48600486510563319136788887 72900729765844978705183331)
  ·
    refine ⟨109351094648767468057774997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72900729765844978705183331 109351094648767468057774997)
    ·
      refine ⟨5125832561660975065208203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109351094648767468057774997 5125832561660975065208203)
      ·
        refine ⟨7688748842491462597812305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125832561660975065208203 7688748842491462597812305)
        ·
          refine ⟨5766561631868596948359229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7688748842491462597812305 5766561631868596948359229)
          ·
            refine ⟨2162460611950723855634711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5766561631868596948359229 2162460611950723855634711)
            ·
              refine ⟨3243690917926085783452067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2162460611950723855634711 3243690917926085783452067)
              ·
                refine ⟨4865536376889128675178101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243690917926085783452067 4865536376889128675178101)
                ·
                  refine ⟨456144035333355813297947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865536376889128675178101 456144035333355813297947)
                  ·
                    rfl

theorem cell21_1998759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 5].length) (baseStart_1998759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998759 prefixEnd_1998759 := by exact prefixLift 1998759
  have htrace : WordTrace (prefixWord ++ tailWord_1998759) baseStart_1998759 baseEnd_1998759 := by
    simpa [prefixWord, tailWord_1998759, baseEnd_1998759] using wordTrace_append hprefix tailTrace_1998759
  have hstable : (prefixWord ++ tailWord_1998759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998759).length < 2 ^ (prefixWord ++ tailWord_1998759).sum := by decide
  have hdescent : baseEnd_1998759 < baseStart_1998759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998773 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 4]
def baseStart_1998773 : Nat := 118140960795 + 1998773 * 2 ^ 59
def prefixEnd_1998773 : Nat := 4983230072969 + 3 ^ 40 * 1998773 * 2
def baseEnd_1998773 : Nat := 456147230324094900064585

theorem tailTrace_1998773 : CollatzResearch.WordTrace tailWord_1998773 prefixEnd_1998773 456147230324094900064585 := by
  unfold tailWord_1998773
  simp only [CollatzResearch.WordTrace]
  refine ⟨72901240387794259096192973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48600826925196172730795315 72901240387794259096192973)
  ·
    refine ⟨27337965145422847161072365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72901240387794259096192973 27337965145422847161072365)
    ·
      refine ⟨10251736929533567685402137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27337965145422847161072365 10251736929533567685402137)
      ·
        refine ⟨7688802697150175764051603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10251736929533567685402137 7688802697150175764051603)
        ·
          refine ⟨11533204045725263646077405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688802697150175764051603 11533204045725263646077405)
          ·
            refine ⟨4324951517146973867279027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11533204045725263646077405 4324951517146973867279027)
            ·
              refine ⟨6487427275720460800918541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324951517146973867279027 6487427275720460800918541)
              ·
                refine ⟨2432785228395172800344453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6487427275720460800918541 2432785228395172800344453)
                ·
                  refine ⟨456147230324094900064585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432785228395172800344453 456147230324094900064585)
                  ·
                    rfl

theorem cell21_1998773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_1998773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998773 prefixEnd_1998773 := by exact prefixLift 1998773
  have htrace : WordTrace (prefixWord ++ tailWord_1998773) baseStart_1998773 baseEnd_1998773 := by
    simpa [prefixWord, tailWord_1998773, baseEnd_1998773] using wordTrace_append hprefix tailTrace_1998773
  have hstable : (prefixWord ++ tailWord_1998773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998773).length < 2 ^ (prefixWord ++ tailWord_1998773).sum := by decide
  have hdescent : baseEnd_1998773 < baseStart_1998773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998832 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_1998832 : Nat := 118140960795 + 1998832 * 2 ^ 59
def prefixEnd_1998832 : Nat := 4983230072969 + 3 ^ 40 * 1998832 * 2
def baseEnd_1998832 : Nat := 456160694927923908581131

theorem tailTrace_1998832 : CollatzResearch.WordTrace tailWord_1998832 prefixEnd_1998832 456160694927923908581131 := by
  unfold tailWord_1998832
  simp only [CollatzResearch.WordTrace]
  refine ⟨36451696147290256086295375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48602261529720341448393833 36451696147290256086295375)
  ·
    refine ⟨54677544220935384129443063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36451696147290256086295375 54677544220935384129443063)
    ·
      refine ⟨82016316331403076194164595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54677544220935384129443063 82016316331403076194164595)
      ·
        refine ⟨123024474497104614291246893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82016316331403076194164595 123024474497104614291246893)
        ·
          refine ⟨46134177936414230359217585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123024474497104614291246893 46134177936414230359217585)
          ·
            refine ⟨34600633452310672769413189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46134177936414230359217585 34600633452310672769413189)
            ·
              refine ⟨6487618772308251144264973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34600633452310672769413189 6487618772308251144264973)
              ·
                refine ⟨2432857039615594179099365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6487618772308251144264973 2432857039615594179099365)
                ·
                  refine ⟨456160694927923908581131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432857039615594179099365 456160694927923908581131)
                  ·
                    rfl

theorem cell21_1998832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_1998832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998832 prefixEnd_1998832 := by exact prefixLift 1998832
  have htrace : WordTrace (prefixWord ++ tailWord_1998832) baseStart_1998832 baseEnd_1998832 := by
    simpa [prefixWord, tailWord_1998832, baseEnd_1998832] using wordTrace_append hprefix tailTrace_1998832
  have hstable : (prefixWord ++ tailWord_1998832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998832).length < 2 ^ (prefixWord ++ tailWord_1998832).sum := by decide
  have hdescent : baseEnd_1998832 < baseStart_1998832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998894 : List Nat := [4, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1998894 : Nat := 118140960795 + 1998894 * 2 ^ 59
def prefixEnd_1998894 : Nat := 4983230072969 + 3 ^ 40 * 1998894 * 2
def baseEnd_1998894 : Nat := 456174844172625578547671

theorem tailTrace_1998894 : CollatzResearch.WordTrace tailWord_1998894 prefixEnd_1998894 456174844172625578547671 := by
  unfold tailWord_1998894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113206702544487095168467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48603769080237264507565157 9113206702544487095168467)
  ·
    refine ⟨13669810053816730642752701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113206702544487095168467 13669810053816730642752701)
    ·
      refine ⟨5126178770181273991032263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13669810053816730642752701 5126178770181273991032263)
      ·
        refine ⟨7689268155271910986548395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126178770181273991032263 7689268155271910986548395)
        ·
          refine ⟨11533902232907866479822593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689268155271910986548395 11533902232907866479822593)
          ·
            refine ⟨8650426674680899859866945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11533902232907866479822593 8650426674680899859866945)
            ·
              refine ⟨6487820006010674894900209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8650426674680899859866945 6487820006010674894900209)
              ·
                refine ⟨4865865004508006171175157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487820006010674894900209 4865865004508006171175157)
                ·
                  refine ⟨456174844172625578547671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865865004508006171175157 456174844172625578547671)
                  ·
                    rfl

theorem cell21_1998894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1998894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998894 prefixEnd_1998894 := by exact prefixLift 1998894
  have htrace : WordTrace (prefixWord ++ tailWord_1998894) baseStart_1998894 baseEnd_1998894 := by
    simpa [prefixWord, tailWord_1998894, baseEnd_1998894] using wordTrace_append hprefix tailTrace_1998894
  have hstable : (prefixWord ++ tailWord_1998894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998894).length < 2 ^ (prefixWord ++ tailWord_1998894).sum := by decide
  have hdescent : baseEnd_1998894 < baseStart_1998894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1998925 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1998925 : Nat := 118140960795 + 1998925 * 2 ^ 59
def prefixEnd_1998925 : Nat := 4983230072969 + 3 ^ 40 * 1998925 * 2
def baseEnd_1998925 : Nat := 456181918794976413530941

theorem tailTrace_1998925 : CollatzResearch.WordTrace tailWord_1998925 prefixEnd_1998925 456181918794976413530941 := by
  unfold tailWord_1998925
  simp only [CollatzResearch.WordTrace]
  refine ⟨72906784283243589055726229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48604522855495726037150819 72906784283243589055726229)
  ·
    refine ⟨3417505513277043236987167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72906784283243589055726229 3417505513277043236987167)
    ·
      refine ⟨5126258269915564855480751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417505513277043236987167 5126258269915564855480751)
      ·
        refine ⟨7689387404873347283221127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126258269915564855480751 7689387404873347283221127)
        ·
          refine ⟨11534081107310020924831691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689387404873347283221127 11534081107310020924831691)
          ·
            refine ⟨17301121660965031387247537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11534081107310020924831691 17301121660965031387247537)
            ·
              refine ⟨12975841245723773540435653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17301121660965031387247537 12975841245723773540435653)
              ·
                refine ⟨2432970233573207538831685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12975841245723773540435653 2432970233573207538831685)
                ·
                  refine ⟨456181918794976413530941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2432970233573207538831685 456181918794976413530941)
                  ·
                    rfl

theorem cell21_1998925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1998925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1998925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1998925 prefixEnd_1998925 := by exact prefixLift 1998925
  have htrace : WordTrace (prefixWord ++ tailWord_1998925) baseStart_1998925 baseEnd_1998925 := by
    simpa [prefixWord, tailWord_1998925, baseEnd_1998925] using wordTrace_append hprefix tailTrace_1998925
  have hstable : (prefixWord ++ tailWord_1998925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1998925).length < 2 ^ (prefixWord ++ tailWord_1998925).sum := by decide
  have hdescent : baseEnd_1998925 < baseStart_1998925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1998925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999088 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_1999088 : Nat := 118140960795 + 1999088 * 2 ^ 59
def prefixEnd_1999088 : Nat := 4983230072969 + 3 ^ 40 * 1999088 * 2
def baseEnd_1999088 : Nat := 456219117615724352313941

theorem tailTrace_1999088 : CollatzResearch.WordTrace tailWord_1999088 prefixEnd_1999088 456219117615724352313941 := by
  unfold tailWord_1999088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36456364690826533946954959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48608486254435378595939945 36456364690826533946954959)
  ·
    refine ⟨54684547036239800920432439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36456364690826533946954959 54684547036239800920432439)
    ·
      refine ⟨82026820554359701380648659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54684547036239800920432439 82026820554359701380648659)
      ·
        refine ⟨123040230831539552070972989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82026820554359701380648659 123040230831539552070972989)
        ·
          refine ⟨46140086561827332026614871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123040230831539552070972989 46140086561827332026614871)
          ·
            refine ⟨69210129842740998039922307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46140086561827332026614871 69210129842740998039922307)
            ·
              refine ⟨103815194764111497059883461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69210129842740998039922307 103815194764111497059883461)
              ·
                refine ⟨19465349018270905698728149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103815194764111497059883461 19465349018270905698728149)
                ·
                  refine ⟨456219117615724352313941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19465349018270905698728149 456219117615724352313941)
                  ·
                    rfl

theorem cell21_1999088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_1999088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999088 prefixEnd_1999088 := by exact prefixLift 1999088
  have htrace : WordTrace (prefixWord ++ tailWord_1999088) baseStart_1999088 baseEnd_1999088 := by
    simpa [prefixWord, tailWord_1999088, baseEnd_1999088] using wordTrace_append hprefix tailTrace_1999088
  have hstable : (prefixWord ++ tailWord_1999088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999088).length < 2 ^ (prefixWord ++ tailWord_1999088).sum := by decide
  have hdescent : baseEnd_1999088 < baseStart_1999088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999111 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 4]
def baseStart_1999111 : Nat := 118140960795 + 1999111 * 2 ^ 59
def prefixEnd_1999111 : Nat := 4983230072969 + 3 ^ 40 * 1999111 * 2
def baseEnd_1999111 : Nat := 456224366529081423430561

theorem tailTrace_1999111 : CollatzResearch.WordTrace tailWord_1999111 prefixEnd_1999111 456224366529081423430561 := by
  unfold tailWord_1999111
  simp only [CollatzResearch.WordTrace]
  refine ⟨72913568260569742821997187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48609045507046495214664791 72913568260569742821997187)
  ·
    refine ⟨109370352390854614232995781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72913568260569742821997187 109370352390854614232995781)
    ·
      refine ⟨20506941073285240168686709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109370352390854614232995781 20506941073285240168686709)
      ·
        refine ⟨1922525725620491265814379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20506941073285240168686709 1922525725620491265814379)
        ·
          refine ⟨2883788588430736898721569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922525725620491265814379 2883788588430736898721569)
          ·
            refine ⟨2162841441323052674041177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2883788588430736898721569 2162841441323052674041177)
            ·
              refine ⟨1622131080992289505530883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162841441323052674041177 1622131080992289505530883)
              ·
                refine ⟨2433196621488434258296325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622131080992289505530883 2433196621488434258296325)
                ·
                  refine ⟨456224366529081423430561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433196621488434258296325 456224366529081423430561)
                  ·
                    rfl

theorem cell21_1999111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 4].length) (baseStart_1999111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999111 prefixEnd_1999111 := by exact prefixLift 1999111
  have htrace : WordTrace (prefixWord ++ tailWord_1999111) baseStart_1999111 baseEnd_1999111 := by
    simpa [prefixWord, tailWord_1999111, baseEnd_1999111] using wordTrace_append hprefix tailTrace_1999111
  have hstable : (prefixWord ++ tailWord_1999111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999111).length < 2 ^ (prefixWord ++ tailWord_1999111).sum := by decide
  have hdescent : baseEnd_1999111 < baseStart_1999111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999153 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 4]
def baseStart_1999153 : Nat := 118140960795 + 1999153 * 2 ^ 59
def prefixEnd_1999153 : Nat := 4983230072969 + 3 ^ 40 * 1999153 * 2
def baseEnd_1999153 : Nat := 456233951501298683730475

theorem tailTrace_1999153 : CollatzResearch.WordTrace tailWord_1999153 prefixEnd_1999153 456233951501298683730475 := by
  unfold tailWord_1999153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72915100126417583995026113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48610066750945055996684075 72915100126417583995026113)
  ·
    refine ⟨54686325094813187996269585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72915100126417583995026113 54686325094813187996269585)
    ·
      refine ⟨41014743821109890997202189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54686325094813187996269585 41014743821109890997202189)
      ·
        refine ⟨15380528932916209123950821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41014743821109890997202189 15380528932916209123950821)
        ·
          refine ⟨2883849174921789210740779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15380528932916209123950821 2883849174921789210740779)
          ·
            refine ⟨4325773762382683816111169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883849174921789210740779 4325773762382683816111169)
            ·
              refine ⟨3244330321787012862083377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325773762382683816111169 3244330321787012862083377)
              ·
                refine ⟨2433247741340259646562533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244330321787012862083377 2433247741340259646562533)
                ·
                  refine ⟨456233951501298683730475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433247741340259646562533 456233951501298683730475)
                  ·
                    rfl

theorem cell21_1999153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_1999153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999153 prefixEnd_1999153 := by exact prefixLift 1999153
  have htrace : WordTrace (prefixWord ++ tailWord_1999153) baseStart_1999153 baseEnd_1999153 := by
    simpa [prefixWord, tailWord_1999153, baseEnd_1999153] using wordTrace_append hprefix tailTrace_1999153
  have hstable : (prefixWord ++ tailWord_1999153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999153).length < 2 ^ (prefixWord ++ tailWord_1999153).sum := by decide
  have hdescent : baseEnd_1999153 < baseStart_1999153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999156 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1999156 : Nat := 118140960795 + 1999156 * 2 ^ 59
def prefixEnd_1999156 : Nat := 4983230072969 + 3 ^ 40 * 1999156 * 2
def baseEnd_1999156 : Nat := 456234636142171345180469

theorem tailTrace_1999156 : CollatzResearch.WordTrace tailWord_1999156 prefixEnd_1999156 456234636142171345180469 := by
  unfold tailWord_1999156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36457604772703357753692661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48610139696937810338256881 36457604772703357753692661)
  ·
    refine ⟨3417900447440939789408687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36457604772703357753692661 3417900447440939789408687)
    ·
      refine ⟨5126850671161409684113031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417900447440939789408687 5126850671161409684113031)
      ·
        refine ⟨7690276006742114526169547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126850671161409684113031 7690276006742114526169547)
        ·
          refine ⟨11535414010113171789254321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690276006742114526169547 11535414010113171789254321)
          ·
            refine ⟨8651560507584878841940741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11535414010113171789254321 8651560507584878841940741)
            ·
              refine ⟨1622167595172164782863889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8651560507584878841940741 1622167595172164782863889)
              ·
                refine ⟨1216625696379123587147917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622167595172164782863889 1216625696379123587147917)
                ·
                  refine ⟨456234636142171345180469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216625696379123587147917 456234636142171345180469)
                  ·
                    rfl

theorem cell21_1999156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1999156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999156 prefixEnd_1999156 := by exact prefixLift 1999156
  have htrace : WordTrace (prefixWord ++ tailWord_1999156) baseStart_1999156 baseEnd_1999156 := by
    simpa [prefixWord, tailWord_1999156, baseEnd_1999156] using wordTrace_append hprefix tailTrace_1999156
  have hstable : (prefixWord ++ tailWord_1999156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999156).length < 2 ^ (prefixWord ++ tailWord_1999156).sum := by decide
  have hdescent : baseEnd_1999156 < baseStart_1999156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999209 : List Nat := [1, 2, 1, 1, 1, 3, 12]
def baseStart_1999209 : Nat := 118140960795 + 1999209 * 2 ^ 59
def prefixEnd_1999209 : Nat := 4983230072969 + 3 ^ 40 * 1999209 * 2
def baseEnd_1999209 : Nat := 50694081273806114533003

theorem tailTrace_1999209 : CollatzResearch.WordTrace tailWord_1999209 prefixEnd_1999209 50694081273806114533003 := by
  unfold tailWord_1999209
  simp only [CollatzResearch.WordTrace]
  refine ⟨72917142614214705559064681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48611428409476470372709787 72917142614214705559064681)
  ·
    refine ⟨54687856960661029169298511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72917142614214705559064681 54687856960661029169298511)
    ·
      refine ⟨82031785440991543753947767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54687856960661029169298511 82031785440991543753947767)
      ·
        refine ⟨123047678161487315630921651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82031785440991543753947767 123047678161487315630921651)
        ·
          refine ⟨184571517242230973446382477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123047678161487315630921651 184571517242230973446382477)
          ·
            refine ⟨69214318965836615042393429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184571517242230973446382477 69214318965836615042393429)
            ·
              refine ⟨50694081273806114533003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 69214318965836615042393429 50694081273806114533003)
              ·
                rfl

theorem cell21_1999209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 12].length) (baseStart_1999209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999209 prefixEnd_1999209 := by exact prefixLift 1999209
  have htrace : WordTrace (prefixWord ++ tailWord_1999209) baseStart_1999209 baseEnd_1999209 := by
    simpa [prefixWord, tailWord_1999209, baseEnd_1999209] using wordTrace_append hprefix tailTrace_1999209
  have hstable : (prefixWord ++ tailWord_1999209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999209).length < 2 ^ (prefixWord ++ tailWord_1999209).sum := by decide
  have hdescent : baseEnd_1999209 < baseStart_1999209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999212 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_1999212 : Nat := 118140960795 + 1999212 * 2 ^ 59
def prefixEnd_1999212 : Nat := 4983230072969 + 3 ^ 40 * 1999212 * 2
def baseEnd_1999212 : Nat := 456247416105127692247021

theorem tailTrace_1999212 : CollatzResearch.WordTrace tailWord_1999212 prefixEnd_1999212 456247416105127692247021 := by
  unfold tailWord_1999212
  simp only [CollatzResearch.WordTrace]
  refine ⟨36458626016601918535711945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48611501355469224714282593 36458626016601918535711945)
  ·
    refine ⟨27343969512451438901783959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36458626016601918535711945 27343969512451438901783959)
    ·
      refine ⟨41015954268677158352675939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27343969512451438901783959 41015954268677158352675939)
      ·
        refine ⟨61523931403015737529013909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41015954268677158352675939 61523931403015737529013909)
        ·
          refine ⟨2883934284516362696672527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61523931403015737529013909 2883934284516362696672527)
          ·
            refine ⟨4325901426774544045008791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883934284516362696672527 4325901426774544045008791)
            ·
              refine ⟨6488852140161816067513187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325901426774544045008791 6488852140161816067513187)
              ·
                refine ⟨9733278210242724101269781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488852140161816067513187 9733278210242724101269781)
                ·
                  refine ⟨456247416105127692247021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9733278210242724101269781 456247416105127692247021)
                  ·
                    rfl

theorem cell21_1999212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_1999212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999212 prefixEnd_1999212 := by exact prefixLift 1999212
  have htrace : WordTrace (prefixWord ++ tailWord_1999212) baseStart_1999212 baseEnd_1999212 := by
    simpa [prefixWord, tailWord_1999212, baseEnd_1999212] using wordTrace_append hprefix tailTrace_1999212
  have hstable : (prefixWord ++ tailWord_1999212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999212).length < 2 ^ (prefixWord ++ tailWord_1999212).sum := by decide
  have hdescent : baseEnd_1999212 < baseStart_1999212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999229 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1999229 : Nat := 118140960795 + 1999229 * 2 ^ 59
def prefixEnd_1999229 : Nat := 4983230072969 + 3 ^ 40 * 1999229 * 2
def baseEnd_1999229 : Nat := 456251295736739440463653

theorem tailTrace_1999229 : CollatzResearch.WordTrace tailWord_1999229 prefixEnd_1999229 456251295736739440463653 := by
  unfold tailWord_1999229
  simp only [CollatzResearch.WordTrace]
  refine ⟨72917872074142248974792741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48611914716094832649861827 72917872074142248974792741)
  ·
    refine ⟨13672101013901671682773639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72917872074142248974792741 13672101013901671682773639)
    ·
      refine ⟨20508151520852507524160459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13672101013901671682773639 20508151520852507524160459)
      ·
        refine ⟨30762227281278761286240689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20508151520852507524160459 30762227281278761286240689)
        ·
          refine ⟨23071670460959070964680517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30762227281278761286240689 23071670460959070964680517)
          ·
            refine ⟨4325938211429825805877597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23071670460959070964680517 4325938211429825805877597)
            ·
              refine ⟨1622226829286184677204099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4325938211429825805877597 1622226829286184677204099)
              ·
                refine ⟨2433340243929277015806149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622226829286184677204099 2433340243929277015806149)
                ·
                  refine ⟨456251295736739440463653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2433340243929277015806149 456251295736739440463653)
                  ·
                    rfl

theorem cell21_1999229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1999229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1999229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1999229 prefixEnd_1999229 := by exact prefixLift 1999229
  have htrace : WordTrace (prefixWord ++ tailWord_1999229) baseStart_1999229 baseEnd_1999229 := by
    simpa [prefixWord, tailWord_1999229, baseEnd_1999229] using wordTrace_append hprefix tailTrace_1999229
  have hstable : (prefixWord ++ tailWord_1999229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999229).length < 2 ^ (prefixWord ++ tailWord_1999229).sum := by decide
  have hdescent : baseEnd_1999229 < baseStart_1999229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
