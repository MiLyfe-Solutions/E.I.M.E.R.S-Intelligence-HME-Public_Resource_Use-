import V185TrunkScan23Chunk0333

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1973923 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 9]
def baseStart_1973923 : Nat := 118140960795 + 1973923 * 2 ^ 59
def prefixEnd_1973923 : Nat := 4983230072969 + 3 ^ 40 * 1973923 * 2
def baseEnd_1973923 : Nat := 112619030440553972320511

theorem tailTrace_1973923 : CollatzResearch.WordTrace tailWord_1973923 prefixEnd_1973923 112619030440553972320511 := by
  unfold tailWord_1973923
  simp only [CollatzResearch.WordTrace]
  refine ⟨71994886427821565054078423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47996590951881043369385615 71994886427821565054078423)
  ·
    refine ⟨107992329641732347581117635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71994886427821565054078423 107992329641732347581117635)
    ·
      refine ⟨161988494462598521371676453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107992329641732347581117635 161988494462598521371676453)
      ·
        refine ⟨30372842711737222757189335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161988494462598521371676453 30372842711737222757189335)
        ·
          refine ⟨45559264067605834135784003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30372842711737222757189335 45559264067605834135784003)
          ·
            refine ⟨68338896101408751203676005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45559264067605834135784003 68338896101408751203676005)
            ·
              refine ⟨12813543019014140850689251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68338896101408751203676005 12813543019014140850689251)
              ·
                refine ⟨19220314528521211276033877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12813543019014140850689251 19220314528521211276033877)
                ·
                  refine ⟨112619030440553972320511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19220314528521211276033877 112619030440553972320511)
                  ·
                    rfl

theorem cell23_1973923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 9].length) (baseStart_1973923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973923 prefixEnd_1973923 := by exact prefixLift 1973923
  have htrace : WordTrace (prefixWord ++ tailWord_1973923) baseStart_1973923 baseEnd_1973923 := by
    simpa [prefixWord, tailWord_1973923, baseEnd_1973923] using wordTrace_append hprefix tailTrace_1973923
  have hstable : (prefixWord ++ tailWord_1973923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973923).length < 2 ^ (prefixWord ++ tailWord_1973923).sum := by decide
  have hdescent : baseEnd_1973923 < baseStart_1973923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973987 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 1, 7]
def baseStart_1973987 : Nat := 118140960795 + 1973987 * 2 ^ 59
def prefixEnd_1973987 : Nat := 4983230072969 + 3 ^ 40 * 1973987 * 2
def baseEnd_1973987 : Nat := 337868045575624500161435

theorem tailTrace_1973987 : CollatzResearch.WordTrace tailWord_1973987 prefixEnd_1973987 337868045575624500161435 := by
  unfold tailWord_1973987
  simp only [CollatzResearch.WordTrace]
  refine ⟨71997220699589703984408215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47998147133059802656272143 71997220699589703984408215)
  ·
    refine ⟨107995831049384555976612323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71997220699589703984408215 107995831049384555976612323)
    ·
      refine ⟨161993746574076833964918485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107995831049384555976612323 161993746574076833964918485)
      ·
        refine ⟨3796728435329925796052777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 161993746574076833964918485 3796728435329925796052777)
        ·
          refine ⟨2847546326497444347039583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3796728435329925796052777 2847546326497444347039583)
          ·
            refine ⟨4271319489746166520559375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847546326497444347039583 4271319489746166520559375)
            ·
              refine ⟨6406979234619249780839063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271319489746166520559375 6406979234619249780839063)
              ·
                refine ⟨9610468851928874671258595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6406979234619249780839063 9610468851928874671258595)
                ·
                  refine ⟨14415703277893312006887893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9610468851928874671258595 14415703277893312006887893)
                  ·
                    refine ⟨337868045575624500161435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14415703277893312006887893 337868045575624500161435)
                    ·
                      rfl

theorem cell23_1973987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 7].length) (baseStart_1973987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973987 prefixEnd_1973987 := by exact prefixLift 1973987
  have htrace : WordTrace (prefixWord ++ tailWord_1973987) baseStart_1973987 baseEnd_1973987 := by
    simpa [prefixWord, tailWord_1973987, baseEnd_1973987] using wordTrace_append hprefix tailTrace_1973987
  have hstable : (prefixWord ++ tailWord_1973987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973987).length < 2 ^ (prefixWord ++ tailWord_1973987).sum := by decide
  have hdescent : baseEnd_1973987 < baseStart_1973987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1973991 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 5]
def baseStart_1973991 : Nat := 118140960795 + 1973991 * 2 ^ 59
def prefixEnd_1973991 : Nat := 4983230072969 + 3 ^ 40 * 1973991 * 2
def baseEnd_1973991 : Nat := 112622910072165720537143

theorem tailTrace_1973991 : CollatzResearch.WordTrace tailWord_1973991 prefixEnd_1973991 112622910072165720537143 := by
  unfold tailWord_1973991
  simp only [CollatzResearch.WordTrace]
  refine ⟨71997366591575212667553827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47998244394383475111702551 71997366591575212667553827)
  ·
    refine ⟨107996049887362819001330741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71997366591575212667553827 107996049887362819001330741)
    ·
      refine ⟨10124629676940264281374757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107996049887362819001330741 10124629676940264281374757)
      ·
        refine ⟨1898368064426299552757767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10124629676940264281374757 1898368064426299552757767)
        ·
          refine ⟨2847552096639449329136651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898368064426299552757767 2847552096639449329136651)
          ·
            refine ⟨4271328144959173993704977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847552096639449329136651 4271328144959173993704977)
            ·
              refine ⟨3203496108719380495278733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271328144959173993704977 3203496108719380495278733)
              ·
                refine ⟨1201311040769767685729525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3203496108719380495278733 1201311040769767685729525)
                ·
                  refine ⟨112622910072165720537143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1201311040769767685729525 112622910072165720537143)
                  ·
                    rfl

theorem cell23_1973991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 5].length) (baseStart_1973991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1973991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1973991 prefixEnd_1973991 := by exact prefixLift 1973991
  have htrace : WordTrace (prefixWord ++ tailWord_1973991) baseStart_1973991 baseEnd_1973991 := by
    simpa [prefixWord, tailWord_1973991, baseEnd_1973991] using wordTrace_append hprefix tailTrace_1973991
  have hstable : (prefixWord ++ tailWord_1973991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1973991).length < 2 ^ (prefixWord ++ tailWord_1973991).sum := by decide
  have hdescent : baseEnd_1973991 < baseStart_1973991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1973991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974007 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 2, 4, 2]
def baseStart_1974007 : Nat := 118140960795 + 1974007 * 2 ^ 59
def prefixEnd_1974007 : Nat := 4983230072969 + 3 ^ 40 * 1974007 * 2
def baseEnd_1974007 : Nat := 1013614406339963422234213

theorem tailTrace_1974007 : CollatzResearch.WordTrace tailWord_1974007 prefixEnd_1974007 1013614406339963422234213 := by
  unfold tailWord_1974007
  simp only [CollatzResearch.WordTrace]
  refine ⟨71997950159517247400136275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47998633439678164933424183 71997950159517247400136275)
  ·
    refine ⟨107996925239275871100204413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71997950159517247400136275 107996925239275871100204413)
    ·
      refine ⟨40498846964728451662576655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107996925239275871100204413 40498846964728451662576655)
      ·
        refine ⟨60748270447092677493864983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40498846964728451662576655 60748270447092677493864983)
        ·
          refine ⟨91122405670639016240797475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60748270447092677493864983 91122405670639016240797475)
          ·
            refine ⟨136683608505958524361196213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91122405670639016240797475 136683608505958524361196213)
            ·
              refine ⟨12814088297433611658862145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136683608505958524361196213 12814088297433611658862145)
              ·
                refine ⟨9610566223075208744146609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12814088297433611658862145 9610566223075208744146609)
                ·
                  refine ⟨7207924667306406558109957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9610566223075208744146609 7207924667306406558109957)
                  ·
                    refine ⟨1351485875119951229645617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7207924667306406558109957 1351485875119951229645617)
                    ·
                      refine ⟨1013614406339963422234213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351485875119951229645617 1013614406339963422234213)
                      ·
                        rfl

theorem cell23_1974007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_1974007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974007 prefixEnd_1974007 := by exact prefixLift 1974007
  have htrace : WordTrace (prefixWord ++ tailWord_1974007) baseStart_1974007 baseEnd_1974007 := by
    simpa [prefixWord, tailWord_1974007, baseEnd_1974007] using wordTrace_append hprefix tailTrace_1974007
  have hstable : (prefixWord ++ tailWord_1974007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974007).length < 2 ^ (prefixWord ++ tailWord_1974007).sum := by decide
  have hdescent : baseEnd_1974007 < baseStart_1974007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974017 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1974017 : Nat := 118140960795 + 1974017 * 2 ^ 59
def prefixEnd_1974017 : Nat := 4983230072969 + 3 ^ 40 * 1974017 * 2
def baseEnd_1974017 : Nat := 337873180382169461036389

theorem tailTrace_1974017 : CollatzResearch.WordTrace tailWord_1974017 prefixEnd_1974017 337873180382169461036389 := by
  unfold tailWord_1974017
  simp only [CollatzResearch.WordTrace]
  refine ⟨71998314889481019108000305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47998876592987346072000203 71998314889481019108000305)
  ·
    refine ⟨53998736167110764331000229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71998314889481019108000305 53998736167110764331000229)
    ·
      refine ⟨10124763031333268312062543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53998736167110764331000229 10124763031333268312062543)
      ·
        refine ⟨15187144546999902468093815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10124763031333268312062543 15187144546999902468093815)
        ·
          refine ⟨22780716820499853702140723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15187144546999902468093815 22780716820499853702140723)
          ·
            refine ⟨34171075230749780553211085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22780716820499853702140723 34171075230749780553211085)
            ·
              refine ⟨12814153211531167707454157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34171075230749780553211085 12814153211531167707454157)
              ·
                refine ⟨4805307454324187890295309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12814153211531167707454157 4805307454324187890295309)
                ·
                  refine ⟨1801990295371570458860741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4805307454324187890295309 1801990295371570458860741)
                  ·
                    refine ⟨337873180382169461036389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1801990295371570458860741 337873180382169461036389)
                    ·
                      rfl

theorem cell23_1974017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1974017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974017 prefixEnd_1974017 := by exact prefixLift 1974017
  have htrace : WordTrace (prefixWord ++ tailWord_1974017) baseStart_1974017 baseEnd_1974017 := by
    simpa [prefixWord, tailWord_1974017, baseEnd_1974017] using wordTrace_append hprefix tailTrace_1974017
  have hstable : (prefixWord ++ tailWord_1974017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974017).length < 2 ^ (prefixWord ++ tailWord_1974017).sum := by decide
  have hdescent : baseEnd_1974017 < baseStart_1974017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974080 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1974080 : Nat := 118140960795 + 1974080 * 2 ^ 59
def prefixEnd_1974080 : Nat := 4983230072969 + 3 ^ 40 * 1974080 * 2
def baseEnd_1974080 : Nat := 1013651890427741636621377

theorem tailTrace_1974080 : CollatzResearch.WordTrace tailWord_1974080 prefixEnd_1974080 1013651890427741636621377 := by
  unfold tailWord_1974080
  simp only [CollatzResearch.WordTrace]
  refine ⟨36000306344126390433771847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48000408458835187245029129 36000306344126390433771847)
  ·
    refine ⟨54000459516189585650657771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36000306344126390433771847 54000459516189585650657771)
    ·
      refine ⟨81000689274284378475986657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54000459516189585650657771 81000689274284378475986657)
      ·
        refine ⟨60750516955713283856989993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81000689274284378475986657 60750516955713283856989993)
        ·
          refine ⟨45562887716784962892742495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60750516955713283856989993 45562887716784962892742495)
          ·
            refine ⟨68344331575177444339113743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45562887716784962892742495 68344331575177444339113743)
            ·
              refine ⟨102516497362766166508670615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68344331575177444339113743 102516497362766166508670615)
              ·
                refine ⟨153774746044149249763005923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102516497362766166508670615 153774746044149249763005923)
                ·
                  refine ⟨230662119066223874644508885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153774746044149249763005923 230662119066223874644508885)
                  ·
                    refine ⟨5406143415614622061980677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 230662119066223874644508885 5406143415614622061980677)
                    ·
                      refine ⟨1013651890427741636621377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5406143415614622061980677 1013651890427741636621377)
                      ·
                        rfl

theorem cell23_1974080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1974080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974080 prefixEnd_1974080 := by exact prefixLift 1974080
  have htrace : WordTrace (prefixWord ++ tailWord_1974080) baseStart_1974080 baseEnd_1974080 := by
    simpa [prefixWord, tailWord_1974080, baseEnd_1974080] using wordTrace_append hprefix tailTrace_1974080
  have hstable : (prefixWord ++ tailWord_1974080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974080).length < 2 ^ (prefixWord ++ tailWord_1974080).sum := by decide
  have hdescent : baseEnd_1974080 < baseStart_1974080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974101 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1974101 : Nat := 118140960795 + 1974101 * 2 ^ 59
def prefixEnd_1974101 : Nat := 4983230072969 + 3 ^ 40 * 1974101 * 2
def baseEnd_1974101 : Nat := 1013662673521486054458781

theorem tailTrace_1974101 : CollatzResearch.WordTrace tailWord_1974101 prefixEnd_1974101 1013662673521486054458781 := by
  unfold tailWord_1974101
  simp only [CollatzResearch.WordTrace]
  refine ⟨72001378621176701454058157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48000919080784467636038771 72001378621176701454058157)
  ·
    refine ⟨27000516982941263045271809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72001378621176701454058157 27000516982941263045271809)
    ·
      refine ⟨20250387737205947283953857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27000516982941263045271809 20250387737205947283953857)
      ·
        refine ⟨15187790802904460462965393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20250387737205947283953857 15187790802904460462965393)
        ·
          refine ⟨11390843102178345347224045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15187790802904460462965393 11390843102178345347224045)
          ·
            refine ⟨4271566163316879505209017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11390843102178345347224045 4271566163316879505209017)
            ·
              refine ⟨3203674622487659628906763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271566163316879505209017 3203674622487659628906763)
              ·
                refine ⟨4805511933731489443360145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203674622487659628906763 4805511933731489443360145)
                ·
                  refine ⟨3604133950298617082520109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4805511933731489443360145 3604133950298617082520109)
                  ·
                    refine ⟨1351550231361981405945041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3604133950298617082520109 1351550231361981405945041)
                    ·
                      refine ⟨1013662673521486054458781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351550231361981405945041 1013662673521486054458781)
                      ·
                        rfl

theorem cell23_1974101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1974101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974101 prefixEnd_1974101 := by exact prefixLift 1974101
  have htrace : WordTrace (prefixWord ++ tailWord_1974101) baseStart_1974101 baseEnd_1974101 := by
    simpa [prefixWord, tailWord_1974101, baseEnd_1974101] using wordTrace_append hprefix tailTrace_1974101
  have hstable : (prefixWord ++ tailWord_1974101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974101).length < 2 ^ (prefixWord ++ tailWord_1974101).sum := by decide
  have hdescent : baseEnd_1974101 < baseStart_1974101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974124 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_1974124 : Nat := 118140960795 + 1974124 * 2 ^ 59
def prefixEnd_1974124 : Nat := 4983230072969 + 3 ^ 40 * 1974124 * 2
def baseEnd_1974124 : Nat := 337891494525513154823725

theorem tailTrace_1974124 : CollatzResearch.WordTrace tailWord_1974124 prefixEnd_1974124 337891494525513154823725 := by
  unfold tailWord_1974124
  simp only [CollatzResearch.WordTrace]
  refine ⟨36001108750046688191072713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48001478333395584254763617 36001108750046688191072713)
  ·
    refine ⟨27000831562535016143304535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36001108750046688191072713 27000831562535016143304535)
    ·
      refine ⟨40501247343802524214956803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27000831562535016143304535 40501247343802524214956803)
      ·
        refine ⟨60751871015703786322435205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40501247343802524214956803 60751871015703786322435205)
        ·
          refine ⟨11390975815444459935456601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60751871015703786322435205 11390975815444459935456601)
          ·
            refine ⟨8543231861583344951592451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11390975815444459935456601 8543231861583344951592451)
            ·
              refine ⟨12814847792375017427388677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8543231861583344951592451 12814847792375017427388677)
              ·
                refine ⟨2402783961070315767635377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12814847792375017427388677 2402783961070315767635377)
                ·
                  refine ⟨1802087970802736825726533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2402783961070315767635377 1802087970802736825726533)
                  ·
                    refine ⟨337891494525513154823725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1802087970802736825726533 337891494525513154823725)
                    ·
                      rfl

theorem cell23_1974124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_1974124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974124 prefixEnd_1974124 := by exact prefixLift 1974124
  have htrace : WordTrace (prefixWord ++ tailWord_1974124) baseStart_1974124 baseEnd_1974124 := by
    simpa [prefixWord, tailWord_1974124, baseEnd_1974124] using wordTrace_append hprefix tailTrace_1974124
  have hstable : (prefixWord ++ tailWord_1974124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974124).length < 2 ^ (prefixWord ++ tailWord_1974124).sum := by decide
  have hdescent : baseEnd_1974124 < baseStart_1974124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974168 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1974168 : Nat := 118140960795 + 1974168 * 2 ^ 59
def prefixEnd_1974168 : Nat := 4983230072969 + 3 ^ 40 * 1974168 * 2
def baseEnd_1974168 : Nat := 1013697076725337292320973

theorem tailTrace_1974168 : CollatzResearch.WordTrace tailWord_1974168 prefixEnd_1974168 1013697076725337292320973 := by
  unfold tailWord_1974168
  simp only [CollatzResearch.WordTrace]
  refine ⟨36001911155966985948373579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48002548207955981264498105 36001911155966985948373579)
  ·
    refine ⟨54002866733950478922560369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36001911155966985948373579 54002866733950478922560369)
    ·
      refine ⟨40502150050462859191920277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54002866733950478922560369 40502150050462859191920277)
      ·
        refine ⟨1898538283615446524621263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40502150050462859191920277 1898538283615446524621263)
        ·
          refine ⟨2847807425423169786931895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898538283615446524621263 2847807425423169786931895)
          ·
            refine ⟨4271711138134754680397843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847807425423169786931895 4271711138134754680397843)
            ·
              refine ⟨6407566707202132020596765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271711138134754680397843 6407566707202132020596765)
              ·
                refine ⟨2402837515200799507723787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6407566707202132020596765 2402837515200799507723787)
                ·
                  refine ⟨3604256272801199261585681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2402837515200799507723787 3604256272801199261585681)
                  ·
                    refine ⟨2703192204600899446189261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604256272801199261585681 2703192204600899446189261)
                    ·
                      refine ⟨1013697076725337292320973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2703192204600899446189261 1013697076725337292320973)
                      ·
                        rfl

theorem cell23_1974168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1974168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974168 prefixEnd_1974168 := by exact prefixLift 1974168
  have htrace : WordTrace (prefixWord ++ tailWord_1974168) baseStart_1974168 baseEnd_1974168 := by
    simpa [prefixWord, tailWord_1974168, baseEnd_1974168] using wordTrace_append hprefix tailTrace_1974168
  have hstable : (prefixWord ++ tailWord_1974168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974168).length < 2 ^ (prefixWord ++ tailWord_1974168).sum := by decide
  have hdescent : baseEnd_1974168 < baseStart_1974168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974207 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_1974207 : Nat := 118140960795 + 1974207 * 2 ^ 59
def prefixEnd_1974207 : Nat := 4983230072969 + 3 ^ 40 * 1974207 * 2
def baseEnd_1974207 : Nat := 1013717102470862639733293

theorem tailTrace_1974207 : CollatzResearch.WordTrace tailWord_1974207 prefixEnd_1974207 1013717102470862639733293 := by
  unfold tailWord_1974207
  simp only [CollatzResearch.WordTrace]
  refine ⟨72005244758792681557416875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48003496505861787704944583 72005244758792681557416875)
  ·
    refine ⟨108007867138189022336125313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72005244758792681557416875 108007867138189022336125313)
    ·
      refine ⟨81005900353641766752093985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108007867138189022336125313 81005900353641766752093985)
      ·
        refine ⟨60754425265231325064070489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81005900353641766752093985 60754425265231325064070489)
        ·
          refine ⟨45565818948923493798052867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60754425265231325064070489 45565818948923493798052867)
          ·
            refine ⟨68348728423385240697079301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45565818948923493798052867 68348728423385240697079301)
            ·
              refine ⟨12815386579384732630702369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68348728423385240697079301 12815386579384732630702369)
              ·
                refine ⟨9611539934538549473026777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12815386579384732630702369 9611539934538549473026777)
                ·
                  refine ⟨7208654950903912104770083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9611539934538549473026777 7208654950903912104770083)
                  ·
                    refine ⟨10812982426355868157155125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7208654950903912104770083 10812982426355868157155125)
                    ·
                      refine ⟨1013717102470862639733293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10812982426355868157155125 1013717102470862639733293)
                      ·
                        rfl

theorem cell23_1974207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_1974207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974207 prefixEnd_1974207 := by exact prefixLift 1974207
  have htrace : WordTrace (prefixWord ++ tailWord_1974207) baseStart_1974207 baseEnd_1974207 := by
    simpa [prefixWord, tailWord_1974207, baseEnd_1974207] using wordTrace_append hprefix tailTrace_1974207
  have hstable : (prefixWord ++ tailWord_1974207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974207).length < 2 ^ (prefixWord ++ tailWord_1974207).sum := by decide
  have hdescent : baseEnd_1974207 < baseStart_1974207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974295 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 5]
def baseStart_1974295 : Nat := 118140960795 + 1974295 * 2 ^ 59
def prefixEnd_1974295 : Nat := 4983230072969 + 3 ^ 40 * 1974295 * 2
def baseEnd_1974295 : Nat := 112640254307606477270321

theorem tailTrace_1974295 : CollatzResearch.WordTrace tailWord_1974295 prefixEnd_1974295 112640254307606477270321 := by
  unfold tailWord_1974295
  simp only [CollatzResearch.WordTrace]
  refine ⟨72008454382473872586620339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48005636254982581724413559 72008454382473872586620339)
  ·
    refine ⟨108012681573710808879930509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72008454382473872586620339 108012681573710808879930509)
    ·
      refine ⟨40504755590141553329973941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108012681573710808879930509 40504755590141553329973941)
      ·
        refine ⟨3797320836575770624685057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40504755590141553329973941 3797320836575770624685057)
        ·
          refine ⟨2847990627431827968513793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797320836575770624685057 2847990627431827968513793)
          ·
            refine ⟨2135992970573870976385345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2847990627431827968513793 2135992970573870976385345)
            ·
              refine ⟨1601994727930403232289009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135992970573870976385345 1601994727930403232289009)
              ·
                refine ⟨1201496045947802424216757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601994727930403232289009 1201496045947802424216757)
                ·
                  refine ⟨112640254307606477270321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1201496045947802424216757 112640254307606477270321)
                  ·
                    rfl

theorem cell23_1974295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 5].length) (baseStart_1974295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974295 prefixEnd_1974295 := by exact prefixLift 1974295
  have htrace : WordTrace (prefixWord ++ tailWord_1974295) baseStart_1974295 baseEnd_1974295 := by
    simpa [prefixWord, tailWord_1974295, baseEnd_1974295] using wordTrace_append hprefix tailTrace_1974295
  have hstable : (prefixWord ++ tailWord_1974295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974295).length < 2 ^ (prefixWord ++ tailWord_1974295).sum := by decide
  have hdescent : baseEnd_1974295 < baseStart_1974295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974297 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1974297 : Nat := 118140960795 + 1974297 * 2 ^ 59
def prefixEnd_1974297 : Nat := 4983230072969 + 3 ^ 40 * 1974297 * 2
def baseEnd_1974297 : Nat := 1013763315729767287607879

theorem tailTrace_1974297 : CollatzResearch.WordTrace tailWord_1974297 prefixEnd_1974297 1013763315729767287607879 := by
  unfold tailWord_1974297
  simp only [CollatzResearch.WordTrace]
  refine ⟨72008527328466626928193145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48005684885644417952128763 72008527328466626928193145)
  ·
    refine ⟨54006395496349970196144859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72008527328466626928193145 54006395496349970196144859)
    ·
      refine ⟨81009593244524955294217289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54006395496349970196144859 81009593244524955294217289)
      ·
        refine ⟨60757194933393716470662967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81009593244524955294217289 60757194933393716470662967)
        ·
          refine ⟨91135792400090574705994451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60757194933393716470662967 91135792400090574705994451)
          ·
            refine ⟨136703688600135862058991677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91135792400090574705994451 136703688600135862058991677)
            ·
              refine ⟨51263883225050948272121879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136703688600135862058991677 51263883225050948272121879)
              ·
                refine ⟨76895824837576422408182819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51263883225050948272121879 76895824837576422408182819)
                ·
                  refine ⟨115343737256364633612274229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76895824837576422408182819 115343737256364633612274229)
                  ·
                    refine ⟨10813475367784184401150709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115343737256364633612274229 10813475367784184401150709)
                    ·
                      refine ⟨1013763315729767287607879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10813475367784184401150709 1013763315729767287607879)
                      ·
                        rfl

theorem cell23_1974297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1974297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974297 prefixEnd_1974297 := by exact prefixLift 1974297
  have htrace : WordTrace (prefixWord ++ tailWord_1974297) baseStart_1974297 baseEnd_1974297 := by
    simpa [prefixWord, tailWord_1974297, baseEnd_1974297] using wordTrace_append hprefix tailTrace_1974297
  have hstable : (prefixWord ++ tailWord_1974297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974297).length < 2 ^ (prefixWord ++ tailWord_1974297).sum := by decide
  have hdescent : baseEnd_1974297 < baseStart_1974297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974321 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 3, 4]
def baseStart_1974321 : Nat := 118140960795 + 1974321 * 2 ^ 59
def prefixEnd_1974321 : Nat := 4983230072969 + 3 ^ 40 * 1974321 * 2
def baseEnd_1974321 : Nat := 337925213088491731235923

theorem tailTrace_1974321 : CollatzResearch.WordTrace tailWord_1974321 prefixEnd_1974321 337925213088491731235923 := by
  unfold tailWord_1974321
  simp only [CollatzResearch.WordTrace]
  refine ⟨72009402680379679027066817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48006268453586452684711211 72009402680379679027066817)
  ·
    refine ⟨54007052010284759270300113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72009402680379679027066817 54007052010284759270300113)
    ·
      refine ⟨40505289007713569452725085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54007052010284759270300113 40505289007713569452725085)
      ·
        refine ⟨15189483377892588544771907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40505289007713569452725085 15189483377892588544771907)
        ·
          refine ⟨22784225066838882817157861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15189483377892588544771907 22784225066838882817157861)
          ·
            refine ⟨4272042200032290528217099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22784225066838882817157861 4272042200032290528217099)
            ·
              refine ⟨6408063300048435792325649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272042200032290528217099 6408063300048435792325649)
              ·
                refine ⟨4806047475036326844244237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6408063300048435792325649 4806047475036326844244237)
                ·
                  refine ⟨1802267803138622566591589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4806047475036326844244237 1802267803138622566591589)
                  ·
                    refine ⟨337925213088491731235923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1802267803138622566591589 337925213088491731235923)
                    ·
                      rfl

theorem cell23_1974321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_1974321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974321 prefixEnd_1974321 := by exact prefixLift 1974321
  have htrace : WordTrace (prefixWord ++ tailWord_1974321) baseStart_1974321 baseEnd_1974321 := by
    simpa [prefixWord, tailWord_1974321, baseEnd_1974321] using wordTrace_append hprefix tailTrace_1974321
  have hstable : (prefixWord ++ tailWord_1974321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974321).length < 2 ^ (prefixWord ++ tailWord_1974321).sum := by decide
  have hdescent : baseEnd_1974321 < baseStart_1974321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974328 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_1974328 : Nat := 118140960795 + 1974328 * 2 ^ 59
def prefixEnd_1974328 : Nat := 4983230072969 + 3 ^ 40 * 1974328 * 2
def baseEnd_1974328 : Nat := 1013779233630056666320237

theorem tailTrace_1974328 : CollatzResearch.WordTrace tailWord_1974328 prefixEnd_1974328 1013779233630056666320237 := by
  unfold tailWord_1974328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36004828995677159611285819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48006438660902879481714425 36004828995677159611285819)
  ·
    refine ⟨54007243493515739416928729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36004828995677159611285819 54007243493515739416928729)
    ·
      refine ⟨40505432620136804562696547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54007243493515739416928729 40505432620136804562696547)
      ·
        refine ⟨60758148930205206844044821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40505432620136804562696547 60758148930205206844044821)
        ·
          refine ⟨2848038231103369070814601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60758148930205206844044821 2848038231103369070814601)
          ·
            refine ⟨2136028673327526803110951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848038231103369070814601 2136028673327526803110951)
            ·
              refine ⟨3204043009991290204666427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136028673327526803110951 3204043009991290204666427)
              ·
                refine ⟨4806064514986935306999641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204043009991290204666427 4806064514986935306999641)
                ·
                  refine ⟨3604548386240201480249731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4806064514986935306999641 3604548386240201480249731)
                  ·
                    refine ⟨5406822579360302220374597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3604548386240201480249731 5406822579360302220374597)
                    ·
                      refine ⟨1013779233630056666320237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5406822579360302220374597 1013779233630056666320237)
                      ·
                        rfl

theorem cell23_1974328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_1974328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974328 prefixEnd_1974328 := by exact prefixLift 1974328
  have htrace : WordTrace (prefixWord ++ tailWord_1974328) baseStart_1974328 baseEnd_1974328 := by
    simpa [prefixWord, tailWord_1974328, baseEnd_1974328] using wordTrace_append hprefix tailTrace_1974328
  have hstable : (prefixWord ++ tailWord_1974328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974328).length < 2 ^ (prefixWord ++ tailWord_1974328).sum := by decide
  have hdescent : baseEnd_1974328 < baseStart_1974328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974371 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 1, 5, 2]
def baseStart_1974371 : Nat := 118140960795 + 1974371 * 2 ^ 59
def prefixEnd_1974371 : Nat := 4983230072969 + 3 ^ 40 * 1974371 * 2
def baseEnd_1974371 : Nat := 1013801313298199998082539

theorem tailTrace_1974371 : CollatzResearch.WordTrace tailWord_1974371 prefixEnd_1974371 1013801313298199998082539 := by
  unfold tailWord_1974371
  simp only [CollatzResearch.WordTrace]
  refine ⟨72011226330198537566386967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48007484220132358377591311 72011226330198537566386967)
  ·
    refine ⟨108016839495297806349580451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72011226330198537566386967 108016839495297806349580451)
    ·
      refine ⟨162025259242946709524370677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108016839495297806349580451 162025259242946709524370677)
      ·
        refine ⟨15189868054026254017909751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162025259242946709524370677 15189868054026254017909751)
        ·
          refine ⟨22784802081039381026864627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15189868054026254017909751 22784802081039381026864627)
          ·
            refine ⟨34177203121559071540296941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22784802081039381026864627 34177203121559071540296941)
            ·
              refine ⟨12816451170584651827611353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34177203121559071540296941 12816451170584651827611353)
              ·
                refine ⟨9612338377938488870708515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12816451170584651827611353 9612338377938488870708515)
                ·
                  refine ⟨14418507566907733306062773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612338377938488870708515 14418507566907733306062773)
                  ·
                    refine ⟨1351735084397599997443385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14418507566907733306062773 1351735084397599997443385)
                    ·
                      refine ⟨1013801313298199998082539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351735084397599997443385 1013801313298199998082539)
                      ·
                        rfl

theorem cell23_1974371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_1974371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974371 prefixEnd_1974371 := by exact prefixLift 1974371
  have htrace : WordTrace (prefixWord ++ tailWord_1974371) baseStart_1974371 baseEnd_1974371 := by
    simpa [prefixWord, tailWord_1974371, baseEnd_1974371] using wordTrace_append hprefix tailTrace_1974371
  have hstable : (prefixWord ++ tailWord_1974371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974371).length < 2 ^ (prefixWord ++ tailWord_1974371).sum := by decide
  have hdescent : baseEnd_1974371 < baseStart_1974371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974421 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_1974421 : Nat := 118140960795 + 1974421 * 2 ^ 59
def prefixEnd_1974421 : Nat := 4983230072969 + 3 ^ 40 * 1974421 * 2
def baseEnd_1974421 : Nat := 1013826987330924802457309

theorem tailTrace_1974421 : CollatzResearch.WordTrace tailWord_1974421 prefixEnd_1974421 1013826987330924802457309 := by
  unfold tailWord_1974421
  simp only [CollatzResearch.WordTrace]
  refine ⟨72013049980017396105707117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48008699986678264070471411 72013049980017396105707117)
  ·
    refine ⟨27004893742506523539640169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72013049980017396105707117 27004893742506523539640169)
    ·
      refine ⟨20253670306879892654730127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27004893742506523539640169 20253670306879892654730127)
      ·
        refine ⟨30380505460319838982095191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20253670306879892654730127 30380505460319838982095191)
        ·
          refine ⟨45570758190479758473142787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30380505460319838982095191 45570758190479758473142787)
          ·
            refine ⟨68356137285719637709714181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45570758190479758473142787 68356137285719637709714181)
            ·
              refine ⟨12816775741072432070571409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68356137285719637709714181 12816775741072432070571409)
              ·
                refine ⟨9612581805804324052928557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12816775741072432070571409 9612581805804324052928557)
                ·
                  refine ⟨3604718177176621519848209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9612581805804324052928557 3604718177176621519848209)
                  ·
                    refine ⟨2703538632882466139886157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604718177176621519848209 2703538632882466139886157)
                    ·
                      refine ⟨1013826987330924802457309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2703538632882466139886157 1013826987330924802457309)
                      ·
                        rfl

theorem cell23_1974421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_1974421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974421 prefixEnd_1974421 := by exact prefixLift 1974421
  have htrace : WordTrace (prefixWord ++ tailWord_1974421) baseStart_1974421 baseEnd_1974421 := by
    simpa [prefixWord, tailWord_1974421, baseEnd_1974421] using wordTrace_append hprefix tailTrace_1974421
  have hstable : (prefixWord ++ tailWord_1974421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974421).length < 2 ^ (prefixWord ++ tailWord_1974421).sum := by decide
  have hdescent : baseEnd_1974421 < baseStart_1974421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974428 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1974428 : Nat := 118140960795 + 1974428 * 2 ^ 59
def prefixEnd_1974428 : Nat := 4983230072969 + 3 ^ 40 * 1974428 * 2
def baseEnd_1974428 : Nat := 337943527231835425023259

theorem tailTrace_1974428 : CollatzResearch.WordTrace tailWord_1974428 prefixEnd_1974428 337943527231835425023259 := by
  unfold tailWord_1974428
  simp only [CollatzResearch.WordTrace]
  refine ⟨36006652645496018150605969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48008870193994690867474625 36006652645496018150605969)
  ·
    refine ⟨27004989484122013612954477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36006652645496018150605969 27004989484122013612954477)
    ·
      refine ⟨10126871056545755104857929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27004989484122013612954477 10126871056545755104857929)
      ·
        refine ⟨7595153292409316328643447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10126871056545755104857929 7595153292409316328643447)
        ·
          refine ⟨11392729938613974492965171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595153292409316328643447 11392729938613974492965171)
          ·
            refine ⟨17089094907920961739447757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11392729938613974492965171 17089094907920961739447757)
            ·
              refine ⟨6408410590470360652292909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17089094907920961739447757 6408410590470360652292909)
              ·
                refine ⟨2403153971426385244609841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6408410590470360652292909 2403153971426385244609841)
                ·
                  refine ⟨1802365478569788933457381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403153971426385244609841 1802365478569788933457381)
                  ·
                    refine ⟨337943527231835425023259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1802365478569788933457381 337943527231835425023259)
                    ·
                      rfl

theorem cell23_1974428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1974428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974428 prefixEnd_1974428 := by exact prefixLift 1974428
  have htrace : WordTrace (prefixWord ++ tailWord_1974428) baseStart_1974428 baseEnd_1974428 := by
    simpa [prefixWord, tailWord_1974428, baseEnd_1974428] using wordTrace_append hprefix tailTrace_1974428
  have hstable : (prefixWord ++ tailWord_1974428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974428).length < 2 ^ (prefixWord ++ tailWord_1974428).sum := by decide
  have hdescent : baseEnd_1974428 < baseStart_1974428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974431 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1974431 : Nat := 118140960795 + 1974431 * 2 ^ 59
def prefixEnd_1974431 : Nat := 4983230072969 + 3 ^ 40 * 1974431 * 2
def baseEnd_1974431 : Nat := 1013832122137469763332263

theorem tailTrace_1974431 : CollatzResearch.WordTrace tailWord_1974431 prefixEnd_1974431 1013832122137469763332263 := by
  unfold tailWord_1974431
  simp only [CollatzResearch.WordTrace]
  refine ⟨72013414709981167813571147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48008943139987445209047431 72013414709981167813571147)
  ·
    refine ⟨108020122064971751720356721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72013414709981167813571147 108020122064971751720356721)
    ·
      refine ⟨81015091548728813790267541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108020122064971751720356721 81015091548728813790267541)
      ·
        refine ⟨3797582416346663146418791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81015091548728813790267541 3797582416346663146418791)
        ·
          refine ⟨5696373624519994719628187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3797582416346663146418791 5696373624519994719628187)
          ·
            refine ⟨8544560436779992079442281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696373624519994719628187 8544560436779992079442281)
            ·
              refine ⟨6408420327584994059581711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8544560436779992079442281 6408420327584994059581711)
              ·
                refine ⟨9612630491377491089372567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408420327584994059581711 9612630491377491089372567)
                ·
                  refine ⟨14418945737066236634058851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9612630491377491089372567 14418945737066236634058851)
                  ·
                    refine ⟨21628418605599354951088277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14418945737066236634058851 21628418605599354951088277)
                    ·
                      refine ⟨1013832122137469763332263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21628418605599354951088277 1013832122137469763332263)
                      ·
                        rfl

theorem cell23_1974431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1974431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974431 prefixEnd_1974431 := by exact prefixLift 1974431
  have htrace : WordTrace (prefixWord ++ tailWord_1974431) baseStart_1974431 baseEnd_1974431 := by
    simpa [prefixWord, tailWord_1974431, baseEnd_1974431] using wordTrace_append hprefix tailTrace_1974431
  have hstable : (prefixWord ++ tailWord_1974431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974431).length < 2 ^ (prefixWord ++ tailWord_1974431).sum := by decide
  have hdescent : baseEnd_1974431 < baseStart_1974431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974455 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 1, 2, 3]
def baseStart_1974455 : Nat := 118140960795 + 1974455 * 2 ^ 59
def prefixEnd_1974455 : Nat := 4983230072969 + 3 ^ 40 * 1974455 * 2
def baseEnd_1974455 : Nat := 1013844445673177669432153

theorem tailTrace_1974455 : CollatzResearch.WordTrace tailWord_1974455 prefixEnd_1974455 1013844445673177669432153 := by
  unfold tailWord_1974455
  simp only [CollatzResearch.WordTrace]
  refine ⟨72014290061894219912444819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48009526707929479941629879 72014290061894219912444819)
  ·
    refine ⟨108021435092841329868667229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72014290061894219912444819 108021435092841329868667229)
    ·
      refine ⟨40508038159815498700750211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108021435092841329868667229 40508038159815498700750211)
      ·
        refine ⟨60762057239723248051125317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40508038159815498700750211 60762057239723248051125317)
        ·
          refine ⟨11392885732448109009585997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60762057239723248051125317 11392885732448109009585997)
          ·
            refine ⟨4272332149668040878594749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11392885732448109009585997 4272332149668040878594749)
            ·
              refine ⟨1602124556125515329473031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4272332149668040878594749 1602124556125515329473031)
              ·
                refine ⟨2403186834188272994209547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602124556125515329473031 2403186834188272994209547)
                ·
                  refine ⟨3604780251282409491314321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403186834188272994209547 3604780251282409491314321)
                  ·
                    refine ⟨2703585188461807118485741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3604780251282409491314321 2703585188461807118485741)
                    ·
                      refine ⟨1013844445673177669432153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2703585188461807118485741 1013844445673177669432153)
                      ·
                        rfl

theorem cell23_1974455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_1974455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974455 prefixEnd_1974455 := by exact prefixLift 1974455
  have htrace : WordTrace (prefixWord ++ tailWord_1974455) baseStart_1974455 baseEnd_1974455 := by
    simpa [prefixWord, tailWord_1974455, baseEnd_1974455] using wordTrace_append hprefix tailTrace_1974455
  have hstable : (prefixWord ++ tailWord_1974455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974455).length < 2 ^ (prefixWord ++ tailWord_1974455).sum := by decide
  have hdescent : baseEnd_1974455 < baseStart_1974455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974485 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1974485 : Nat := 118140960795 + 1974485 * 2 ^ 59
def prefixEnd_1974485 : Nat := 4983230072969 + 3 ^ 40 * 1974485 * 2
def baseEnd_1974485 : Nat := 1013859850092812552057015

theorem tailTrace_1974485 : CollatzResearch.WordTrace tailWord_1974485 prefixEnd_1974485 1013859850092812552057015 := by
  unfold tailWord_1974485
  simp only [CollatzResearch.WordTrace]
  refine ⟨72015384251785535036036909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48010256167857023357357939 72015384251785535036036909)
  ·
    refine ⟨27005769094419575638513841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72015384251785535036036909 27005769094419575638513841)
    ·
      refine ⟨20254326820814681728885381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27005769094419575638513841 20254326820814681728885381)
      ·
        refine ⟨3797686278902752824166009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20254326820814681728885381 3797686278902752824166009)
        ·
          refine ⟨2848264709177064618124507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797686278902752824166009 2848264709177064618124507)
          ·
            refine ⟨4272397063765596927186761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848264709177064618124507 4272397063765596927186761)
            ·
              refine ⟨3204297797824197695390071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4272397063765596927186761 3204297797824197695390071)
              ·
                refine ⟨4806446696736296543085107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204297797824197695390071 4806446696736296543085107)
                ·
                  refine ⟨7209670045104444814627661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806446696736296543085107 7209670045104444814627661)
                  ·
                    refine ⟨2703626266914166805485373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7209670045104444814627661 2703626266914166805485373)
                    ·
                      refine ⟨1013859850092812552057015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2703626266914166805485373 1013859850092812552057015)
                      ·
                        rfl

theorem cell23_1974485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1974485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974485 prefixEnd_1974485 := by exact prefixLift 1974485
  have htrace : WordTrace (prefixWord ++ tailWord_1974485) baseStart_1974485 baseEnd_1974485 := by
    simpa [prefixWord, tailWord_1974485, baseEnd_1974485] using wordTrace_append hprefix tailTrace_1974485
  have hstable : (prefixWord ++ tailWord_1974485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974485).length < 2 ^ (prefixWord ++ tailWord_1974485).sum := by decide
  have hdescent : baseEnd_1974485 < baseStart_1974485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974508 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 1, 4, 2]
def baseStart_1974508 : Nat := 118140960795 + 1974508 * 2 ^ 59
def prefixEnd_1974508 : Nat := 4983230072969 + 3 ^ 40 * 1974508 * 2
def baseEnd_1974508 : Nat := 1013871660147865962069409

theorem tailTrace_1974508 : CollatzResearch.WordTrace tailWord_1974508 prefixEnd_1974508 1013871660147865962069409 := by
  unfold tailWord_1974508
  simp only [CollatzResearch.WordTrace]
  refine ⟨36008111565351104982062089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48010815420468139976082785 36008111565351104982062089)
  ·
    refine ⟨27006083674013328736546567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36008111565351104982062089 27006083674013328736546567)
    ·
      refine ⟨40509125511019993104819851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27006083674013328736546567 40509125511019993104819851)
      ·
        refine ⟨60763688266529989657229777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40509125511019993104819851 60763688266529989657229777)
        ·
          refine ⟨45572766199897492242922333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60763688266529989657229777 45572766199897492242922333)
          ·
            refine ⟨17089787324961559591095875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45572766199897492242922333 17089787324961559591095875)
            ·
              refine ⟨25634680987442339386643813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17089787324961559591095875 25634680987442339386643813)
              ·
                refine ⟨4806502685145438634995715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25634680987442339386643813 4806502685145438634995715)
                ·
                  refine ⟨7209754027718157952493573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4806502685145438634995715 7209754027718157952493573)
                  ·
                    refine ⟨1351828880197154616092545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7209754027718157952493573 1351828880197154616092545)
                    ·
                      refine ⟨1013871660147865962069409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351828880197154616092545 1013871660147865962069409)
                      ·
                        rfl

theorem cell23_1974508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_1974508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974508 prefixEnd_1974508 := by exact prefixLift 1974508
  have htrace : WordTrace (prefixWord ++ tailWord_1974508) baseStart_1974508 baseEnd_1974508 := by
    simpa [prefixWord, tailWord_1974508, baseEnd_1974508] using wordTrace_append hprefix tailTrace_1974508
  have hstable : (prefixWord ++ tailWord_1974508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974508).length < 2 ^ (prefixWord ++ tailWord_1974508).sum := by decide
  have hdescent : baseEnd_1974508 < baseStart_1974508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974531 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 7]
def baseStart_1974531 : Nat := 118140960795 + 1974531 * 2 ^ 59
def prefixEnd_1974531 : Nat := 4983230072969 + 3 ^ 40 * 1974531 * 2
def baseEnd_1974531 : Nat := 112653718911435485786867

theorem tailTrace_1974531 : CollatzResearch.WordTrace tailWord_1974531 prefixEnd_1974531 112653718911435485786867 := by
  unfold tailWord_1974531
  simp only [CollatzResearch.WordTrace]
  refine ⟨72017062009618884892211447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48011374673079256594807631 72017062009618884892211447)
  ·
    refine ⟨108025593014428327338317171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72017062009618884892211447 108025593014428327338317171)
    ·
      refine ⟨162038389521642491007475757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108025593014428327338317171 162038389521642491007475757)
      ·
        refine ⟨60764396070615934127803409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162038389521642491007475757 60764396070615934127803409)
        ·
          refine ⟨45573297052961950595852557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60764396070615934127803409 45573297052961950595852557)
          ·
            refine ⟨17089986394860731473444709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45573297052961950595852557 17089986394860731473444709)
            ·
              refine ⟨3204372449036387151270883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17089986394860731473444709 3204372449036387151270883)
              ·
                refine ⟨4806558673554580726906325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204372449036387151270883 4806558673554580726906325)
                ·
                  refine ⟨112653718911435485786867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4806558673554580726906325 112653718911435485786867)
                  ·
                    rfl

theorem cell23_1974531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 7].length) (baseStart_1974531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974531 prefixEnd_1974531 := by exact prefixLift 1974531
  have htrace : WordTrace (prefixWord ++ tailWord_1974531) baseStart_1974531 baseEnd_1974531 := by
    simpa [prefixWord, tailWord_1974531, baseEnd_1974531] using wordTrace_append hprefix tailTrace_1974531
  have hstable : (prefixWord ++ tailWord_1974531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974531).length < 2 ^ (prefixWord ++ tailWord_1974531).sum := by decide
  have hdescent : baseEnd_1974531 < baseStart_1974531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974561 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1974561 : Nat := 118140960795 + 1974561 * 2 ^ 59
def prefixEnd_1974561 : Nat := 4983230072969 + 3 ^ 40 * 1974561 * 2
def baseEnd_1974561 : Nat := 337966291540851418235555

theorem tailTrace_1974561 : CollatzResearch.WordTrace tailWord_1974561 prefixEnd_1974561 337966291540851418235555 := by
  unfold tailWord_1974561
  simp only [CollatzResearch.WordTrace]
  refine ⟨72018156199510200015803537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48012104133006800010535691 72018156199510200015803537)
  ·
    refine ⟨54013617149632650011852653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72018156199510200015803537 54013617149632650011852653)
    ·
      refine ⟨20255106431112243754444745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54013617149632650011852653 20255106431112243754444745)
      ·
        refine ⟨15191329823334182815833559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20255106431112243754444745 15191329823334182815833559)
        ·
          refine ⟨22786994735001274223750339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15191329823334182815833559 22786994735001274223750339)
          ·
            refine ⟨34180492102501911335625509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22786994735001274223750339 34180492102501911335625509)
            ·
              refine ⟨6408842269219108375429783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34180492102501911335625509 6408842269219108375429783)
              ·
                refine ⟨9613263403828662563144675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6408842269219108375429783 9613263403828662563144675)
                ·
                  refine ⟨14419895105742993844717013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9613263403828662563144675 14419895105742993844717013)
                  ·
                    refine ⟨337966291540851418235555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14419895105742993844717013 337966291540851418235555)
                    ·
                      rfl

theorem cell23_1974561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1974561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974561 prefixEnd_1974561 := by exact prefixLift 1974561
  have htrace : WordTrace (prefixWord ++ tailWord_1974561) baseStart_1974561 baseEnd_1974561 := by
    simpa [prefixWord, tailWord_1974561, baseEnd_1974561] using wordTrace_append hprefix tailTrace_1974561
  have hstable : (prefixWord ++ tailWord_1974561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974561).length < 2 ^ (prefixWord ++ tailWord_1974561).sum := by decide
  have hdescent : baseEnd_1974561 < baseStart_1974561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974593 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_1974593 : Nat := 118140960795 + 1974593 * 2 ^ 59
def prefixEnd_1974593 : Nat := 4983230072969 + 3 ^ 40 * 1974593 * 2
def baseEnd_1974593 : Nat := 1013915306003498129506519

theorem tailTrace_1974593 : CollatzResearch.WordTrace tailWord_1974593 prefixEnd_1974593 1013915306003498129506519 := by
  unfold tailWord_1974593
  simp only [CollatzResearch.WordTrace]
  refine ⟨72019323335394269480968433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48012882223596179653978955 72019323335394269480968433)
  ·
    refine ⟨54014492501545702110726325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72019323335394269480968433 54014492501545702110726325)
    ·
      refine ⟨5063858672019909572880593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54014492501545702110726325 5063858672019909572880593)
      ·
        refine ⟨3797894004014932179660445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5063858672019909572880593 3797894004014932179660445)
        ·
          refine ⟨1424210251505599567372667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3797894004014932179660445 1424210251505599567372667)
          ·
            refine ⟨2136315377258399351059001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424210251505599567372667 2136315377258399351059001)
            ·
              refine ⟨1602236532943799513294251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136315377258399351059001 1602236532943799513294251)
              ·
                refine ⟨2403354799415699269941377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602236532943799513294251 2403354799415699269941377)
                ·
                  refine ⟨1802516099561774452456033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403354799415699269941377 1802516099561774452456033)
                  ·
                    refine ⟨1351887074671330839342025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1802516099561774452456033 1351887074671330839342025)
                    ·
                      refine ⟨1013915306003498129506519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1351887074671330839342025 1013915306003498129506519)
                      ·
                        rfl

theorem cell23_1974593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_1974593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974593 prefixEnd_1974593 := by exact prefixLift 1974593
  have htrace : WordTrace (prefixWord ++ tailWord_1974593) baseStart_1974593 baseEnd_1974593 := by
    simpa [prefixWord, tailWord_1974593, baseEnd_1974593] using wordTrace_append hprefix tailTrace_1974593
  have hstable : (prefixWord ++ tailWord_1974593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974593).length < 2 ^ (prefixWord ++ tailWord_1974593).sum := by decide
  have hdescent : baseEnd_1974593 < baseStart_1974593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974641 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1974641 : Nat := 118140960795 + 1974641 * 2 ^ 59
def prefixEnd_1974641 : Nat := 4983230072969 + 3 ^ 40 * 1974641 * 2
def baseEnd_1974641 : Nat := 1013939953074913941706297

theorem tailTrace_1974641 : CollatzResearch.WordTrace tailWord_1974641 prefixEnd_1974641 1013939953074913941706297 := by
  unfold tailWord_1974641
  simp only [CollatzResearch.WordTrace]
  refine ⟨72021074039220373678715777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48014049359480249119143851 72021074039220373678715777)
  ·
    refine ⟨54015805529415280259036833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72021074039220373678715777 54015805529415280259036833)
    ·
      refine ⟨40511854147061460194277625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54015805529415280259036833 40511854147061460194277625)
      ·
        refine ⟨30383890610296095145708219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40511854147061460194277625 30383890610296095145708219)
        ·
          refine ⟨45575835915444142718562329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30383890610296095145708219 45575835915444142718562329)
          ·
            refine ⟨34181876936583107038921747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45575835915444142718562329 34181876936583107038921747)
            ·
              refine ⟨51272815404874660558382621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34181876936583107038921747 51272815404874660558382621)
              ·
                refine ⟨19227305776827997709393483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51272815404874660558382621 19227305776827997709393483)
                ·
                  refine ⟨28840958665241996564090225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19227305776827997709393483 28840958665241996564090225)
                  ·
                    refine ⟨21630718998931497423067669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28840958665241996564090225 21630718998931497423067669)
                    ·
                      refine ⟨1013939953074913941706297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21630718998931497423067669 1013939953074913941706297)
                      ·
                        rfl

theorem cell23_1974641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1974641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974641 prefixEnd_1974641 := by exact prefixLift 1974641
  have htrace : WordTrace (prefixWord ++ tailWord_1974641) baseStart_1974641 baseEnd_1974641 := by
    simpa [prefixWord, tailWord_1974641, baseEnd_1974641] using wordTrace_append hprefix tailTrace_1974641
  have hstable : (prefixWord ++ tailWord_1974641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974641).length < 2 ^ (prefixWord ++ tailWord_1974641).sum := by decide
  have hdescent : baseEnd_1974641 < baseStart_1974641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974642 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_1974642 : Nat := 118140960795 + 1974642 * 2 ^ 59
def prefixEnd_1974642 : Nat := 4983230072969 + 3 ^ 40 * 1974642 * 2
def baseEnd_1974642 : Nat := 337980155518522812597931

theorem tailTrace_1974642 : CollatzResearch.WordTrace tailWord_1974642 prefixEnd_1974642 337980155518522812597931 := by
  unfold tailWord_1974642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005277628054187712375545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48014073674811167233001453 18005277628054187712375545)
  ·
    refine ⟨13503958221040640784281659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18005277628054187712375545 13503958221040640784281659)
    ·
      refine ⟨20255937331560961176422489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503958221040640784281659 20255937331560961176422489)
      ·
        refine ⟨15191952998670720882316867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20255937331560961176422489 15191952998670720882316867)
        ·
          refine ⟨22787929498006081323475301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15191952998670720882316867 22787929498006081323475301)
          ·
            refine ⟨4272736780876140248151619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22787929498006081323475301 4272736780876140248151619)
            ·
              refine ⟨6409105171314210372227429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272736780876140248151619 6409105171314210372227429)
              ·
                refine ⟨1201707219621414444792643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6409105171314210372227429 1201707219621414444792643)
                ·
                  refine ⟨1802560829432121667188965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201707219621414444792643 1802560829432121667188965)
                  ·
                    refine ⟨337980155518522812597931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1802560829432121667188965 337980155518522812597931)
                    ·
                      rfl

theorem cell23_1974642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_1974642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974642 prefixEnd_1974642 := by exact prefixLift 1974642
  have htrace : WordTrace (prefixWord ++ tailWord_1974642) baseStart_1974642 baseEnd_1974642 := by
    simpa [prefixWord, tailWord_1974642, baseEnd_1974642] using wordTrace_append hprefix tailTrace_1974642
  have hstable : (prefixWord ++ tailWord_1974642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974642).length < 2 ^ (prefixWord ++ tailWord_1974642).sum := by decide
  have hdescent : baseEnd_1974642 < baseStart_1974642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974661 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_1974661 : Nat := 118140960795 + 1974661 * 2 ^ 59
def prefixEnd_1974661 : Nat := 4983230072969 + 3 ^ 40 * 1974661 * 2
def baseEnd_1974661 : Nat := 1013950222688003863456205

theorem tailTrace_1974661 : CollatzResearch.WordTrace tailWord_1974661 prefixEnd_1974661 1013950222688003863456205 := by
  unfold tailWord_1974661
  simp only [CollatzResearch.WordTrace]
  refine ⟨72021803499147917094443837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48014535666098611396295891 72021803499147917094443837)
  ·
    refine ⟨27008176312180468910416439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72021803499147917094443837 27008176312180468910416439)
    ·
      refine ⟨40512264468270703365624659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27008176312180468910416439 40512264468270703365624659)
      ·
        refine ⟨60768396702406055048436989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40512264468270703365624659 60768396702406055048436989)
        ·
          refine ⟨22788148763402270643163871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60768396702406055048436989 22788148763402270643163871)
          ·
            refine ⟨34182223145103405964745807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22788148763402270643163871 34182223145103405964745807)
            ·
              refine ⟨51273334717655108947118711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34182223145103405964745807 51273334717655108947118711)
              ·
                refine ⟨76910002076482663420678067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51273334717655108947118711 76910002076482663420678067)
                ·
                  refine ⟨115365003114723995131017101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76910002076482663420678067 115365003114723995131017101)
                  ·
                    refine ⟨43261876168021498174131413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 115365003114723995131017101 43261876168021498174131413)
                    ·
                      refine ⟨1013950222688003863456205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43261876168021498174131413 1013950222688003863456205)
                      ·
                        rfl

theorem cell23_1974661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_1974661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974661 prefixEnd_1974661 := by exact prefixLift 1974661
  have htrace : WordTrace (prefixWord ++ tailWord_1974661) baseStart_1974661 baseEnd_1974661 := by
    simpa [prefixWord, tailWord_1974661, baseEnd_1974661] using wordTrace_append hprefix tailTrace_1974661
  have hstable : (prefixWord ++ tailWord_1974661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974661).length < 2 ^ (prefixWord ++ tailWord_1974661).sum := by decide
  have hdescent : baseEnd_1974661 < baseStart_1974661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974665 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 3]
def baseStart_1974665 : Nat := 118140960795 + 1974665 * 2 ^ 59
def prefixEnd_1974665 : Nat := 4983230072969 + 3 ^ 40 * 1974665 * 2
def baseEnd_1974665 : Nat := 1013952276610621847806187

theorem tailTrace_1974665 : CollatzResearch.WordTrace tailWord_1974665 prefixEnd_1974665 1013952276610621847806187 := by
  unfold tailWord_1974665
  simp only [CollatzResearch.WordTrace]
  refine ⟨72021949391133425777589449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48014632927422283851726299 72021949391133425777589449)
  ·
    refine ⟨54016462043350069333192087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72021949391133425777589449 54016462043350069333192087)
    ·
      refine ⟨81024693065025103999788131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54016462043350069333192087 81024693065025103999788131)
      ·
        refine ⟨121537039597537655999682197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81024693065025103999788131 121537039597537655999682197)
        ·
          refine ⟨5697048731134577624985103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121537039597537655999682197 5697048731134577624985103)
          ·
            refine ⟨8545573096701866437477655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697048731134577624985103 8545573096701866437477655)
            ·
              refine ⟨12818359645052799656216483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8545573096701866437477655 12818359645052799656216483)
              ·
                refine ⟨19227539467579199484324725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12818359645052799656216483 19227539467579199484324725)
                ·
                  refine ⟨1802581825085549951655443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19227539467579199484324725 1802581825085549951655443)
                  ·
                    refine ⟨2703872737628324927483165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1802581825085549951655443 2703872737628324927483165)
                    ·
                      refine ⟨1013952276610621847806187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2703872737628324927483165 1013952276610621847806187)
                      ·
                        rfl

theorem cell23_1974665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_1974665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974665 prefixEnd_1974665 := by exact prefixLift 1974665
  have htrace : WordTrace (prefixWord ++ tailWord_1974665) baseStart_1974665 baseEnd_1974665 := by
    simpa [prefixWord, tailWord_1974665, baseEnd_1974665] using wordTrace_append hprefix tailTrace_1974665
  have hstable : (prefixWord ++ tailWord_1974665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974665).length < 2 ^ (prefixWord ++ tailWord_1974665).sum := by decide
  have hdescent : baseEnd_1974665 < baseStart_1974665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974668 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_1974668 : Nat := 118140960795 + 1974668 * 2 ^ 59
def prefixEnd_1974668 : Nat := 4983230072969 + 3 ^ 40 * 1974668 * 2
def baseEnd_1974668 : Nat := 337984605684195112022891

theorem tailTrace_1974668 : CollatzResearch.WordTrace tailWord_1974668 prefixEnd_1974668 337984605684195112022891 := by
  unfold tailWord_1974668
  simp only [CollatzResearch.WordTrace]
  refine ⟨36011029405061278644974329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48014705873415038193299105 36011029405061278644974329)
  ·
    refine ⟨27008272053795958983730747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36011029405061278644974329 27008272053795958983730747)
    ·
      refine ⟨40512408080693938475596121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27008272053795958983730747 40512408080693938475596121)
      ·
        refine ⟨30384306060520453856697091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40512408080693938475596121 30384306060520453856697091)
        ·
          refine ⟨45576459090780680785045637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30384306060520453856697091 45576459090780680785045637)
          ·
            refine ⟨8545586079521377647196057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45576459090780680785045637 8545586079521377647196057)
            ·
              refine ⟨6409189559641033235397043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8545586079521377647196057 6409189559641033235397043)
              ·
                refine ⟨9613784339461549853095565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6409189559641033235397043 9613784339461549853095565)
                ·
                  refine ⟨3605169127298081194910837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9613784339461549853095565 3605169127298081194910837)
                  ·
                    refine ⟨337984605684195112022891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3605169127298081194910837 337984605684195112022891)
                    ·
                      rfl

theorem cell23_1974668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_1974668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974668 prefixEnd_1974668 := by exact prefixLift 1974668
  have htrace : WordTrace (prefixWord ++ tailWord_1974668) baseStart_1974668 baseEnd_1974668 := by
    simpa [prefixWord, tailWord_1974668, baseEnd_1974668] using wordTrace_append hprefix tailTrace_1974668
  have hstable : (prefixWord ++ tailWord_1974668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974668).length < 2 ^ (prefixWord ++ tailWord_1974668).sum := by decide
  have hdescent : baseEnd_1974668 < baseStart_1974668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974689 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 6]
def baseStart_1974689 : Nat := 118140960795 + 1974689 * 2 ^ 59
def prefixEnd_1974689 : Nat := 4983230072969 + 3 ^ 40 * 1974689 * 2
def baseEnd_1974689 : Nat := 112662733349592194878453

theorem tailTrace_1974689 : CollatzResearch.WordTrace tailWord_1974689 prefixEnd_1974689 112662733349592194878453 := by
  unfold tailWord_1974689
  simp only [CollatzResearch.WordTrace]
  refine ⟨72022824743046477876463121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48015216495364318584308747 72022824743046477876463121)
  ·
    refine ⟨54017118557284858407347341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72022824743046477876463121 54017118557284858407347341)
    ·
      refine ⟨20256419458981821902755253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54017118557284858407347341 20256419458981821902755253)
      ·
        refine ⟨1899039324279545803383305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20256419458981821902755253 1899039324279545803383305)
        ·
          refine ⟨1424279493209659352537479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899039324279545803383305 1424279493209659352537479)
          ·
            refine ⟨2136419239814489028806219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424279493209659352537479 2136419239814489028806219)
            ·
              refine ⟨3204628859721733543209329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136419239814489028806219 3204628859721733543209329)
              ·
                refine ⟨2403471644791300157406997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204628859721733543209329 2403471644791300157406997)
                ·
                  refine ⟨112662733349592194878453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2403471644791300157406997 112662733349592194878453)
                  ·
                    rfl

theorem cell23_1974689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 6].length) (baseStart_1974689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974689 prefixEnd_1974689 := by exact prefixLift 1974689
  have htrace : WordTrace (prefixWord ++ tailWord_1974689) baseStart_1974689 baseEnd_1974689 := by
    simpa [prefixWord, tailWord_1974689, baseEnd_1974689] using wordTrace_append hprefix tailTrace_1974689
  have hstable : (prefixWord ++ tailWord_1974689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974689).length < 2 ^ (prefixWord ++ tailWord_1974689).sum := by decide
  have hdescent : baseEnd_1974689 < baseStart_1974689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974728 : List Nat := [2, 1, 3, 1, 3, 3, 1, 9]
def baseStart_1974728 : Nat := 118140960795 + 1974728 * 2 ^ 59
def prefixEnd_1974728 : Nat := 4983230072969 + 3 ^ 40 * 1974728 * 2
def baseEnd_1974728 : Nat := 37554986144142781530311

theorem tailTrace_1974728 : CollatzResearch.WordTrace tailWord_1974728 prefixEnd_1974728 37554986144142781530311 := by
  unfold tailWord_1974728
  simp only [CollatzResearch.WordTrace]
  refine ⟨36012123594952593768566419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48016164793270125024755225 36012123594952593768566419)
  ·
    refine ⟨54018185392428890652849629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36012123594952593768566419 54018185392428890652849629)
    ·
      refine ⟨20256819522160833994818611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54018185392428890652849629 20256819522160833994818611)
      ·
        refine ⟨30385229283241250992227917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20256819522160833994818611 30385229283241250992227917)
        ·
          refine ⟨11394460981215469122085469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30385229283241250992227917 11394460981215469122085469)
          ·
            refine ⟨4272922867955800920782051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11394460981215469122085469 4272922867955800920782051)
            ·
              refine ⟨6409384301933701381173077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272922867955800920782051 6409384301933701381173077)
              ·
                refine ⟨37554986144142781530311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6409384301933701381173077 37554986144142781530311)
                ·
                  rfl

theorem cell23_1974728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 9].length) (baseStart_1974728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974728 prefixEnd_1974728 := by exact prefixLift 1974728
  have htrace : WordTrace (prefixWord ++ tailWord_1974728) baseStart_1974728 baseEnd_1974728 := by
    simpa [prefixWord, tailWord_1974728, baseEnd_1974728] using wordTrace_append hprefix tailTrace_1974728
  have hstable : (prefixWord ++ tailWord_1974728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974728).length < 2 ^ (prefixWord ++ tailWord_1974728).sum := by decide
  have hdescent : baseEnd_1974728 < baseStart_1974728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974742 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1974742 : Nat := 118140960795 + 1974742 * 2 ^ 59
def prefixEnd_1974742 : Nat := 4983230072969 + 3 ^ 40 * 1974742 * 2
def baseEnd_1974742 : Nat := 1013991814621018046543333

theorem tailTrace_1974742 : CollatzResearch.WordTrace tailWord_1974742 prefixEnd_1974742 1013991814621018046543333 := by
  unfold tailWord_1974742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501547363240904245508905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48016505207902978618761653 4501547363240904245508905)
  ·
    refine ⟨3376160522430678184131679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4501547363240904245508905 3376160522430678184131679)
    ·
      refine ⟨5064240783646017276197519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376160522430678184131679 5064240783646017276197519)
      ·
        refine ⟨7596361175469025914296279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064240783646017276197519 7596361175469025914296279)
        ·
          refine ⟨11394541763203538871444419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7596361175469025914296279 11394541763203538871444419)
          ·
            refine ⟨17091812644805308307166629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11394541763203538871444419 17091812644805308307166629)
            ·
              refine ⟨3204714870900995307593743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17091812644805308307166629 3204714870900995307593743)
              ·
                refine ⟨4807072306351492961390615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204714870900995307593743 4807072306351492961390615)
                ·
                  refine ⟨7210608459527239442085923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807072306351492961390615 7210608459527239442085923)
                  ·
                    refine ⟨10815912689290859163128885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7210608459527239442085923 10815912689290859163128885)
                    ·
                      refine ⟨1013991814621018046543333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10815912689290859163128885 1013991814621018046543333)
                      ·
                        rfl

theorem cell23_1974742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1974742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974742 prefixEnd_1974742 := by exact prefixLift 1974742
  have htrace : WordTrace (prefixWord ++ tailWord_1974742) baseStart_1974742 baseEnd_1974742 := by
    simpa [prefixWord, tailWord_1974742, baseEnd_1974742] using wordTrace_append hprefix tailTrace_1974742
  have hstable : (prefixWord ++ tailWord_1974742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974742).length < 2 ^ (prefixWord ++ tailWord_1974742).sum := by decide
  have hdescent : baseEnd_1974742 < baseStart_1974742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974778 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1974778 : Nat := 118140960795 + 1974778 * 2 ^ 59
def prefixEnd_1974778 : Nat := 4983230072969 + 3 ^ 40 * 1974778 * 2
def baseEnd_1974778 : Nat := 1014010299924579905693167

theorem tailTrace_1974778 : CollatzResearch.WordTrace tailWord_1974778 prefixEnd_1974778 1014010299924579905693167 := by
  unfold tailWord_1974778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006517709931011519113247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48017380559816030717635325 18006517709931011519113247)
  ·
    refine ⟨27009776564896517278669871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18006517709931011519113247 27009776564896517278669871)
    ·
      refine ⟨40514664847344775918004807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27009776564896517278669871 40514664847344775918004807)
      ·
        refine ⟨60771997271017163877007211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40514664847344775918004807 60771997271017163877007211)
        ·
          refine ⟨91157995906525745815510817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60771997271017163877007211 91157995906525745815510817)
          ·
            refine ⟨68368496929894309361633113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91157995906525745815510817 68368496929894309361633113)
            ·
              refine ⟨51276372697420732021224835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68368496929894309361633113 51276372697420732021224835)
              ·
                refine ⟨76914559046131098031837253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51276372697420732021224835 76914559046131098031837253)
                ·
                  refine ⟨14421479821149580880969485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76914559046131098031837253 14421479821149580880969485)
                  ·
                    refine ⟨5408054932931092830363557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14421479821149580880969485 5408054932931092830363557)
                    ·
                      refine ⟨1014010299924579905693167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5408054932931092830363557 1014010299924579905693167)
                      ·
                        rfl

theorem cell23_1974778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1974778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974778 prefixEnd_1974778 := by exact prefixLift 1974778
  have htrace : WordTrace (prefixWord ++ tailWord_1974778) baseStart_1974778 baseEnd_1974778 := by
    simpa [prefixWord, tailWord_1974778, baseEnd_1974778] using wordTrace_append hprefix tailTrace_1974778
  have hstable : (prefixWord ++ tailWord_1974778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974778).length < 2 ^ (prefixWord ++ tailWord_1974778).sum := by decide
  have hdescent : baseEnd_1974778 < baseStart_1974778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1974807 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1974807 : Nat := 118140960795 + 1974807 * 2 ^ 59
def prefixEnd_1974807 : Nat := 4983230072969 + 3 ^ 40 * 1974807 * 2
def baseEnd_1974807 : Nat := 1014025190863560292230535

theorem tailTrace_1974807 : CollatzResearch.WordTrace tailWord_1974807 prefixEnd_1974807 1014025190863560292230535 := by
  unfold tailWord_1974807
  simp only [CollatzResearch.WordTrace]
  refine ⟨72027128556618984029258675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48018085704412656019505783 72027128556618984029258675)
  ·
    refine ⟨108040692834928476043888013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72027128556618984029258675 108040692834928476043888013)
    ·
      refine ⟨40515259813098178516458005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108040692834928476043888013 40515259813098178516458005)
      ·
        refine ⟨1899152803738977117958969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40515259813098178516458005 1899152803738977117958969)
        ·
          refine ⟨1424364602804232838469227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899152803738977117958969 1424364602804232838469227)
          ·
            refine ⟨2136546904206349257703841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424364602804232838469227 2136546904206349257703841)
            ·
              refine ⟨1602410178154761943277881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136546904206349257703841 1602410178154761943277881)
              ·
                refine ⟨1201807633616071457458411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602410178154761943277881 1201807633616071457458411)
                ·
                  refine ⟨1802711450424107186187617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201807633616071457458411 1802711450424107186187617)
                  ·
                    refine ⟨1352033587818080389640713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1802711450424107186187617 1352033587818080389640713)
                    ·
                      refine ⟨1014025190863560292230535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352033587818080389640713 1014025190863560292230535)
                      ·
                        rfl

theorem cell23_1974807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1974807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1974807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1974807 prefixEnd_1974807 := by exact prefixLift 1974807
  have htrace : WordTrace (prefixWord ++ tailWord_1974807) baseStart_1974807 baseEnd_1974807 := by
    simpa [prefixWord, tailWord_1974807, baseEnd_1974807] using wordTrace_append hprefix tailTrace_1974807
  have hstable : (prefixWord ++ tailWord_1974807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1974807).length < 2 ^ (prefixWord ++ tailWord_1974807).sum := by decide
  have hdescent : baseEnd_1974807 < baseStart_1974807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1974807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975002 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 1, 6]
def baseStart_1975002 : Nat := 118140960795 + 1975002 * 2 ^ 59
def prefixEnd_1975002 : Nat := 4983230072969 + 3 ^ 40 * 1975002 * 2
def baseEnd_1975002 : Nat := 338041773197062343097379

theorem tailTrace_1975002 : CollatzResearch.WordTrace tailWord_1975002 prefixEnd_1975002 338041773197062343097379 := by
  unfold tailWord_1975002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008560197728133083151815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48022827193941688221738173 18008560197728133083151815)
  ·
    refine ⟨27012840296592199624727723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008560197728133083151815 27012840296592199624727723)
    ·
      refine ⟨40519260444888299437091585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27012840296592199624727723 40519260444888299437091585)
      ·
        refine ⟨30389445333666224577818689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40519260444888299437091585 30389445333666224577818689)
        ·
          refine ⟨22792084000249668433364017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30389445333666224577818689 22792084000249668433364017)
          ·
            refine ⟨17094063000187251325023013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22792084000249668433364017 17094063000187251325023013)
            ·
              refine ⟨3205136812535109623441815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17094063000187251325023013 3205136812535109623441815)
              ·
                refine ⟨4807705218802664435162723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205136812535109623441815 4807705218802664435162723)
                ·
                  refine ⟨7211557828203996652744085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4807705218802664435162723 7211557828203996652744085)
                  ·
                    refine ⟨338041773197062343097379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7211557828203996652744085 338041773197062343097379)
                    ·
                      rfl

theorem cell23_1975002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_1975002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975002 prefixEnd_1975002 := by exact prefixLift 1975002
  have htrace : WordTrace (prefixWord ++ tailWord_1975002) baseStart_1975002 baseEnd_1975002 := by
    simpa [prefixWord, tailWord_1975002, baseEnd_1975002] using wordTrace_append hprefix tailTrace_1975002
  have hstable : (prefixWord ++ tailWord_1975002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975002).length < 2 ^ (prefixWord ++ tailWord_1975002).sum := by decide
  have hdescent : baseEnd_1975002 < baseStart_1975002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975026 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_1975026 : Nat := 118140960795 + 1975026 * 2 ^ 59
def prefixEnd_1975026 : Nat := 4983230072969 + 3 ^ 40 * 1975026 * 2
def baseEnd_1975026 : Nat := 1014137643126894935392027

theorem tailTrace_1975026 : CollatzResearch.WordTrace tailWord_1975026 prefixEnd_1975026 1014137643126894935392027 := by
  unfold tailWord_1975026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008779035706396107870233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48023410761883722954320621 18008779035706396107870233)
  ·
    refine ⟨13506584276779797080902675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18008779035706396107870233 13506584276779797080902675)
    ·
      refine ⟨20259876415169695621354013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13506584276779797080902675 20259876415169695621354013)
      ·
        refine ⟨7597453655688635858007755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20259876415169695621354013 7597453655688635858007755)
        ·
          refine ⟨11396180483532953787011633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597453655688635858007755 11396180483532953787011633)
          ·
            refine ⟨8547135362649715340258725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11396180483532953787011633 8547135362649715340258725)
            ·
              refine ⟨1602587880496821626298511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8547135362649715340258725 1602587880496821626298511)
              ·
                refine ⟨2403881820745232439447767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602587880496821626298511 2403881820745232439447767)
                ·
                  refine ⟨3605822731117848659171651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2403881820745232439447767 3605822731117848659171651)
                  ·
                    refine ⟨5408734096676772988757477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3605822731117848659171651 5408734096676772988757477)
                    ·
                      refine ⟨1014137643126894935392027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5408734096676772988757477 1014137643126894935392027)
                      ·
                        rfl

theorem cell23_1975026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_1975026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975026 prefixEnd_1975026 := by exact prefixLift 1975026
  have htrace : WordTrace (prefixWord ++ tailWord_1975026) baseStart_1975026 baseEnd_1975026 := by
    simpa [prefixWord, tailWord_1975026, baseEnd_1975026] using wordTrace_append hprefix tailTrace_1975026
  have hstable : (prefixWord ++ tailWord_1975026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975026).length < 2 ^ (prefixWord ++ tailWord_1975026).sum := by decide
  have hdescent : baseEnd_1975026 < baseStart_1975026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975036 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_1975036 : Nat := 118140960795 + 1975036 * 2 ^ 59
def prefixEnd_1975036 : Nat := 4983230072969 + 3 ^ 40 * 1975036 * 2
def baseEnd_1975036 : Nat := 338047592644479965422327

theorem tailTrace_1975036 : CollatzResearch.WordTrace tailWord_1975036 prefixEnd_1975036 338047592644479965422327 := by
  unfold tailWord_1975036
  simp only [CollatzResearch.WordTrace]
  refine ⟨36017740436394678069672481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48023653915192904092896641 36017740436394678069672481)
  ·
    refine ⟨27013305327296008552254361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36017740436394678069672481 27013305327296008552254361)
    ·
      refine ⟨20259978995472006414190771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27013305327296008552254361 20259978995472006414190771)
      ·
        refine ⟨30389968493208009621286157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20259978995472006414190771 30389968493208009621286157)
        ·
          refine ⟨11396238184953003607982309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30389968493208009621286157 11396238184953003607982309)
          ·
            refine ⟨2136794659678688176496683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11396238184953003607982309 2136794659678688176496683)
            ·
              refine ⟨3205191989518032264745025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136794659678688176496683 3205191989518032264745025)
              ·
                refine ⟨2403893992138524198558769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3205191989518032264745025 2403893992138524198558769)
                ·
                  refine ⟨1802920494103893148919077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2403893992138524198558769 1802920494103893148919077)
                  ·
                    refine ⟨338047592644479965422327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1802920494103893148919077 338047592644479965422327)
                    ·
                      rfl

theorem cell23_1975036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_1975036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975036 prefixEnd_1975036 := by exact prefixLift 1975036
  have htrace : WordTrace (prefixWord ++ tailWord_1975036) baseStart_1975036 baseEnd_1975036 := by
    simpa [prefixWord, tailWord_1975036, baseEnd_1975036] using wordTrace_append hprefix tailTrace_1975036
  have hstable : (prefixWord ++ tailWord_1975036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975036).length < 2 ^ (prefixWord ++ tailWord_1975036).sum := by decide
  have hdescent : baseEnd_1975036 < baseStart_1975036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975045 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_1975045 : Nat := 118140960795 + 1975045 * 2 ^ 59
def prefixEnd_1975045 : Nat := 4983230072969 + 3 ^ 40 * 1975045 * 2
def baseEnd_1975045 : Nat := 338049133086443453684813

theorem tailTrace_1975045 : CollatzResearch.WordTrace tailWord_1975045 prefixEnd_1975045 338049133086443453684813 := by
  unfold tailWord_1975045
  simp only [CollatzResearch.WordTrace]
  refine ⟨72035809129756750676422589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48023872753171167117615059 72035809129756750676422589)
  ·
    refine ⟨27013428423658781503658471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72035809129756750676422589 27013428423658781503658471)
    ·
      refine ⟨40520142635488172255487707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27013428423658781503658471 40520142635488172255487707)
      ·
        refine ⟨60780213953232258383231561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40520142635488172255487707 60780213953232258383231561)
        ·
          refine ⟨45585160464924193787423671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60780213953232258383231561 45585160464924193787423671)
          ·
            refine ⟨68377740697386290681135507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45585160464924193787423671 68377740697386290681135507)
            ·
              refine ⟨102566611046079436021703261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68377740697386290681135507 102566611046079436021703261)
              ·
                refine ⟨38462479142279788508138723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102566611046079436021703261 38462479142279788508138723)
                ·
                  refine ⟨57693718713419682762208085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38462479142279788508138723 57693718713419682762208085)
                  ·
                    refine ⟨338049133086443453684813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 57693718713419682762208085 338049133086443453684813)
                    ·
                      rfl

theorem cell23_1975045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_1975045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975045 prefixEnd_1975045 := by exact prefixLift 1975045
  have htrace : WordTrace (prefixWord ++ tailWord_1975045) baseStart_1975045 baseEnd_1975045 := by
    simpa [prefixWord, tailWord_1975045, baseEnd_1975045] using wordTrace_append hprefix tailTrace_1975045
  have hstable : (prefixWord ++ tailWord_1975045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975045).length < 2 ^ (prefixWord ++ tailWord_1975045).sum := by decide
  have hdescent : baseEnd_1975045 < baseStart_1975045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975065 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1975065 : Nat := 118140960795 + 1975065 * 2 ^ 59
def prefixEnd_1975065 : Nat := 4983230072969 + 3 ^ 40 * 1975065 * 2
def baseEnd_1975065 : Nat := 1014157668872420282804347

theorem tailTrace_1975065 : CollatzResearch.WordTrace tailWord_1975065 prefixEnd_1975065 1014157668872420282804347 := by
  unfold tailWord_1975065
  simp only [CollatzResearch.WordTrace]
  refine ⟨72036538589684294092150649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48024359059789529394767099 72036538589684294092150649)
  ·
    refine ⟨54027403942263220569112987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72036538589684294092150649 54027403942263220569112987)
    ·
      refine ⟨81041105913394830853669481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54027403942263220569112987 81041105913394830853669481)
      ·
        refine ⟨60780829435046123140252111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81041105913394830853669481 60780829435046123140252111)
        ·
          refine ⟨91171244152569184710378167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60780829435046123140252111 91171244152569184710378167)
          ·
            refine ⟨136756866228853777065567251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91171244152569184710378167 136756866228853777065567251)
            ·
              refine ⟨205135299343280665598350877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136756866228853777065567251 205135299343280665598350877)
              ·
                refine ⟨76925737253730249599381579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205135299343280665598350877 76925737253730249599381579)
                ·
                  refine ⟨115388605880595374399072369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76925737253730249599381579 115388605880595374399072369)
                  ·
                    refine ⟨86541454410446530799304277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115388605880595374399072369 86541454410446530799304277)
                    ·
                      refine ⟨1014157668872420282804347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 86541454410446530799304277 1014157668872420282804347)
                      ·
                        rfl

theorem cell23_1975065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1975065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975065 prefixEnd_1975065 := by exact prefixLift 1975065
  have htrace : WordTrace (prefixWord ++ tailWord_1975065) baseStart_1975065 baseEnd_1975065 := by
    simpa [prefixWord, tailWord_1975065, baseEnd_1975065] using wordTrace_append hprefix tailTrace_1975065
  have hstable : (prefixWord ++ tailWord_1975065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975065).length < 2 ^ (prefixWord ++ tailWord_1975065).sum := by decide
  have hdescent : baseEnd_1975065 < baseStart_1975065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975072 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1975072 : Nat := 118140960795 + 1975072 * 2 ^ 59
def prefixEnd_1975072 : Nat := 4983230072969 + 3 ^ 40 * 1975072 * 2
def baseEnd_1975072 : Nat := 1014161263237001755416815

theorem tailTrace_1975072 : CollatzResearch.WordTrace tailWord_1975072 prefixEnd_1975072 1014161263237001755416815 := by
  unfold tailWord_1975072
  simp only [CollatzResearch.WordTrace]
  refine ⟨36018396950329467143827735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48024529267105956191770313 36018396950329467143827735)
  ·
    refine ⟨54027595425494200715741603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36018396950329467143827735 54027595425494200715741603)
    ·
      refine ⟨81041393138241301073612405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54027595425494200715741603 81041393138241301073612405)
      ·
        refine ⟨7597630606710121975651163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81041393138241301073612405 7597630606710121975651163)
        ·
          refine ⟨11396445910065182963476745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597630606710121975651163 11396445910065182963476745)
          ·
            refine ⟨8547334432548887222607559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11396445910065182963476745 8547334432548887222607559)
            ·
              refine ⟨12821001648823330833911339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547334432548887222607559 12821001648823330833911339)
              ·
                refine ⟨19231502473234996250867009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821001648823330833911339 19231502473234996250867009)
                ·
                  refine ⟨14423626854926247188150257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19231502473234996250867009 14423626854926247188150257)
                  ·
                    refine ⟨10817720141194685391112693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14423626854926247188150257 10817720141194685391112693)
                    ·
                      refine ⟨1014161263237001755416815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10817720141194685391112693 1014161263237001755416815)
                      ·
                        rfl

theorem cell23_1975072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1975072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975072 prefixEnd_1975072 := by exact prefixLift 1975072
  have htrace : WordTrace (prefixWord ++ tailWord_1975072) baseStart_1975072 baseEnd_1975072 := by
    simpa [prefixWord, tailWord_1975072, baseEnd_1975072] using wordTrace_append hprefix tailTrace_1975072
  have hstable : (prefixWord ++ tailWord_1975072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975072).length < 2 ^ (prefixWord ++ tailWord_1975072).sum := by decide
  have hdescent : baseEnd_1975072 < baseStart_1975072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975094 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_1975094 : Nat := 118140960795 + 1975094 * 2 ^ 59
def prefixEnd_1975094 : Nat := 4983230072969 + 3 ^ 40 * 1975094 * 2
def baseEnd_1975094 : Nat := 1014172559811400669341715

theorem tailTrace_1975094 : CollatzResearch.WordTrace tailWord_1975094 prefixEnd_1975094 1014172559811400669341715 := by
  unfold tailWord_1975094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502349769161202002809771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48025064204386154696637557 4502349769161202002809771)
  ·
    refine ⟨6753524653741803004214657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4502349769161202002809771 6753524653741803004214657)
    ·
      refine ⟨5065143490306352253160993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6753524653741803004214657 5065143490306352253160993)
      ·
        refine ⟨3798857617729764189870745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5065143490306352253160993 3798857617729764189870745)
        ·
          refine ⟨2849143213297323142403059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798857617729764189870745 2849143213297323142403059)
          ·
            refine ⟨4273714819945984713604589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849143213297323142403059 4273714819945984713604589)
            ·
              refine ⟨1602643057479744267601721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4273714819945984713604589 1602643057479744267601721)
              ·
                refine ⟨1201982293109808200701291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602643057479744267601721 1201982293109808200701291)
                ·
                  refine ⟨1802973439664712301051937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201982293109808200701291 1802973439664712301051937)
                  ·
                    refine ⟨1352230079748534225788953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1802973439664712301051937 1352230079748534225788953)
                    ·
                      refine ⟨1014172559811400669341715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352230079748534225788953 1014172559811400669341715)
                      ·
                        rfl

theorem cell23_1975094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_1975094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975094 prefixEnd_1975094 := by exact prefixLift 1975094
  have htrace : WordTrace (prefixWord ++ tailWord_1975094) baseStart_1975094 baseEnd_1975094 := by
    simpa [prefixWord, tailWord_1975094, baseEnd_1975094] using wordTrace_append hprefix tailTrace_1975094
  have hstable : (prefixWord ++ tailWord_1975094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975094).length < 2 ^ (prefixWord ++ tailWord_1975094).sum := by decide
  have hdescent : baseEnd_1975094 < baseStart_1975094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975112 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1975112 : Nat := 118140960795 + 1975112 * 2 ^ 59
def prefixEnd_1975112 : Nat := 4983230072969 + 3 ^ 40 * 1975112 * 2
def baseEnd_1975112 : Nat := 1014181802463181598916631

theorem tailTrace_1975112 : CollatzResearch.WordTrace tailWord_1975112 prefixEnd_1975112 1014181802463181598916631 := by
  unfold tailWord_1975112
  simp only [CollatzResearch.WordTrace]
  refine ⟨36019126410257010559555795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48025501880342680746074393 36019126410257010559555795)
  ·
    refine ⟨54028689615385515839333693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36019126410257010559555795 54028689615385515839333693)
    ·
      refine ⟨20260758605769568439750135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54028689615385515839333693 20260758605769568439750135)
      ·
        refine ⟨30391137908654352659625203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20260758605769568439750135 30391137908654352659625203)
        ·
          refine ⟨45586706862981528989437805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30391137908654352659625203 45586706862981528989437805)
          ·
            refine ⟨17095015073618073371039177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45586706862981528989437805 17095015073618073371039177)
            ·
              refine ⟨12821261305213555028279383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17095015073618073371039177 12821261305213555028279383)
              ·
                refine ⟨19231891957820332542419075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821261305213555028279383 19231891957820332542419075)
                ·
                  refine ⟨28847837936730498813628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19231891957820332542419075 28847837936730498813628613)
                  ·
                    refine ⟨5408969613136968527555365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28847837936730498813628613 5408969613136968527555365)
                    ·
                      refine ⟨1014181802463181598916631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5408969613136968527555365 1014181802463181598916631)
                      ·
                        rfl

theorem cell23_1975112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1975112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975112 prefixEnd_1975112 := by exact prefixLift 1975112
  have htrace : WordTrace (prefixWord ++ tailWord_1975112) baseStart_1975112 baseEnd_1975112 := by
    simpa [prefixWord, tailWord_1975112, baseEnd_1975112] using wordTrace_append hprefix tailTrace_1975112
  have hstable : (prefixWord ++ tailWord_1975112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975112).length < 2 ^ (prefixWord ++ tailWord_1975112).sum := by decide
  have hdescent : baseEnd_1975112 < baseStart_1975112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975122 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 9]
def baseStart_1975122 : Nat := 118140960795 + 1975122 * 2 ^ 59
def prefixEnd_1975122 : Nat := 4983230072969 + 3 ^ 40 * 1975122 * 2
def baseEnd_1975122 : Nat := 112687437474414062199065

theorem tailTrace_1975122 : CollatzResearch.WordTrace tailWord_1975122 prefixEnd_1975122 112687437474414062199065 := by
  unfold tailWord_1975122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18009654387619448206743905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48025745033651861884650413 18009654387619448206743905)
  ·
    refine ⟨13507240790714586155057929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18009654387619448206743905 13507240790714586155057929)
    ·
      refine ⟨10130430593035939616293447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13507240790714586155057929 10130430593035939616293447)
      ·
        refine ⟨15195645889553909424440171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10130430593035939616293447 15195645889553909424440171)
        ·
          refine ⟨22793468834330864136660257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15195645889553909424440171 22793468834330864136660257)
          ·
            refine ⟨17095101625748148102495193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22793468834330864136660257 17095101625748148102495193)
            ·
              refine ⟨12821326219311111076871395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17095101625748148102495193 12821326219311111076871395)
              ·
                refine ⟨19231989328966666615307093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821326219311111076871395 19231989328966666615307093)
                ·
                  refine ⟨112687437474414062199065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19231989328966666615307093 112687437474414062199065)
                  ·
                    rfl

theorem cell23_1975122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_1975122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975122 prefixEnd_1975122 := by exact prefixLift 1975122
  have htrace : WordTrace (prefixWord ++ tailWord_1975122) baseStart_1975122 baseEnd_1975122 := by
    simpa [prefixWord, tailWord_1975122, baseEnd_1975122] using wordTrace_append hprefix tailTrace_1975122
  have hstable : (prefixWord ++ tailWord_1975122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975122).length < 2 ^ (prefixWord ++ tailWord_1975122).sum := by decide
  have hdescent : baseEnd_1975122 < baseStart_1975122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975149 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1975149 : Nat := 118140960795 + 1975149 * 2 ^ 59
def prefixEnd_1975149 : Nat := 4983230072969 + 3 ^ 40 * 1975149 * 2
def baseEnd_1975149 : Nat := 1014200801247397954153961

theorem tailTrace_1975149 : CollatzResearch.WordTrace tailWord_1975149 prefixEnd_1975149 1014200801247397954153961 := by
  unfold tailWord_1975149
  simp only [CollatzResearch.WordTrace]
  refine ⟨72039602321379976438208501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48026401547586650958805667 72039602321379976438208501)
  ·
    refine ⟨6753712717629372791082047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72039602321379976438208501 6753712717629372791082047)
    ·
      refine ⟨10130569076444059186623071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6753712717629372791082047 10130569076444059186623071)
      ·
        refine ⟨15195853614666088779934607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10130569076444059186623071 15195853614666088779934607)
        ·
          refine ⟨22793780421999133169901911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15195853614666088779934607 22793780421999133169901911)
          ·
            refine ⟨34190670632998699754852867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22793780421999133169901911 34190670632998699754852867)
            ·
              refine ⟨51286005949498049632279301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34190670632998699754852867 51286005949498049632279301)
              ·
                refine ⟨9616126115530884306052369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51286005949498049632279301 9616126115530884306052369)
                ·
                  refine ⟨7212094586648163229539277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9616126115530884306052369 7212094586648163229539277)
                  ·
                    refine ⟨2704535469993061211077229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7212094586648163229539277 2704535469993061211077229)
                    ·
                      refine ⟨1014200801247397954153961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2704535469993061211077229 1014200801247397954153961)
                      ·
                        rfl

theorem cell23_1975149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1975149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975149 prefixEnd_1975149 := by exact prefixLift 1975149
  have htrace : WordTrace (prefixWord ++ tailWord_1975149) baseStart_1975149 baseEnd_1975149 := by
    simpa [prefixWord, tailWord_1975149, baseEnd_1975149] using wordTrace_append hprefix tailTrace_1975149
  have hstable : (prefixWord ++ tailWord_1975149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975149).length < 2 ^ (prefixWord ++ tailWord_1975149).sum := by decide
  have hdescent : baseEnd_1975149 < baseStart_1975149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975186 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1975186 : Nat := 118140960795 + 1975186 * 2 ^ 59
def prefixEnd_1975186 : Nat := 4983230072969 + 3 ^ 40 * 1975186 * 2
def baseEnd_1975186 : Nat := 338073266677204769797097

theorem tailTrace_1975186 : CollatzResearch.WordTrace tailWord_1975186 prefixEnd_1975186 338073266677204769797097 := by
  unfold tailWord_1975186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010237955561482939326353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48027301214830621171536941 18010237955561482939326353)
  ·
    refine ⟨13507678466671112204494765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18010237955561482939326353 13507678466671112204494765)
    ·
      refine ⟨5065379425001667076685537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13507678466671112204494765 5065379425001667076685537)
      ·
        refine ⟨3799034568751250307514153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5065379425001667076685537 3799034568751250307514153)
        ·
          refine ⟨2849275926563437730635615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799034568751250307514153 2849275926563437730635615)
          ·
            refine ⟨4273913889845156595953423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849275926563437730635615 4273913889845156595953423)
            ·
              refine ⟨6410870834767734893930135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273913889845156595953423 6410870834767734893930135)
              ·
                refine ⟨9616306252151602340895203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6410870834767734893930135 9616306252151602340895203)
                ·
                  refine ⟨14424459378227403511342805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616306252151602340895203 14424459378227403511342805)
                  ·
                    refine ⟨338073266677204769797097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14424459378227403511342805 338073266677204769797097)
                    ·
                      rfl

theorem cell23_1975186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1975186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975186 prefixEnd_1975186 := by exact prefixLift 1975186
  have htrace : WordTrace (prefixWord ++ tailWord_1975186) baseStart_1975186 baseEnd_1975186 := by
    simpa [prefixWord, tailWord_1975186, baseEnd_1975186] using wordTrace_append hprefix tailTrace_1975186
  have hstable : (prefixWord ++ tailWord_1975186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975186).length < 2 ^ (prefixWord ++ tailWord_1975186).sum := by decide
  have hdescent : baseEnd_1975186 < baseStart_1975186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975189 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1975189 : Nat := 118140960795 + 1975189 * 2 ^ 59
def prefixEnd_1975189 : Nat := 4983230072969 + 3 ^ 40 * 1975189 * 2
def baseEnd_1975189 : Nat := 1014221340473577797653777

theorem tailTrace_1975189 : CollatzResearch.WordTrace tailWord_1975189 prefixEnd_1975189 1014221340473577797653777 := by
  unfold tailWord_1975189
  simp only [CollatzResearch.WordTrace]
  refine ⟨72041061241235063269664621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48027374160823375513109747 72041061241235063269664621)
  ·
    refine ⟨27015397965463148726124233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72041061241235063269664621 27015397965463148726124233)
    ·
      refine ⟨20261548474097361544593175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27015397965463148726124233 20261548474097361544593175)
      ·
        refine ⟨30392322711146042316889763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20261548474097361544593175 30392322711146042316889763)
        ·
          refine ⟨45588484066719063475334645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30392322711146042316889763 45588484066719063475334645)
          ·
            refine ⟨4273920381254912200812623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45588484066719063475334645 4273920381254912200812623)
            ·
              refine ⟨6410880571882368301218935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273920381254912200812623 6410880571882368301218935)
              ·
                refine ⟨9616320857823552451828403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6410880571882368301218935 9616320857823552451828403)
                ·
                  refine ⟨14424481286735328677742605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9616320857823552451828403 14424481286735328677742605)
                  ·
                    refine ⟨5409180482525748254153477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14424481286735328677742605 5409180482525748254153477)
                    ·
                      refine ⟨1014221340473577797653777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5409180482525748254153477 1014221340473577797653777)
                      ·
                        rfl

theorem cell23_1975189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1975189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975189 prefixEnd_1975189 := by exact prefixLift 1975189
  have htrace : WordTrace (prefixWord ++ tailWord_1975189) baseStart_1975189 baseEnd_1975189 := by
    simpa [prefixWord, tailWord_1975189, baseEnd_1975189] using wordTrace_append hprefix tailTrace_1975189
  have hstable : (prefixWord ++ tailWord_1975189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975189).length < 2 ^ (prefixWord ++ tailWord_1975189).sum := by decide
  have hdescent : baseEnd_1975189 < baseStart_1975189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975190 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1975190 : Nat := 118140960795 + 1975190 * 2 ^ 59
def prefixEnd_1975190 : Nat := 4983230072969 + 3 ^ 40 * 1975190 * 2
def baseEnd_1975190 : Nat := 112691317106025810415697

theorem tailTrace_1975190 : CollatzResearch.WordTrace tailWord_1975190 prefixEnd_1975190 112691317106025810415697 := by
  unfold tailWord_1975190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4502568607139465027528189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48027398476154293626967349 4502568607139465027528189)
  ·
    refine ⟨1688463227677299385323071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4502568607139465027528189 1688463227677299385323071)
    ·
      refine ⟨2532694841515949077984607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688463227677299385323071 2532694841515949077984607)
      ·
        refine ⟨3799042262273923616976911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532694841515949077984607 3799042262273923616976911)
        ·
          refine ⟨5698563393410885425465367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799042262273923616976911 5698563393410885425465367)
          ·
            refine ⟨8547845090116328138198051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698563393410885425465367 8547845090116328138198051)
            ·
              refine ⟨12821767635174492207297077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8547845090116328138198051 12821767635174492207297077)
              ·
                refine ⟨1202040715797608644434101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12821767635174492207297077 1202040715797608644434101)
                ·
                  refine ⟨112691317106025810415697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1202040715797608644434101 112691317106025810415697)
                  ·
                    rfl

theorem cell23_1975190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1975190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975190 prefixEnd_1975190 := by exact prefixLift 1975190
  have htrace : WordTrace (prefixWord ++ tailWord_1975190) baseStart_1975190 baseEnd_1975190 := by
    simpa [prefixWord, tailWord_1975190, baseEnd_1975190] using wordTrace_append hprefix tailTrace_1975190
  have hstable : (prefixWord ++ tailWord_1975190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975190).length < 2 ^ (prefixWord ++ tailWord_1975190).sum := by decide
  have hdescent : baseEnd_1975190 < baseStart_1975190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975209 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_1975209 : Nat := 118140960795 + 1975209 * 2 ^ 59
def prefixEnd_1975209 : Nat := 4983230072969 + 3 ^ 40 * 1975209 * 2
def baseEnd_1975209 : Nat := 1014231610086667719403685

theorem tailTrace_1975209 : CollatzResearch.WordTrace tailWord_1975209 prefixEnd_1975209 1014231610086667719403685 := by
  unfold tailWord_1975209
  simp only [CollatzResearch.WordTrace]
  refine ⟨72041790701162606685392681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48027860467441737790261787 72041790701162606685392681)
  ·
    refine ⟨54031343025871955014044511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72041790701162606685392681 54031343025871955014044511)
    ·
      refine ⟨81047014538807932521066767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54031343025871955014044511 81047014538807932521066767)
      ·
        refine ⟨121570521808211898781600151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81047014538807932521066767 121570521808211898781600151)
        ·
          refine ⟨182355782712317848172400227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121570521808211898781600151 182355782712317848172400227)
          ·
            refine ⟨273533674068476772258600341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182355782712317848172400227 273533674068476772258600341)
            ·
              refine ⟨12821890971959848699621891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 273533674068476772258600341 12821890971959848699621891)
              ·
                refine ⟨19232836457939773049432837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12821890971959848699621891 19232836457939773049432837)
                ·
                  refine ⟨3606156835863707446768657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19232836457939773049432837 3606156835863707446768657)
                  ·
                    refine ⟨2704617626897780585076493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606156835863707446768657 2704617626897780585076493)
                    ·
                      refine ⟨1014231610086667719403685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2704617626897780585076493 1014231610086667719403685)
                      ·
                        rfl

theorem cell23_1975209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_1975209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975209 prefixEnd_1975209 := by exact prefixLift 1975209
  have htrace : WordTrace (prefixWord ++ tailWord_1975209) baseStart_1975209 baseEnd_1975209 := by
    simpa [prefixWord, tailWord_1975209, baseEnd_1975209] using wordTrace_append hprefix tailTrace_1975209
  have hstable : (prefixWord ++ tailWord_1975209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975209).length < 2 ^ (prefixWord ++ tailWord_1975209).sum := by decide
  have hdescent : baseEnd_1975209 < baseStart_1975209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975212 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 8]
def baseStart_1975212 : Nat := 118140960795 + 1975212 * 2 ^ 59
def prefixEnd_1975212 : Nat := 4983230072969 + 3 ^ 40 * 1975212 * 2
def baseEnd_1975212 : Nat := 112692572280959023074019

theorem tailTrace_1975212 : CollatzResearch.WordTrace tailWord_1975212 prefixEnd_1975212 112692572280959023074019 := by
  unfold tailWord_1975212
  simp only [CollatzResearch.WordTrace]
  refine ⟨36020950060075869098875945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48027933413434492131834593 36020950060075869098875945)
  ·
    refine ⟨27015712545056901824156959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36020950060075869098875945 27015712545056901824156959)
    ·
      refine ⟨40523568817585352736235439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27015712545056901824156959 40523568817585352736235439)
      ·
        refine ⟨60785353226378029104353159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40523568817585352736235439 60785353226378029104353159)
        ·
          refine ⟨91178029839567043656529739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60785353226378029104353159 91178029839567043656529739)
          ·
            refine ⟨136767044759350565484794609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91178029839567043656529739 136767044759350565484794609)
            ·
              refine ⟨102575283569512924113595957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136767044759350565484794609 102575283569512924113595957)
              ·
                refine ⟨9616432834641836635649621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102575283569512924113595957 9616432834641836635649621)
                ·
                  refine ⟨112692572280959023074019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9616432834641836635649621 112692572280959023074019)
                  ·
                    rfl

theorem cell23_1975212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_1975212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975212 prefixEnd_1975212 := by exact prefixLift 1975212
  have htrace : WordTrace (prefixWord ++ tailWord_1975212) baseStart_1975212 baseEnd_1975212 := by
    simpa [prefixWord, tailWord_1975212, baseEnd_1975212] using wordTrace_append hprefix tailTrace_1975212
  have hstable : (prefixWord ++ tailWord_1975212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975212).length < 2 ^ (prefixWord ++ tailWord_1975212).sum := by decide
  have hdescent : baseEnd_1975212 < baseStart_1975212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975250 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1975250 : Nat := 118140960795 + 1975250 * 2 ^ 59
def prefixEnd_1975250 : Nat := 4983230072969 + 3 ^ 40 * 1975250 * 2
def baseEnd_1975250 : Nat := 338084220931167352996999

theorem tailTrace_1975250 : CollatzResearch.WordTrace tailWord_1975250 prefixEnd_1975250 338084220931167352996999 := by
  unfold tailWord_1975250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010821523503517671908801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48028857396009380458423469 18010821523503517671908801)
  ·
    refine ⟨13508116142627638253931601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18010821523503517671908801 13508116142627638253931601)
    ·
      refine ⟨10131087106970728690448701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13508116142627638253931601 10131087106970728690448701)
      ·
        refine ⟨3799157665114023258918263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10131087106970728690448701 3799157665114023258918263)
        ·
          refine ⟨5698736497671034888377395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799157665114023258918263 5698736497671034888377395)
          ·
            refine ⟨8548104746506552332566093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698736497671034888377395 8548104746506552332566093)
            ·
              refine ⟨3205539279939957124712285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8548104746506552332566093 3205539279939957124712285)
              ·
                refine ⟨1202077229977483921767107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3205539279939957124712285 1202077229977483921767107)
                ·
                  refine ⟨1803115844966225882650661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202077229977483921767107 1803115844966225882650661)
                  ·
                    refine ⟨338084220931167352996999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803115844966225882650661 338084220931167352996999)
                    ·
                      rfl

theorem cell23_1975250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1975250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975250 prefixEnd_1975250 := by exact prefixLift 1975250
  have htrace : WordTrace (prefixWord ++ tailWord_1975250) baseStart_1975250 baseEnd_1975250 := by
    simpa [prefixWord, tailWord_1975250, baseEnd_1975250] using wordTrace_append hprefix tailTrace_1975250
  have hstable : (prefixWord ++ tailWord_1975250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975250).length < 2 ^ (prefixWord ++ tailWord_1975250).sum := by decide
  have hdescent : baseEnd_1975250 < baseStart_1975250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975289 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_1975289 : Nat := 118140960795 + 1975289 * 2 ^ 59
def prefixEnd_1975289 : Nat := 4983230072969 + 3 ^ 40 * 1975289 * 2
def baseEnd_1975289 : Nat := 338090896179675802134439

theorem tailTrace_1975289 : CollatzResearch.WordTrace tailWord_1975289 prefixEnd_1975289 338090896179675802134439 := by
  unfold tailWord_1975289
  simp only [CollatzResearch.WordTrace]
  refine ⟨72044708540872780348304921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48029805693915186898869947 72044708540872780348304921)
  ·
    refine ⟨54033531405654585261228691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72044708540872780348304921 54033531405654585261228691)
    ·
      refine ⟨81050297108481877891843037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54033531405654585261228691 81050297108481877891843037)
      ·
        refine ⟨30393861415680704209441139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81050297108481877891843037 30393861415680704209441139)
        ·
          refine ⟨45590792123521056314161709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30393861415680704209441139 45590792123521056314161709)
          ·
            refine ⟨17096547046320396117810641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45590792123521056314161709 17096547046320396117810641)
            ·
              refine ⟨12822410284740297088357981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17096547046320396117810641 12822410284740297088357981)
              ·
                refine ⟨4808403856777611408134243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12822410284740297088357981 4808403856777611408134243)
                ·
                  refine ⟨7212605785166417112201365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808403856777611408134243 7212605785166417112201365)
                  ·
                    refine ⟨338090896179675802134439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7212605785166417112201365 338090896179675802134439)
                    ·
                      rfl

theorem cell23_1975289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_1975289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975289 prefixEnd_1975289 := by exact prefixLift 1975289
  have htrace : WordTrace (prefixWord ++ tailWord_1975289) baseStart_1975289 baseEnd_1975289 := by
    simpa [prefixWord, tailWord_1975289, baseEnd_1975289] using wordTrace_append hprefix tailTrace_1975289
  have hstable : (prefixWord ++ tailWord_1975289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975289).length < 2 ^ (prefixWord ++ tailWord_1975289).sum := by decide
  have hdescent : baseEnd_1975289 < baseStart_1975289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975306 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1975306 : Nat := 118140960795 + 1975306 * 2 ^ 59
def prefixEnd_1975306 : Nat := 4983230072969 + 3 ^ 40 * 1975306 * 2
def baseEnd_1975306 : Nat := 338093805903384613296913

theorem tailTrace_1975306 : CollatzResearch.WordTrace tailWord_1975306 prefixEnd_1975306 338093805903384613296913 := by
  unfold tailWord_1975306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18011332145452798062918443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48030219054540794834449181 18011332145452798062918443)
  ·
    refine ⟨27016998218179197094377665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18011332145452798062918443 27016998218179197094377665)
    ·
      refine ⟨20262748663634397820783249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27016998218179197094377665 20262748663634397820783249)
      ·
        refine ⟨15197061497725798365587437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20262748663634397820783249 15197061497725798365587437)
        ·
          refine ⟨5698898061647174387095289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15197061497725798365587437 5698898061647174387095289)
          ·
            refine ⟨4274173546235380790321467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5698898061647174387095289 4274173546235380790321467)
            ·
              refine ⟨6411260319353071185482201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274173546235380790321467 6411260319353071185482201)
              ·
                refine ⟨4808445239514803389111651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6411260319353071185482201 4808445239514803389111651)
                ·
                  refine ⟨7212667859272205083667477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808445239514803389111651 7212667859272205083667477)
                  ·
                    refine ⟨338093805903384613296913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7212667859272205083667477 338093805903384613296913)
                    ·
                      rfl

theorem cell23_1975306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1975306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975306 prefixEnd_1975306 := by exact prefixLift 1975306
  have htrace : WordTrace (prefixWord ++ tailWord_1975306) baseStart_1975306 baseEnd_1975306 := by
    simpa [prefixWord, tailWord_1975306, baseEnd_1975306] using wordTrace_append hprefix tailTrace_1975306
  have hstable : (prefixWord ++ tailWord_1975306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975306).length < 2 ^ (prefixWord ++ tailWord_1975306).sum := by decide
  have hdescent : baseEnd_1975306 < baseStart_1975306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975319 : List Nat := [1, 1, 3, 5, 1, 12]
def baseStart_1975319 : Nat := 118140960795 + 1975319 * 2 ^ 59
def prefixEnd_1975319 : Nat := 4983230072969 + 3 ^ 40 * 1975319 * 2
def baseEnd_1975319 : Nat := 4174025073903960037153

theorem tailTrace_1975319 : CollatzResearch.WordTrace tailWord_1975319 prefixEnd_1975319 4174025073903960037153 := by
  unfold tailWord_1975319
  simp only [CollatzResearch.WordTrace]
  refine ⟨72045802730764095471897011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48030535153842730314598007 72045802730764095471897011)
  ·
    refine ⟨108068704096146143207845517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72045802730764095471897011 108068704096146143207845517)
    ·
      refine ⟨40525764036054803702942069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108068704096146143207845517 40525764036054803702942069)
      ·
        refine ⟨3799290378380137847150819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40525764036054803702942069 3799290378380137847150819)
        ·
          refine ⟨5698935567570206770726229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799290378380137847150819 5698935567570206770726229)
          ·
            refine ⟨4174025073903960037153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5698935567570206770726229 4174025073903960037153)
            ·
              rfl

theorem cell23_1975319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 12].length) (baseStart_1975319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975319 prefixEnd_1975319 := by exact prefixLift 1975319
  have htrace : WordTrace (prefixWord ++ tailWord_1975319) baseStart_1975319 baseEnd_1975319 := by
    simpa [prefixWord, tailWord_1975319, baseEnd_1975319] using wordTrace_append hprefix tailTrace_1975319
  have hstable : (prefixWord ++ tailWord_1975319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975319).length < 2 ^ (prefixWord ++ tailWord_1975319).sum := by decide
  have hdescent : baseEnd_1975319 < baseStart_1975319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975324 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1975324 : Nat := 118140960795 + 1975324 * 2 ^ 59
def prefixEnd_1975324 : Nat := 4983230072969 + 3 ^ 40 * 1975324 * 2
def baseEnd_1975324 : Nat := 1014290660361934769465657

theorem tailTrace_1975324 : CollatzResearch.WordTrace tailWord_1975324 prefixEnd_1975324 1014290660361934769465657 := by
  unfold tailWord_1975324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36022992547872990662914513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48030656730497320883886017 36022992547872990662914513)
  ·
    refine ⟨27017244410904742997185885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36022992547872990662914513 27017244410904742997185885)
    ·
      refine ⟨10131466654089278623944707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27017244410904742997185885 10131466654089278623944707)
      ·
        refine ⟨15197199981133917935917061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131466654089278623944707 15197199981133917935917061)
        ·
          refine ⟨2849474996462609612984449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15197199981133917935917061 2849474996462609612984449)
          ·
            refine ⟨2137106247346957209738337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849474996462609612984449 2137106247346957209738337)
            ·
              refine ⟨1602829685510217907303753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137106247346957209738337 1602829685510217907303753)
              ·
                refine ⟨1202122264132663430477815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602829685510217907303753 1202122264132663430477815)
                ·
                  refine ⟨1803183396198995145716723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202122264132663430477815 1803183396198995145716723)
                  ·
                    refine ⟨2704775094298492718575085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1803183396198995145716723 2704775094298492718575085)
                    ·
                      refine ⟨1014290660361934769465657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2704775094298492718575085 1014290660361934769465657)
                      ·
                        rfl

theorem cell23_1975324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1975324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975324 prefixEnd_1975324 := by exact prefixLift 1975324
  have htrace : WordTrace (prefixWord ++ tailWord_1975324) baseStart_1975324 baseEnd_1975324 := by
    simpa [prefixWord, tailWord_1975324, baseEnd_1975324] using wordTrace_append hprefix tailTrace_1975324
  have hstable : (prefixWord ++ tailWord_1975324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975324).length < 2 ^ (prefixWord ++ tailWord_1975324).sum := by decide
  have hdescent : baseEnd_1975324 < baseStart_1975324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975349 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1975349 : Nat := 118140960795 + 1975349 * 2 ^ 59
def prefixEnd_1975349 : Nat := 4983230072969 + 3 ^ 40 * 1975349 * 2
def baseEnd_1975349 : Nat := 338101165792765723884347

theorem tailTrace_1975349 : CollatzResearch.WordTrace tailWord_1975349 prefixEnd_1975349 338101165792765723884347 := by
  unfold tailWord_1975349
  simp only [CollatzResearch.WordTrace]
  refine ⟨72046896920655410595489101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48031264613770273730326067 72046896920655410595489101)
  ·
    refine ⟨27017586345245778973308413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72046896920655410595489101 27017586345245778973308413)
    ·
      refine ⟨10131594879467167114990655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27017586345245778973308413 10131594879467167114990655)
      ·
        refine ⟨15197392319200750672485983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131594879467167114990655 15197392319200750672485983)
        ·
          refine ⟨22796088478801126008728975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15197392319200750672485983 22796088478801126008728975)
          ·
            refine ⟨34194132718201689013093463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22796088478801126008728975 34194132718201689013093463)
            ·
              refine ⟨51291199077302533519640195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34194132718201689013093463 51291199077302533519640195)
              ·
                refine ⟨76936798615953800279460293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51291199077302533519640195 76936798615953800279460293)
                ·
                  refine ⟨14425649740491337552398805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76936798615953800279460293 14425649740491337552398805)
                  ·
                    refine ⟨338101165792765723884347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14425649740491337552398805 338101165792765723884347)
                    ·
                      rfl

theorem cell23_1975349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1975349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975349 prefixEnd_1975349 := by exact prefixLift 1975349
  have htrace : WordTrace (prefixWord ++ tailWord_1975349) baseStart_1975349 baseEnd_1975349 := by
    simpa [prefixWord, tailWord_1975349, baseEnd_1975349] using wordTrace_append hprefix tailTrace_1975349
  have hstable : (prefixWord ++ tailWord_1975349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975349).length < 2 ^ (prefixWord ++ tailWord_1975349).sum := by decide
  have hdescent : baseEnd_1975349 < baseStart_1975349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975359 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_1975359 : Nat := 118140960795 + 1975359 * 2 ^ 59
def prefixEnd_1975359 : Nat := 4983230072969 + 3 ^ 40 * 1975359 * 2
def baseEnd_1975359 : Nat := 1014308632184842132527995

theorem tailTrace_1975359 : CollatzResearch.WordTrace tailWord_1975359 prefixEnd_1975359 1014308632184842132527995 := by
  unfold tailWord_1975359
  simp only [CollatzResearch.WordTrace]
  refine ⟨72047261650619182303353131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48031507767079454868902087 72047261650619182303353131)
  ·
    refine ⟨108070892475928773455029697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72047261650619182303353131 108070892475928773455029697)
    ·
      refine ⟨81053169356946580091272273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108070892475928773455029697 81053169356946580091272273)
      ·
        refine ⟨60789877017709935068454205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81053169356946580091272273 60789877017709935068454205)
        ·
          refine ⟨22796203881641225650670327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60789877017709935068454205 22796203881641225650670327)
          ·
            refine ⟨34194305822461838476005491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22796203881641225650670327 34194305822461838476005491)
            ·
              refine ⟨51291458733692757714008237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34194305822461838476005491 51291458733692757714008237)
              ·
                refine ⟨19234297025134784142753089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51291458733692757714008237 19234297025134784142753089)
                ·
                  refine ⟨14425722768851088107064817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19234297025134784142753089 14425722768851088107064817)
                  ·
                    refine ⟨10819292076638316080298613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14425722768851088107064817 10819292076638316080298613)
                    ·
                      refine ⟨1014308632184842132527995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10819292076638316080298613 1014308632184842132527995)
                      ·
                        rfl

theorem cell23_1975359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_1975359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975359 prefixEnd_1975359 := by exact prefixLift 1975359
  have htrace : WordTrace (prefixWord ++ tailWord_1975359) baseStart_1975359 baseEnd_1975359 := by
    simpa [prefixWord, tailWord_1975359, baseEnd_1975359] using wordTrace_append hprefix tailTrace_1975359
  have hstable : (prefixWord ++ tailWord_1975359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975359).length < 2 ^ (prefixWord ++ tailWord_1975359).sum := by decide
  have hdescent : baseEnd_1975359 < baseStart_1975359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975369 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_1975369 : Nat := 118140960795 + 1975369 * 2 ^ 59
def prefixEnd_1975369 : Nat := 4983230072969 + 3 ^ 40 * 1975369 * 2
def baseEnd_1975369 : Nat := 1014313766991387093402949

theorem tailTrace_1975369 : CollatzResearch.WordTrace tailWord_1975369 prefixEnd_1975369 1014313766991387093402949 := by
  unfold tailWord_1975369
  simp only [CollatzResearch.WordTrace]
  refine ⟨72047626380582954011217161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48031750920388636007478107 72047626380582954011217161)
  ·
    refine ⟨54035719785437215508412871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72047626380582954011217161 54035719785437215508412871)
    ·
      refine ⟨81053579678155823262619307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54035719785437215508412871 81053579678155823262619307)
      ·
        refine ⟨121580369517233734893928961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81053579678155823262619307 121580369517233734893928961)
        ·
          refine ⟨91185277137925301170446721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121580369517233734893928961 91185277137925301170446721)
          ·
            refine ⟨68388957853443975877835041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91185277137925301170446721 68388957853443975877835041)
            ·
              refine ⟨51291718390082981908376281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68388957853443975877835041 51291718390082981908376281)
              ·
                refine ⟨38468788792562236431282211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51291718390082981908376281 38468788792562236431282211)
                ·
                  refine ⟨57703183188843354646923317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38468788792562236431282211 57703183188843354646923317)
                  ·
                    refine ⟨5409673423954064498149061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57703183188843354646923317 5409673423954064498149061)
                    ·
                      refine ⟨1014313766991387093402949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5409673423954064498149061 1014313766991387093402949)
                      ·
                        rfl

theorem cell23_1975369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_1975369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975369 prefixEnd_1975369 := by exact prefixLift 1975369
  have htrace : WordTrace (prefixWord ++ tailWord_1975369) baseStart_1975369 baseEnd_1975369 := by
    simpa [prefixWord, tailWord_1975369, baseEnd_1975369] using wordTrace_append hprefix tailTrace_1975369
  have hstable : (prefixWord ++ tailWord_1975369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975369).length < 2 ^ (prefixWord ++ tailWord_1975369).sum := by decide
  have hdescent : baseEnd_1975369 < baseStart_1975369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975379 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 2, 6]
def baseStart_1975379 : Nat := 118140960795 + 1975379 * 2 ^ 59
def prefixEnd_1975379 : Nat := 4983230072969 + 3 ^ 40 * 1975379 * 2
def baseEnd_1975379 : Nat := 338106300599310684759301

theorem tailTrace_1975379 : CollatzResearch.WordTrace tailWord_1975379 prefixEnd_1975379 338106300599310684759301 := by
  unfold tailWord_1975379
  simp only [CollatzResearch.WordTrace]
  refine ⟨72047991110546725719081191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48031994073697817146054127 72047991110546725719081191)
  ·
    refine ⟨108071986665820088578621787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72047991110546725719081191 108071986665820088578621787)
    ·
      refine ⟨162107979998730132867932681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108071986665820088578621787 162107979998730132867932681)
      ·
        refine ⟨121580984999047599650949511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162107979998730132867932681 121580984999047599650949511)
        ·
          refine ⟨182371477498571399476424267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121580984999047599650949511 182371477498571399476424267)
          ·
            refine ⟨273557216247857099214636401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182371477498571399476424267 273557216247857099214636401)
            ·
              refine ⟨205167912185892824410977301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273557216247857099214636401 205167912185892824410977301)
              ·
                refine ⟨9617245883713726144264561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205167912185892824410977301 9617245883713726144264561)
                ·
                  refine ⟨7212934412785294608198421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9617245883713726144264561 7212934412785294608198421)
                  ·
                    refine ⟨338106300599310684759301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7212934412785294608198421 338106300599310684759301)
                    ·
                      rfl

theorem cell23_1975379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 6].length) (baseStart_1975379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975379 prefixEnd_1975379 := by exact prefixLift 1975379
  have htrace : WordTrace (prefixWord ++ tailWord_1975379) baseStart_1975379 baseEnd_1975379 := by
    simpa [prefixWord, tailWord_1975379, baseEnd_1975379] using wordTrace_append hprefix tailTrace_1975379
  have hstable : (prefixWord ++ tailWord_1975379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975379).length < 2 ^ (prefixWord ++ tailWord_1975379).sum := by decide
  have hdescent : baseEnd_1975379 < baseStart_1975379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975380 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1975380 : Nat := 118140960795 + 1975380 * 2 ^ 59
def prefixEnd_1975380 : Nat := 4983230072969 + 3 ^ 40 * 1975380 * 2
def baseEnd_1975380 : Nat := 1014319415278586550365399

theorem tailTrace_1975380 : CollatzResearch.WordTrace tailWord_1975380 prefixEnd_1975380 1014319415278586550365399 := by
  unfold tailWord_1975380
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024013791771551444933797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48032018389028735259911729 36024013791771551444933797)
  ·
    refine ⟨6754502585957165895925087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36024013791771551444933797 6754502585957165895925087)
    ·
      refine ⟨10131753878935748843887631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6754502585957165895925087 10131753878935748843887631)
      ·
        refine ⟨15197630818403623265831447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10131753878935748843887631 15197630818403623265831447)
        ·
          refine ⟨22796446227605434898747171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15197630818403623265831447 22796446227605434898747171)
          ·
            refine ⟨34194669341408152348120757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22796446227605434898747171 34194669341408152348120757)
            ·
              refine ⟨3205750250757014282636321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34194669341408152348120757 3205750250757014282636321)
              ·
                refine ⟨2404312688067760711977241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3205750250757014282636321 2404312688067760711977241)
                ·
                  refine ⟨1803234516050820533982931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404312688067760711977241 1803234516050820533982931)
                  ·
                    refine ⟨2704851774076230800974397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1803234516050820533982931 2704851774076230800974397)
                    ·
                      refine ⟨1014319415278586550365399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2704851774076230800974397 1014319415278586550365399)
                      ·
                        rfl

theorem cell23_1975380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1975380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975380 prefixEnd_1975380 := by exact prefixLift 1975380
  have htrace : WordTrace (prefixWord ++ tailWord_1975380) baseStart_1975380 baseEnd_1975380 := by
    simpa [prefixWord, tailWord_1975380, baseEnd_1975380] using wordTrace_append hprefix tailTrace_1975380
  have hstable : (prefixWord ++ tailWord_1975380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975380).length < 2 ^ (prefixWord ++ tailWord_1975380).sum := by decide
  have hdescent : baseEnd_1975380 < baseStart_1975380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975409 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 9]
def baseStart_1975409 : Nat := 118140960795 + 1975409 * 2 ^ 59
def prefixEnd_1975409 : Nat := 4983230072969 + 3 ^ 40 * 1975409 * 2
def baseEnd_1975409 : Nat := 112703811801951881878085

theorem tailTrace_1975409 : CollatzResearch.WordTrace tailWord_1975409 prefixEnd_1975409 112703811801951881878085 := by
  unfold tailWord_1975409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72049085300438040842673281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48032723533625360561782187 72049085300438040842673281)
  ·
    refine ⟨54036813975328530632004961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72049085300438040842673281 54036813975328530632004961)
    ·
      refine ⟨40527610481496397974003721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54036813975328530632004961 40527610481496397974003721)
      ·
        refine ⟨30395707861122298480502791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40527610481496397974003721 30395707861122298480502791)
        ·
          refine ⟨45593561791683447720754187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30395707861122298480502791 45593561791683447720754187)
          ·
            refine ⟨68390342687525171581131281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45593561791683447720754187 68390342687525171581131281)
            ·
              refine ⟨51292757015643878685848461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68390342687525171581131281 51292757015643878685848461)
              ·
                refine ⟨19234783880866454507193173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51292757015643878685848461 19234783880866454507193173)
                ·
                  refine ⟨112703811801951881878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19234783880866454507193173 112703811801951881878085)
                  ·
                    rfl

theorem cell23_1975409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_1975409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975409 prefixEnd_1975409 := by exact prefixLift 1975409
  have htrace : WordTrace (prefixWord ++ tailWord_1975409) baseStart_1975409 baseEnd_1975409 := by
    simpa [prefixWord, tailWord_1975409, baseEnd_1975409] using wordTrace_append hprefix tailTrace_1975409
  have hstable : (prefixWord ++ tailWord_1975409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975409).length < 2 ^ (prefixWord ++ tailWord_1975409).sum := by decide
  have hdescent : baseEnd_1975409 < baseStart_1975409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975436 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1975436 : Nat := 118140960795 + 1975436 * 2 ^ 59
def prefixEnd_1975436 : Nat := 4983230072969 + 3 ^ 40 * 1975436 * 2
def baseEnd_1975436 : Nat := 1014348170195238331265141

theorem tailTrace_1975436 : CollatzResearch.WordTrace tailWord_1975436 prefixEnd_1975436 1014348170195238331265141 := by
  unfold tailWord_1975436
  simp only [CollatzResearch.WordTrace]
  refine ⟨36025035035670112226953081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48033380047560149635937441 36025035035670112226953081)
  ·
    refine ⟨27018776276752584170214811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36025035035670112226953081 27018776276752584170214811)
    ·
      refine ⟨40528164415128876255322217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27018776276752584170214811 40528164415128876255322217)
      ·
        refine ⟨30396123311346657191491663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40528164415128876255322217 30396123311346657191491663)
        ·
          refine ⟨45594184967019985787237495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30396123311346657191491663 45594184967019985787237495)
          ·
            refine ⟨68391277450529978680856243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45594184967019985787237495 68391277450529978680856243)
            ·
              refine ⟨102586916175794968021284365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68391277450529978680856243 102586916175794968021284365)
              ·
                refine ⟨38470093565923113007981637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102586916175794968021284365 38470093565923113007981637)
                ·
                  refine ⟨7213142543610583688996557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38470093565923113007981637 7213142543610583688996557)
                  ·
                    refine ⟨2704928453853968883373709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7213142543610583688996557 2704928453853968883373709)
                    ·
                      refine ⟨1014348170195238331265141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2704928453853968883373709 1014348170195238331265141)
                      ·
                        rfl

theorem cell23_1975436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1975436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975436 prefixEnd_1975436 := by exact prefixLift 1975436
  have htrace : WordTrace (prefixWord ++ tailWord_1975436) baseStart_1975436 baseEnd_1975436 := by
    simpa [prefixWord, tailWord_1975436, baseEnd_1975436] using wordTrace_append hprefix tailTrace_1975436
  have hstable : (prefixWord ++ tailWord_1975436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975436).length < 2 ^ (prefixWord ++ tailWord_1975436).sum := by decide
  have hdescent : baseEnd_1975436 < baseStart_1975436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975454 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_1975454 : Nat := 118140960795 + 1975454 * 2 ^ 59
def prefixEnd_1975454 : Nat := 4983230072969 + 3 ^ 40 * 1975454 * 2
def baseEnd_1975454 : Nat := 1014357412847019260840059

theorem tailTrace_1975454 : CollatzResearch.WordTrace tailWord_1975454 prefixEnd_1975454 1014357412847019260840059 := by
  unfold tailWord_1975454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006340823159376691007677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48033817723516675685374277 9006340823159376691007677)
  ·
    refine ⟨3377377808684766259127879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9006340823159376691007677 3377377808684766259127879)
    ·
      refine ⟨5066066713027149388691819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377377808684766259127879 5066066713027149388691819)
      ·
        refine ⟨7599100069540724083037729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5066066713027149388691819 7599100069540724083037729)
        ·
          refine ⟨5699325052155543062278297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7599100069540724083037729 5699325052155543062278297)
          ·
            refine ⟨4274493789116657296708723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5699325052155543062278297 4274493789116657296708723)
            ·
              refine ⟨6411740683674985945063085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274493789116657296708723 6411740683674985945063085)
              ·
                refine ⟨2404402756378119729398657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6411740683674985945063085 2404402756378119729398657)
                ·
                  refine ⟨1803302067283589797048993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404402756378119729398657 1803302067283589797048993)
                  ·
                    refine ⟨1352476550462692347786745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1803302067283589797048993 1352476550462692347786745)
                    ·
                      refine ⟨1014357412847019260840059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352476550462692347786745 1014357412847019260840059)
                      ·
                        rfl

theorem cell23_1975454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_1975454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975454 prefixEnd_1975454 := by exact prefixLift 1975454
  have htrace : WordTrace (prefixWord ++ tailWord_1975454) baseStart_1975454 baseEnd_1975454 := by
    simpa [prefixWord, tailWord_1975454, baseEnd_1975454] using wordTrace_append hprefix tailTrace_1975454
  have hstable : (prefixWord ++ tailWord_1975454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975454).length < 2 ^ (prefixWord ++ tailWord_1975454).sum := by decide
  have hdescent : baseEnd_1975454 < baseStart_1975454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975456 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_1975456 : Nat := 118140960795 + 1975456 * 2 ^ 59
def prefixEnd_1975456 : Nat := 4983230072969 + 3 ^ 40 * 1975456 * 2
def baseEnd_1975456 : Nat := 338119479936109417671683

theorem tailTrace_1975456 : CollatzResearch.WordTrace tailWord_1975456 prefixEnd_1975456 338119479936109417671683 := by
  unfold tailWord_1975456
  simp only [CollatzResearch.WordTrace]
  refine ⟨36025399765633883934817111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48033866354178511913089481 36025399765633883934817111)
  ·
    refine ⟨54038099648450825902225667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36025399765633883934817111 54038099648450825902225667)
    ·
      refine ⟨81057149472676238853338501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54038099648450825902225667 81057149472676238853338501)
      ·
        refine ⟨15198215526126794785000969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81057149472676238853338501 15198215526126794785000969)
        ·
          refine ⟨11398661644595096088750727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15198215526126794785000969 11398661644595096088750727)
          ·
            refine ⟨17097992466892644133126091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11398661644595096088750727 17097992466892644133126091)
            ·
              refine ⟨25646988700338966199689137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17097992466892644133126091 25646988700338966199689137)
              ·
                refine ⟨19235241525254224649766853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25646988700338966199689137 19235241525254224649766853)
                ·
                  refine ⟨3606607785985167121831285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19235241525254224649766853 3606607785985167121831285)
                  ·
                    refine ⟨338119479936109417671683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3606607785985167121831285 338119479936109417671683)
                    ·
                      rfl

theorem cell23_1975456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_1975456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975456 prefixEnd_1975456 := by exact prefixLift 1975456
  have htrace : WordTrace (prefixWord ++ tailWord_1975456) baseStart_1975456 baseEnd_1975456 := by
    simpa [prefixWord, tailWord_1975456, baseEnd_1975456] using wordTrace_append hprefix tailTrace_1975456
  have hstable : (prefixWord ++ tailWord_1975456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975456).length < 2 ^ (prefixWord ++ tailWord_1975456).sum := by decide
  have hdescent : baseEnd_1975456 < baseStart_1975456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975473 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_1975473 : Nat := 118140960795 + 1975473 * 2 ^ 59
def prefixEnd_1975473 : Nat := 4983230072969 + 3 ^ 40 * 1975473 * 2
def baseEnd_1975473 : Nat := 338122389659818228834157

theorem tailTrace_1975473 : CollatzResearch.WordTrace tailWord_1975473 prefixEnd_1975473 338122389659818228834157 := by
  unfold tailWord_1975473
  simp only [CollatzResearch.WordTrace]
  refine ⟨72051419572206179773003073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48034279714804119848668715 72051419572206179773003073)
  ·
    refine ⟨54038564679154634829752305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72051419572206179773003073 54038564679154634829752305)
    ·
      refine ⟨40528923509365976122314229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54038564679154634829752305 40528923509365976122314229)
      ·
        refine ⟨3799586579003060261466959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40528923509365976122314229 3799586579003060261466959)
        ·
          refine ⟨5699379868504590392200439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799586579003060261466959 5699379868504590392200439)
          ·
            refine ⟨8549069802756885588300659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699379868504590392200439 8549069802756885588300659)
            ·
              refine ⟨12823604704135328382450989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549069802756885588300659 12823604704135328382450989)
              ·
                refine ⟨4808851764050748143419121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12823604704135328382450989 4808851764050748143419121)
                ·
                  refine ⟨3606638823038061107564341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4808851764050748143419121 3606638823038061107564341)
                  ·
                    refine ⟨338122389659818228834157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3606638823038061107564341 338122389659818228834157)
                    ·
                      rfl

theorem cell23_1975473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_1975473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975473 prefixEnd_1975473 := by exact prefixLift 1975473
  have htrace : WordTrace (prefixWord ++ tailWord_1975473) baseStart_1975473 baseEnd_1975473 := by
    simpa [prefixWord, tailWord_1975473, baseEnd_1975473] using wordTrace_append hprefix tailTrace_1975473
  have hstable : (prefixWord ++ tailWord_1975473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975473).length < 2 ^ (prefixWord ++ tailWord_1975473).sum := by decide
  have hdescent : baseEnd_1975473 < baseStart_1975473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975493 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 2, 4, 2]
def baseStart_1975493 : Nat := 118140960795 + 1975493 * 2 ^ 59
def prefixEnd_1975493 : Nat := 4983230072969 + 3 ^ 40 * 1975493 * 2
def baseEnd_1975493 : Nat := 1014377438592544608252379

theorem tailTrace_1975493 : CollatzResearch.WordTrace tailWord_1975493 prefixEnd_1975493 1014377438592544608252379 := by
  unfold tailWord_1975493
  simp only [CollatzResearch.WordTrace]
  refine ⟨72052149032133723188731133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48034766021422482125820755 72052149032133723188731133)
  ·
    refine ⟨27019555887050146195774175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72052149032133723188731133 27019555887050146195774175)
    ·
      refine ⟨40529333830575219293661263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27019555887050146195774175 40529333830575219293661263)
      ·
        refine ⟨60794000745862828940491895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40529333830575219293661263 60794000745862828940491895)
        ·
          refine ⟨91191001118794243410737843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60794000745862828940491895 91191001118794243410737843)
          ·
            refine ⟨136786501678191365116106765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91191001118794243410737843 136786501678191365116106765)
            ·
              refine ⟨51294938129321761918540037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136786501678191365116106765 51294938129321761918540037)
              ·
                refine ⟨9617800899247830359726257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51294938129321761918540037 9617800899247830359726257)
                ·
                  refine ⟨7213350674435872769794693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9617800899247830359726257 7213350674435872769794693)
                  ·
                    refine ⟨1352503251456726144336505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7213350674435872769794693 1352503251456726144336505)
                    ·
                      refine ⟨1014377438592544608252379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352503251456726144336505 1014377438592544608252379)
                      ·
                        rfl

theorem cell23_1975493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_1975493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975493 prefixEnd_1975493 := by exact prefixLift 1975493
  have htrace : WordTrace (prefixWord ++ tailWord_1975493) baseStart_1975493 baseEnd_1975493 := by
    simpa [prefixWord, tailWord_1975493, baseEnd_1975493] using wordTrace_append hprefix tailTrace_1975493
  have hstable : (prefixWord ++ tailWord_1975493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975493).length < 2 ^ (prefixWord ++ tailWord_1975493).sum := by decide
  have hdescent : baseEnd_1975493 < baseStart_1975493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975527 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1975527 : Nat := 118140960795 + 1975527 * 2 ^ 59
def prefixEnd_1975527 : Nat := 4983230072969 + 3 ^ 40 * 1975527 * 2
def baseEnd_1975527 : Nat := 1014394896934797475227223

theorem tailTrace_1975527 : CollatzResearch.WordTrace tailWord_1975527 prefixEnd_1975527 1014394896934797475227223 := by
  unfold tailWord_1975527
  simp only [CollatzResearch.WordTrace]
  refine ⟨72053389114010546995468835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48035592742673697996979223 72053389114010546995468835)
  ·
    refine ⟨108080083671015820493203253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72053389114010546995468835 108080083671015820493203253)
    ·
      refine ⟨10132507844157733171237805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108080083671015820493203253 10132507844157733171237805)
      ·
        refine ⟨3799690441559149939214177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10132507844157733171237805 3799690441559149939214177)
        ·
          refine ⟨2849767831169362454410633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799690441559149939214177 2849767831169362454410633)
          ·
            refine ⟨2137325873377021840807975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849767831169362454410633 2137325873377021840807975)
            ·
              refine ⟨3205988810065532761211963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137325873377021840807975 3205988810065532761211963)
              ·
                refine ⟨4808983215098299141817945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205988810065532761211963 4808983215098299141817945)
                ·
                  refine ⟨3606737411323724356363459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4808983215098299141817945 3606737411323724356363459)
                  ·
                    refine ⟨5410106116985586534545189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3606737411323724356363459 5410106116985586534545189)
                    ·
                      refine ⟨1014394896934797475227223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5410106116985586534545189 1014394896934797475227223)
                      ·
                        rfl

theorem cell23_1975527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1975527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975527 prefixEnd_1975527 := by exact prefixLift 1975527
  have htrace : WordTrace (prefixWord ++ tailWord_1975527) baseStart_1975527 baseEnd_1975527 := by
    simpa [prefixWord, tailWord_1975527, baseEnd_1975527] using wordTrace_append hprefix tailTrace_1975527
  have hstable : (prefixWord ++ tailWord_1975527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975527).length < 2 ^ (prefixWord ++ tailWord_1975527).sum := by decide
  have hdescent : baseEnd_1975527 < baseStart_1975527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975530 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1975530 : Nat := 118140960795 + 1975530 * 2 ^ 59
def prefixEnd_1975530 : Nat := 4983230072969 + 3 ^ 40 * 1975530 * 2
def baseEnd_1975530 : Nat := 1014396437376760963489709

theorem tailTrace_1975530 : CollatzResearch.WordTrace tailWord_1975530 prefixEnd_1975530 1014396437376760963489709 := by
  unfold tailWord_1975530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013374633249919626957011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48035665688666452338552029 18013374633249919626957011)
  ·
    refine ⟨27020061949874879440435517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18013374633249919626957011 27020061949874879440435517)
    ·
      refine ⟨10132523231203079790163319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27020061949874879440435517 10132523231203079790163319)
      ·
        refine ⟨15198784846804619685244979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132523231203079790163319 15198784846804619685244979)
        ·
          refine ⟨22798177270206929527867469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15198784846804619685244979 22798177270206929527867469)
          ·
            refine ⟨8549316476327598572950301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22798177270206929527867469 8549316476327598572950301)
            ·
              refine ⟨3205993678622849464856363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8549316476327598572950301 3205993678622849464856363)
              ·
                refine ⟨4808990517934274197284545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205993678622849464856363 4808990517934274197284545)
                ·
                  refine ⟨3606742888450705647963409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4808990517934274197284545 3606742888450705647963409)
                  ·
                    refine ⟨2705057166338029235972557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606742888450705647963409 2705057166338029235972557)
                    ·
                      refine ⟨1014396437376760963489709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2705057166338029235972557 1014396437376760963489709)
                      ·
                        rfl

theorem cell23_1975530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1975530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975530 prefixEnd_1975530 := by exact prefixLift 1975530
  have htrace : WordTrace (prefixWord ++ tailWord_1975530) baseStart_1975530 baseEnd_1975530 := by
    simpa [prefixWord, tailWord_1975530, baseEnd_1975530] using wordTrace_append hprefix tailTrace_1975530
  have hstable : (prefixWord ++ tailWord_1975530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975530).length < 2 ^ (prefixWord ++ tailWord_1975530).sum := by decide
  have hdescent : baseEnd_1975530 < baseStart_1975530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975550 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_1975550 : Nat := 118140960795 + 1975550 * 2 ^ 59
def prefixEnd_1975550 : Nat := 4983230072969 + 3 ^ 40 * 1975550 * 2
def baseEnd_1975550 : Nat := 112711856332205653915513

theorem tailTrace_1975550 : CollatzResearch.WordTrace tailWord_1975550 prefixEnd_1975550 112711856332205653915513 := by
  unfold tailWord_1975550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006778499115902740444513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48036151995284814615704069 9006778499115902740444513)
  ·
    refine ⟨6755083874336927055333385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9006778499115902740444513 6755083874336927055333385)
    ·
      refine ⟨5066312905752695291500039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6755083874336927055333385 5066312905752695291500039)
      ·
        refine ⟨7599469358629042937250059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5066312905752695291500039 7599469358629042937250059)
        ·
          refine ⟨11399204037943564405875089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599469358629042937250059 11399204037943564405875089)
          ·
            refine ⟨8549403028457673304406317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399204037943564405875089 8549403028457673304406317)
            ·
              refine ⟨3206026135671627489152369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8549403028457673304406317 3206026135671627489152369)
              ·
                refine ⟨2404519601753720616864277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206026135671627489152369 2404519601753720616864277)
                ·
                  refine ⟨112711856332205653915513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2404519601753720616864277 112711856332205653915513)
                  ·
                    rfl

theorem cell23_1975550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_1975550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975550 prefixEnd_1975550 := by exact prefixLift 1975550
  have htrace : WordTrace (prefixWord ++ tailWord_1975550) baseStart_1975550 baseEnd_1975550 := by
    simpa [prefixWord, tailWord_1975550, baseEnd_1975550] using wordTrace_append hprefix tailTrace_1975550
  have hstable : (prefixWord ++ tailWord_1975550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975550).length < 2 ^ (prefixWord ++ tailWord_1975550).sum := by decide
  have hdescent : baseEnd_1975550 < baseStart_1975550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975597 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1975597 : Nat := 118140960795 + 1975597 * 2 ^ 59
def prefixEnd_1975597 : Nat := 4983230072969 + 3 ^ 40 * 1975597 * 2
def baseEnd_1975597 : Nat := 338143613526870733783967

theorem tailTrace_1975597 : CollatzResearch.WordTrace tailWord_1975597 prefixEnd_1975597 338143613526870733783967 := by
  unfold tailWord_1975597
  simp only [CollatzResearch.WordTrace]
  refine ⟨72055942223756948950517045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48037294815837965967011363 72055942223756948950517045)
  ·
    refine ⟨6755244583477213964110973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72055942223756948950517045 6755244583477213964110973)
    ·
      refine ⟨2533216718803955236541615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6755244583477213964110973 2533216718803955236541615)
      ·
        refine ⟨3799825078205932854812423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533216718803955236541615 3799825078205932854812423)
        ·
          refine ⟨5699737617308899282218635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799825078205932854812423 5699737617308899282218635)
          ·
            refine ⟨8549606425963348923327953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699737617308899282218635 8549606425963348923327953)
            ·
              refine ⟨6412204819472511692495965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549606425963348923327953 6412204819472511692495965)
              ·
                refine ⟨2404576807302191884685987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6412204819472511692495965 2404576807302191884685987)
                ·
                  refine ⟨3606865210953287827028981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404576807302191884685987 3606865210953287827028981)
                  ·
                    refine ⟨338143613526870733783967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3606865210953287827028981 338143613526870733783967)
                    ·
                      rfl

theorem cell23_1975597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1975597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975597 prefixEnd_1975597 := by exact prefixLift 1975597
  have htrace : WordTrace (prefixWord ++ tailWord_1975597) baseStart_1975597 baseEnd_1975597 := by
    simpa [prefixWord, tailWord_1975597, baseEnd_1975597] using wordTrace_append hprefix tailTrace_1975597
  have hstable : (prefixWord ++ tailWord_1975597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975597).length < 2 ^ (prefixWord ++ tailWord_1975597).sum := by decide
  have hdescent : baseEnd_1975597 < baseStart_1975597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975603 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5]
def baseStart_1975603 : Nat := 118140960795 + 1975603 * 2 ^ 59
def prefixEnd_1975603 : Nat := 4983230072969 + 3 ^ 40 * 1975603 * 2
def baseEnd_1975603 : Nat := 1014433921464539177876873

theorem tailTrace_1975603 : CollatzResearch.WordTrace tailWord_1975603 prefixEnd_1975603 1014433921464539177876873 := by
  unfold tailWord_1975603
  simp only [CollatzResearch.WordTrace]
  refine ⟨72056161061735211975235463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48037440707823474650156975 72056161061735211975235463)
  ·
    refine ⟨108084241592602817962853195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72056161061735211975235463 108084241592602817962853195)
    ·
      refine ⟨162126362388904226944279793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108084241592602817962853195 162126362388904226944279793)
      ·
        refine ⟨121594771791678170208209845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162126362388904226944279793 121594771791678170208209845)
        ·
          refine ⟨11399509855469828457019673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121594771791678170208209845 11399509855469828457019673)
          ·
            refine ⟨8549632391602371342764755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399509855469828457019673 8549632391602371342764755)
            ·
              refine ⟨12824448587403557014147133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549632391602371342764755 12824448587403557014147133)
              ·
                refine ⟨4809168220276333880305175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12824448587403557014147133 4809168220276333880305175)
                ·
                  refine ⟨7213752330414500820457763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809168220276333880305175 7213752330414500820457763)
                  ·
                    refine ⟨10820628495621751230686645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7213752330414500820457763 10820628495621751230686645)
                    ·
                      refine ⟨1014433921464539177876873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10820628495621751230686645 1014433921464539177876873)
                      ·
                        rfl

theorem cell23_1975603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_1975603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975603 prefixEnd_1975603 := by exact prefixLift 1975603
  have htrace : WordTrace (prefixWord ++ tailWord_1975603) baseStart_1975603 baseEnd_1975603 := by
    simpa [prefixWord, tailWord_1975603, baseEnd_1975603] using wordTrace_append hprefix tailTrace_1975603
  have hstable : (prefixWord ++ tailWord_1975603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975603).length < 2 ^ (prefixWord ++ tailWord_1975603).sum := by decide
  have hdescent : baseEnd_1975603 < baseStart_1975603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975610 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_1975610 : Nat := 118140960795 + 1975610 * 2 ^ 59
def prefixEnd_1975610 : Nat := 4983230072969 + 3 ^ 40 * 1975610 * 2
def baseEnd_1975610 : Nat := 338145838609706883496447

theorem tailTrace_1975610 : CollatzResearch.WordTrace tailWord_1975610 prefixEnd_1975610 338145838609706883496447 := by
  unfold tailWord_1975610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014104093177463042685071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48037610915139901447160189 18014104093177463042685071)
  ·
    refine ⟨27021156139766194564027607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18014104093177463042685071 27021156139766194564027607)
    ·
      refine ⟨40531734209649291846041411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021156139766194564027607 40531734209649291846041411)
      ·
        refine ⟨60797601314473937769062117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40531734209649291846041411 60797601314473937769062117)
        ·
          refine ⟨11399550246463863331699147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60797601314473937769062117 11399550246463863331699147)
          ·
            refine ⟨17099325369695794997548721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11399550246463863331699147 17099325369695794997548721)
            ·
              refine ⟨12824494027271846248161541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17099325369695794997548721 12824494027271846248161541)
              ·
                refine ⟨2404592630113471171530289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12824494027271846248161541 2404592630113471171530289)
                ·
                  refine ⟨1803444472585103378647717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404592630113471171530289 1803444472585103378647717)
                  ·
                    refine ⟨338145838609706883496447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803444472585103378647717 338145838609706883496447)
                    ·
                      rfl

theorem cell23_1975610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_1975610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975610 prefixEnd_1975610 := by exact prefixLift 1975610
  have htrace : WordTrace (prefixWord ++ tailWord_1975610) baseStart_1975610 baseEnd_1975610 := by
    simpa [prefixWord, tailWord_1975610, baseEnd_1975610] using wordTrace_append hprefix tailTrace_1975610
  have hstable : (prefixWord ++ tailWord_1975610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975610).length < 2 ^ (prefixWord ++ tailWord_1975610).sum := by decide
  have hdescent : baseEnd_1975610 < baseStart_1975610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975623 : List Nat := [1, 1, 4, 1, 2, 4, 2, 8]
def baseStart_1975623 : Nat := 118140960795 + 1975623 * 2 ^ 59
def prefixEnd_1975623 : Nat := 4983230072969 + 3 ^ 40 * 1975623 * 2
def baseEnd_1975623 : Nat := 37572007076949225912103

theorem tailTrace_1975623 : CollatzResearch.WordTrace tailWord_1975623 prefixEnd_1975623 37572007076949225912103 := by
  unfold tailWord_1975623
  simp only [CollatzResearch.WordTrace]
  refine ⟨72056890521662755390963523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48037927014441836927309015 72056890521662755390963523)
  ·
    refine ⟨108085335782494133086445285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72056890521662755390963523 108085335782494133086445285)
    ·
      refine ⟨20266000459217649953708491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108085335782494133086445285 20266000459217649953708491)
      ·
        refine ⟨30399000688826474930562737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20266000459217649953708491 30399000688826474930562737)
        ·
          refine ⟨22799250516619856197922053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30399000688826474930562737 22799250516619856197922053)
          ·
            refine ⟨4274859471866223037110385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22799250516619856197922053 4274859471866223037110385)
            ·
              refine ⟨3206144603899667277832789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274859471866223037110385 3206144603899667277832789)
              ·
                refine ⟨37572007076949225912103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3206144603899667277832789 37572007076949225912103)
                ·
                  rfl

theorem cell23_1975623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 8].length) (baseStart_1975623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975623 prefixEnd_1975623 := by exact prefixLift 1975623
  have htrace : WordTrace (prefixWord ++ tailWord_1975623) baseStart_1975623 baseEnd_1975623 := by
    simpa [prefixWord, tailWord_1975623, baseEnd_1975623] using wordTrace_append hprefix tailTrace_1975623
  have hstable : (prefixWord ++ tailWord_1975623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975623).length < 2 ^ (prefixWord ++ tailWord_1975623).sum := by decide
  have hdescent : baseEnd_1975623 < baseStart_1975623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975637 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_1975637 : Nat := 118140960795 + 1975637 * 2 ^ 59
def prefixEnd_1975637 : Nat := 4983230072969 + 3 ^ 40 * 1975637 * 2
def baseEnd_1975637 : Nat := 1014451379806792044851717

theorem tailTrace_1975637 : CollatzResearch.WordTrace tailWord_1975637 prefixEnd_1975637 1014451379806792044851717 := by
  unfold tailWord_1975637
  simp only [CollatzResearch.WordTrace]
  refine ⟨72057401143612035781973165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48038267429074690521315443 72057401143612035781973165)
  ·
    refine ⟨27021525428854513418239937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72057401143612035781973165 27021525428854513418239937)
    ·
      refine ⟨20266144071640885063679953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27021525428854513418239937 20266144071640885063679953)
      ·
        refine ⟨15199608053730663797759965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20266144071640885063679953 15199608053730663797759965)
        ·
          refine ⟨5699853020148998924159987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15199608053730663797759965 5699853020148998924159987)
          ·
            refine ⟨8549779530223498386239981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699853020148998924159987 8549779530223498386239981)
            ·
              refine ⟨3206167323833811894839993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8549779530223498386239981 3206167323833811894839993)
              ·
                refine ⟨2404625492875358921129995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206167323833811894839993 2404625492875358921129995)
                ·
                  refine ⟨3606938239313038381694993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404625492875358921129995 3606938239313038381694993)
                  ·
                    refine ⟨2705203679484778786271245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3606938239313038381694993 2705203679484778786271245)
                    ·
                      refine ⟨1014451379806792044851717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2705203679484778786271245 1014451379806792044851717)
                      ·
                        rfl

theorem cell23_1975637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_1975637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975637 prefixEnd_1975637 := by exact prefixLift 1975637
  have htrace : WordTrace (prefixWord ++ tailWord_1975637) baseStart_1975637 baseEnd_1975637 := by
    simpa [prefixWord, tailWord_1975637, baseEnd_1975637] using wordTrace_append hprefix tailTrace_1975637
  have hstable : (prefixWord ++ tailWord_1975637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975637).length < 2 ^ (prefixWord ++ tailWord_1975637).sum := by decide
  have hdescent : baseEnd_1975637 < baseStart_1975637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975673 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1975673 : Nat := 118140960795 + 1975673 * 2 ^ 59
def prefixEnd_1975673 : Nat := 4983230072969 + 3 ^ 40 * 1975673 * 2
def baseEnd_1975673 : Nat := 1014469865110353904001551

theorem tailTrace_1975673 : CollatzResearch.WordTrace tailWord_1975673 prefixEnd_1975673 1014469865110353904001551 := by
  unfold tailWord_1975673
  simp only [CollatzResearch.WordTrace]
  refine ⟨72058714171481613930283673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48039142780987742620189115 72058714171481613930283673)
  ·
    refine ⟨54044035628611210447712755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72058714171481613930283673 54044035628611210447712755)
    ·
      refine ⟨81066053442916815671569133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54044035628611210447712755 81066053442916815671569133)
      ·
        refine ⟨30399770041093805876838425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81066053442916815671569133 30399770041093805876838425)
        ·
          refine ⟨22799827530820354407628819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30399770041093805876838425 22799827530820354407628819)
          ·
            refine ⟨34199741296230531611443229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22799827530820354407628819 34199741296230531611443229)
            ·
              refine ⟨12824902986086449354291211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34199741296230531611443229 12824902986086449354291211)
              ·
                refine ⟨19237354479129674031436817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12824902986086449354291211 19237354479129674031436817)
                ·
                  refine ⟨14428015859347255523577613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19237354479129674031436817 14428015859347255523577613)
                  ·
                    refine ⟨5410505947255220821341605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14428015859347255523577613 5410505947255220821341605)
                    ·
                      refine ⟨1014469865110353904001551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5410505947255220821341605 1014469865110353904001551)
                      ·
                        rfl

theorem cell23_1975673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1975673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975673 prefixEnd_1975673 := by exact prefixLift 1975673
  have htrace : WordTrace (prefixWord ++ tailWord_1975673) baseStart_1975673 baseEnd_1975673 := by
    simpa [prefixWord, tailWord_1975673, baseEnd_1975673] using wordTrace_append hprefix tailTrace_1975673
  have hstable : (prefixWord ++ tailWord_1975673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975673).length < 2 ^ (prefixWord ++ tailWord_1975673).sum := by decide
  have hdescent : baseEnd_1975673 < baseStart_1975673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975683 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 1, 8]
def baseStart_1975683 : Nat := 118140960795 + 1975683 * 2 ^ 59
def prefixEnd_1975683 : Nat := 4983230072969 + 3 ^ 40 * 1975683 * 2
def baseEnd_1975683 : Nat := 338158333305632954958835

theorem tailTrace_1975683 : CollatzResearch.WordTrace tailWord_1975683 prefixEnd_1975683 338158333305632954958835 := by
  unfold tailWord_1975683
  simp only [CollatzResearch.WordTrace]
  refine ⟨72059078901445385638147703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48039385934296923758765135 72059078901445385638147703)
  ·
    refine ⟨108088618352168078457221555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72059078901445385638147703 108088618352168078457221555)
    ·
      refine ⟨162132927528252117685832333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108088618352168078457221555 162132927528252117685832333)
      ·
        refine ⟨60799847823094544132187125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162132927528252117685832333 60799847823094544132187125)
        ·
          refine ⟨5699985733415113512392543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60799847823094544132187125 5699985733415113512392543)
          ·
            refine ⟨8549978600122670268588815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699985733415113512392543 8549978600122670268588815)
            ·
              refine ⟨12824967900184005402883223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8549978600122670268588815 12824967900184005402883223)
              ·
                refine ⟨19237451850276008104324835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12824967900184005402883223 19237451850276008104324835)
                ·
                  refine ⟨28856177775414012156487253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19237451850276008104324835 28856177775414012156487253)
                  ·
                    refine ⟨338158333305632954958835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28856177775414012156487253 338158333305632954958835)
                    ·
                      rfl

theorem cell23_1975683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 8].length) (baseStart_1975683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975683 prefixEnd_1975683 := by exact prefixLift 1975683
  have htrace : WordTrace (prefixWord ++ tailWord_1975683) baseStart_1975683 baseEnd_1975683 := by
    simpa [prefixWord, tailWord_1975683, baseEnd_1975683] using wordTrace_append hprefix tailTrace_1975683
  have hstable : (prefixWord ++ tailWord_1975683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975683).length < 2 ^ (prefixWord ++ tailWord_1975683).sum := by decide
  have hdescent : baseEnd_1975683 < baseStart_1975683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975703 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1975703 : Nat := 118140960795 + 1975703 * 2 ^ 59
def prefixEnd_1975703 : Nat := 4983230072969 + 3 ^ 40 * 1975703 * 2
def baseEnd_1975703 : Nat := 1014485269529988786626413

theorem tailTrace_1975703 : CollatzResearch.WordTrace tailWord_1975703 prefixEnd_1975703 1014485269529988786626413 := by
  unfold tailWord_1975703
  simp only [CollatzResearch.WordTrace]
  refine ⟨72059808361372929053875763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48039872240915286035917175 72059808361372929053875763)
  ·
    refine ⟨108089712542059393580813645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72059808361372929053875763 108089712542059393580813645)
    ·
      refine ⟨40533642203272272592805117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108089712542059393580813645 40533642203272272592805117)
      ·
        refine ⟨15200115826227102222301919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40533642203272272592805117 15200115826227102222301919)
        ·
          refine ⟨22800173739340653333452879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15200115826227102222301919 22800173739340653333452879)
          ·
            refine ⟨34200260609010980000179319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22800173739340653333452879 34200260609010980000179319)
            ·
              refine ⟨51300390913516470000268979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34200260609010980000179319 51300390913516470000268979)
              ·
                refine ⟨76950586370274705000403469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51300390913516470000268979 76950586370274705000403469)
                ·
                  refine ⟨28856469888853014375151301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76950586370274705000403469 28856469888853014375151301)
                  ·
                    refine ⟨5410588104159940195340869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28856469888853014375151301 5410588104159940195340869)
                    ·
                      refine ⟨1014485269529988786626413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5410588104159940195340869 1014485269529988786626413)
                      ·
                        rfl

theorem cell23_1975703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1975703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975703 prefixEnd_1975703 := by exact prefixLift 1975703
  have htrace : WordTrace (prefixWord ++ tailWord_1975703) baseStart_1975703 baseEnd_1975703 := by
    simpa [prefixWord, tailWord_1975703, baseEnd_1975703] using wordTrace_append hprefix tailTrace_1975703
  have hstable : (prefixWord ++ tailWord_1975703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975703).length < 2 ^ (prefixWord ++ tailWord_1975703).sum := by decide
  have hdescent : baseEnd_1975703 < baseStart_1975703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975711 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 1, 3, 2]
def baseStart_1975711 : Nat := 118140960795 + 1975711 * 2 ^ 59
def prefixEnd_1975711 : Nat := 4983230072969 + 3 ^ 40 * 1975711 * 2
def baseEnd_1975711 : Nat := 1014489377375224755326377

theorem tailTrace_1975711 : CollatzResearch.WordTrace tailWord_1975711 prefixEnd_1975711 1014489377375224755326377 := by
  unfold tailWord_1975711
  simp only [CollatzResearch.WordTrace]
  refine ⟨72060100145343946420166987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48040066763562630946777991 72060100145343946420166987)
  ·
    refine ⟨108090150218015919630250481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72060100145343946420166987 108090150218015919630250481)
    ·
      refine ⟨81067612663511939722687861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108090150218015919630250481 81067612663511939722687861)
      ·
        refine ⟨7600088687204244349001987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81067612663511939722687861 7600088687204244349001987)
        ·
          refine ⟨11400133030806366523502981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7600088687204244349001987 11400133030806366523502981)
          ·
            refine ⟨2137524943276193723156809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11400133030806366523502981 2137524943276193723156809)
            ·
              refine ⟨1603143707457145292367607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137524943276193723156809 1603143707457145292367607)
              ·
                refine ⟨2404715561185717938551411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603143707457145292367607 2404715561185717938551411)
                ·
                  refine ⟨3607073341778576907827117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404715561185717938551411 3607073341778576907827117)
                  ·
                    refine ⟨1352652503166966340435169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607073341778576907827117 1352652503166966340435169)
                    ·
                      refine ⟨1014489377375224755326377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352652503166966340435169 1014489377375224755326377)
                      ·
                        rfl

theorem cell23_1975711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_1975711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975711 prefixEnd_1975711 := by exact prefixLift 1975711
  have htrace : WordTrace (prefixWord ++ tailWord_1975711) baseStart_1975711 baseEnd_1975711 := by
    simpa [prefixWord, tailWord_1975711, baseEnd_1975711] using wordTrace_append hprefix tailTrace_1975711
  have hstable : (prefixWord ++ tailWord_1975711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975711).length < 2 ^ (prefixWord ++ tailWord_1975711).sum := by decide
  have hdescent : baseEnd_1975711 < baseStart_1975711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975724 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 2, 2, 2]
def baseStart_1975724 : Nat := 118140960795 + 1975724 * 2 ^ 59
def prefixEnd_1975724 : Nat := 4983230072969 + 3 ^ 40 * 1975724 * 2
def baseEnd_1975724 : Nat := 1014496052623733204463817

theorem tailTrace_1975724 : CollatzResearch.WordTrace tailWord_1975724 prefixEnd_1975724 1014496052623733204463817 := by
  unfold tailWord_1975724
  simp only [CollatzResearch.WordTrace]
  refine ⟨36030287147148424820195113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48040382862864566426926817 36030287147148424820195113)
  ·
    refine ⟨27022715360361318615146335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36030287147148424820195113 27022715360361318615146335)
    ·
      refine ⟨40534073040541977922719503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27022715360361318615146335 40534073040541977922719503)
      ·
        refine ⟨60801109560812966884079255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40534073040541977922719503 60801109560812966884079255)
        ·
          refine ⟨91201664341219450326118883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60801109560812966884079255 91201664341219450326118883)
          ·
            refine ⟨136802496511829175489178325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91201664341219450326118883 136802496511829175489178325)
            ·
              refine ⟨3206308511995996300527617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 136802496511829175489178325 3206308511995996300527617)
              ·
                refine ⟨2404731383996997225395713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206308511995996300527617 2404731383996997225395713)
                ·
                  refine ⟨1803548537997747919046785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404731383996997225395713 1803548537997747919046785)
                  ·
                    refine ⟨1352661403498310939285089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1803548537997747919046785 1352661403498310939285089)
                    ·
                      refine ⟨1014496052623733204463817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352661403498310939285089 1014496052623733204463817)
                      ·
                        rfl

theorem cell23_1975724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_1975724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975724 prefixEnd_1975724 := by exact prefixLift 1975724
  have htrace : WordTrace (prefixWord ++ tailWord_1975724) baseStart_1975724 baseEnd_1975724 := by
    simpa [prefixWord, tailWord_1975724, baseEnd_1975724] using wordTrace_append hprefix tailTrace_1975724
  have hstable : (prefixWord ++ tailWord_1975724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975724).length < 2 ^ (prefixWord ++ tailWord_1975724).sum := by decide
  have hdescent : baseEnd_1975724 < baseStart_1975724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975741 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_1975741 : Nat := 118140960795 + 1975741 * 2 ^ 59
def prefixEnd_1975741 : Nat := 4983230072969 + 3 ^ 40 * 1975741 * 2
def baseEnd_1975741 : Nat := 1014504781794859637951239

theorem tailTrace_1975741 : CollatzResearch.WordTrace tailWord_1975741 prefixEnd_1975741 1014504781794859637951239 := by
  unfold tailWord_1975741
  simp only [CollatzResearch.WordTrace]
  refine ⟨72061194335235261543759077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48040796223490174362506051 72061194335235261543759077)
  ·
    refine ⟨13511473937856611539454827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72061194335235261543759077 13511473937856611539454827)
    ·
      refine ⟨20267210906784917309182241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13511473937856611539454827 20267210906784917309182241)
      ·
        refine ⟨15200408180088687981886681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20267210906784917309182241 15200408180088687981886681)
        ·
          refine ⟨11400306135066515986415011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15200408180088687981886681 11400306135066515986415011)
          ·
            refine ⟨17100459202599773979622517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400306135066515986415011 17100459202599773979622517)
            ·
              refine ⟨1603168050243728810589611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17100459202599773979622517 1603168050243728810589611)
              ·
                refine ⟨2404752075365593215884417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603168050243728810589611 2404752075365593215884417)
                ·
                  refine ⟨1803564056524194911913313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2404752075365593215884417 1803564056524194911913313)
                  ·
                    refine ⟨1352673042393146183934985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1803564056524194911913313 1352673042393146183934985)
                    ·
                      refine ⟨1014504781794859637951239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352673042393146183934985 1014504781794859637951239)
                      ·
                        rfl

theorem cell23_1975741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_1975741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975741 prefixEnd_1975741 := by exact prefixLift 1975741
  have htrace : WordTrace (prefixWord ++ tailWord_1975741) baseStart_1975741 baseEnd_1975741 := by
    simpa [prefixWord, tailWord_1975741, baseEnd_1975741] using wordTrace_append hprefix tailTrace_1975741
  have hstable : (prefixWord ++ tailWord_1975741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975741).length < 2 ^ (prefixWord ++ tailWord_1975741).sum := by decide
  have hdescent : baseEnd_1975741 < baseStart_1975741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975753 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_1975753 : Nat := 118140960795 + 1975753 * 2 ^ 59
def prefixEnd_1975753 : Nat := 4983230072969 + 3 ^ 40 * 1975753 * 2
def baseEnd_1975753 : Nat := 1014510943562713591001183

theorem tailTrace_1975753 : CollatzResearch.WordTrace tailWord_1975753 prefixEnd_1975753 1014510943562713591001183 := by
  unfold tailWord_1975753
  simp only [CollatzResearch.WordTrace]
  refine ⟨72061632011191787593195913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48041088007461191728797275 72061632011191787593195913)
  ·
    refine ⟨54046224008393840694896935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72061632011191787593195913 54046224008393840694896935)
    ·
      refine ⟨81069336012590761042345403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54046224008393840694896935 81069336012590761042345403)
      ·
        refine ⟨121604004018886141563518105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81069336012590761042345403 121604004018886141563518105)
        ·
          refine ⟨91203003014164606172638579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121604004018886141563518105 91203003014164606172638579)
          ·
            refine ⟨136804504521246909258957869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91203003014164606172638579 136804504521246909258957869)
            ·
              refine ⟨51301689195467590972109201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136804504521246909258957869 51301689195467590972109201)
              ·
                refine ⟨38476266896600693229081901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51301689195467590972109201 38476266896600693229081901)
                ·
                  refine ⟨14428600086225259960905713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38476266896600693229081901 14428600086225259960905713)
                  ·
                    refine ⟨10821450064668944970679285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14428600086225259960905713 10821450064668944970679285)
                    ·
                      refine ⟨1014510943562713591001183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10821450064668944970679285 1014510943562713591001183)
                      ·
                        rfl

theorem cell23_1975753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_1975753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975753 prefixEnd_1975753 := by exact prefixLift 1975753
  have htrace : WordTrace (prefixWord ++ tailWord_1975753) baseStart_1975753 baseEnd_1975753 := by
    simpa [prefixWord, tailWord_1975753, baseEnd_1975753] using wordTrace_append hprefix tailTrace_1975753
  have hstable : (prefixWord ++ tailWord_1975753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975753).length < 2 ^ (prefixWord ++ tailWord_1975753).sum := by decide
  have hdescent : baseEnd_1975753 < baseStart_1975753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975817 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_1975817 : Nat := 118140960795 + 1975817 * 2 ^ 59
def prefixEnd_1975817 : Nat := 4983230072969 + 3 ^ 40 * 1975817 * 2
def baseEnd_1975817 : Nat := 1014543806324601340600889

theorem tailTrace_1975817 : CollatzResearch.WordTrace tailWord_1975817 prefixEnd_1975817 1014543806324601340600889 := by
  unfold tailWord_1975817
  simp only [CollatzResearch.WordTrace]
  refine ⟨72063966282959926523525705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48042644188639951015683803 72063966282959926523525705)
  ·
    refine ⟨54047974712219944892644279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72063966282959926523525705 54047974712219944892644279)
    ·
      refine ⟨81071962068329917338966419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54047974712219944892644279 81071962068329917338966419)
      ·
        refine ⟨121607943102494876008449629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81071962068329917338966419 121607943102494876008449629)
        ·
          refine ⟨45602978663435578503168611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121607943102494876008449629 45602978663435578503168611)
          ·
            refine ⟨68404467995153367754752917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45602978663435578503168611 68404467995153367754752917)
            ·
              refine ⟨3206459437272814113504043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68404467995153367754752917 3206459437272814113504043)
              ·
                refine ⟨4809689155909221170256065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206459437272814113504043 4809689155909221170256065)
                ·
                  refine ⟨3607266866931915877692049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4809689155909221170256065 3607266866931915877692049)
                  ·
                    refine ⟨2705450150198936908269037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3607266866931915877692049 2705450150198936908269037)
                    ·
                      refine ⟨1014543806324601340600889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2705450150198936908269037 1014543806324601340600889)
                      ·
                        rfl

theorem cell23_1975817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_1975817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975817 prefixEnd_1975817 := by exact prefixLift 1975817
  have htrace : WordTrace (prefixWord ++ tailWord_1975817) baseStart_1975817 baseEnd_1975817 := by
    simpa [prefixWord, tailWord_1975817, baseEnd_1975817] using wordTrace_append hprefix tailTrace_1975817
  have hstable : (prefixWord ++ tailWord_1975817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975817).length < 2 ^ (prefixWord ++ tailWord_1975817).sum := by decide
  have hdescent : baseEnd_1975817 < baseStart_1975817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975837 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 6]
def baseStart_1975837 : Nat := 118140960795 + 1975837 * 2 ^ 59
def prefixEnd_1975837 : Nat := 4983230072969 + 3 ^ 40 * 1975837 * 2
def baseEnd_1975837 : Nat := 112728230659743473594533

theorem tailTrace_1975837 : CollatzResearch.WordTrace tailWord_1975837 prefixEnd_1975837 112728230659743473594533 := by
  unfold tailWord_1975837
  simp only [CollatzResearch.WordTrace]
  refine ⟨72064695742887469939253765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48043130495258313292835843 72064695742887469939253765)
  ·
    refine ⟨13512130451791400613610081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72064695742887469939253765 13512130451791400613610081)
    ·
      refine ⟨10134097838843550460207561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13512130451791400613610081 10134097838843550460207561)
      ·
        refine ⟨7600573379132662845155671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10134097838843550460207561 7600573379132662845155671)
        ·
          refine ⟨11400860068698994267733507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7600573379132662845155671 11400860068698994267733507)
          ·
            refine ⟨17101290103048491401600261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11400860068698994267733507 17101290103048491401600261)
            ·
              refine ⟨3206491894321592137800049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17101290103048491401600261 3206491894321592137800049)
              ·
                refine ⟨2404868920741194103350037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206491894321592137800049 2404868920741194103350037)
                ·
                  refine ⟨112728230659743473594533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2404868920741194103350037 112728230659743473594533)
                  ·
                    rfl

theorem cell23_1975837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_1975837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975837 prefixEnd_1975837 := by exact prefixLift 1975837
  have htrace : WordTrace (prefixWord ++ tailWord_1975837) baseStart_1975837 baseEnd_1975837 := by
    simpa [prefixWord, tailWord_1975837, baseEnd_1975837] using wordTrace_append hprefix tailTrace_1975837
  have hstable : (prefixWord ++ tailWord_1975837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975837).length < 2 ^ (prefixWord ++ tailWord_1975837).sum := by decide
  have hdescent : baseEnd_1975837 < baseStart_1975837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975841 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 1, 4]
def baseStart_1975841 : Nat := 118140960795 + 1975841 * 2 ^ 59
def prefixEnd_1975841 : Nat := 4983230072969 + 3 ^ 40 * 1975841 * 2
def baseEnd_1975841 : Nat := 338185376620103082233593

theorem tailTrace_1975841 : CollatzResearch.WordTrace tailWord_1975841 prefixEnd_1975841 338185376620103082233593 := by
  unfold tailWord_1975841
  simp only [CollatzResearch.WordTrace]
  refine ⟨72064841634872978622399377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48043227756581985748266251 72064841634872978622399377)
  ·
    refine ⟨54048631226154733966799533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72064841634872978622399377 54048631226154733966799533)
    ·
      refine ⟨20268236709808025237549825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54048631226154733966799533 20268236709808025237549825)
      ·
        refine ⟨15201177532356018928162369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20268236709808025237549825 15201177532356018928162369)
        ·
          refine ⟨11400883149267014196121777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15201177532356018928162369 11400883149267014196121777)
          ·
            refine ⟨8550662361950260647091333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11400883149267014196121777 8550662361950260647091333)
            ·
              refine ⟨1603249192865673871329625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8550662361950260647091333 1603249192865673871329625)
              ·
                refine ⟨1202436894649255403497219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603249192865673871329625 1202436894649255403497219)
                ·
                  refine ⟨1803655341973883105245829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202436894649255403497219 1803655341973883105245829)
                  ·
                    refine ⟨338185376620103082233593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803655341973883105245829 338185376620103082233593)
                    ·
                      rfl

theorem cell23_1975841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_1975841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975841 prefixEnd_1975841 := by exact prefixLift 1975841
  have htrace : WordTrace (prefixWord ++ tailWord_1975841) baseStart_1975841 baseEnd_1975841 := by
    simpa [prefixWord, tailWord_1975841, baseEnd_1975841] using wordTrace_append hprefix tailTrace_1975841
  have hstable : (prefixWord ++ tailWord_1975841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975841).length < 2 ^ (prefixWord ++ tailWord_1975841).sum := by decide
  have hdescent : baseEnd_1975841 < baseStart_1975841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975857 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 1, 5, 2]
def baseStart_1975857 : Nat := 118140960795 + 1975857 * 2 ^ 59
def prefixEnd_1975857 : Nat := 4983230072969 + 3 ^ 40 * 1975857 * 2
def baseEnd_1975857 : Nat := 1014564345550781184100705

theorem tailTrace_1975857 : CollatzResearch.WordTrace tailWord_1975857 prefixEnd_1975857 1014564345550781184100705 := by
  unfold tailWord_1975857
  simp only [CollatzResearch.WordTrace]
  refine ⟨72065425202815013354981825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48043616801876675569987883 72065425202815013354981825)
  ·
    refine ⟨54049068902111260016236369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72065425202815013354981825 54049068902111260016236369)
    ·
      refine ⟨40536801676583445012177277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54049068902111260016236369 40536801676583445012177277)
      ·
        refine ⟨15201300628718791879566479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40536801676583445012177277 15201300628718791879566479)
        ·
          refine ⟨22801950943078187819349719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15201300628718791879566479 22801950943078187819349719)
          ·
            refine ⟨34202926414617281729024579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22801950943078187819349719 34202926414617281729024579)
            ·
              refine ⟨51304389621925922593536869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34202926414617281729024579 51304389621925922593536869)
              ·
                refine ⟨9619573054111110486288163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51304389621925922593536869 9619573054111110486288163)
                ·
                  refine ⟨14429359581166665729432245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9619573054111110486288163 14429359581166665729432245)
                  ·
                    refine ⟨1352752460734374912134273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14429359581166665729432245 1352752460734374912134273)
                    ·
                      refine ⟨1014564345550781184100705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352752460734374912134273 1014564345550781184100705)
                      ·
                        rfl

theorem cell23_1975857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_1975857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975857 prefixEnd_1975857 := by exact prefixLift 1975857
  have htrace : WordTrace (prefixWord ++ tailWord_1975857) baseStart_1975857 baseEnd_1975857 := by
    simpa [prefixWord, tailWord_1975857, baseEnd_1975857] using wordTrace_append hprefix tailTrace_1975857
  have hstable : (prefixWord ++ tailWord_1975857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975857).length < 2 ^ (prefixWord ++ tailWord_1975857).sum := by decide
  have hdescent : baseEnd_1975857 < baseStart_1975857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975864 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_1975864 : Nat := 118140960795 + 1975864 * 2 ^ 59
def prefixEnd_1975864 : Nat := 4983230072969 + 3 ^ 40 * 1975864 * 2
def baseEnd_1975864 : Nat := 1014567939915362656713173

theorem tailTrace_1975864 : CollatzResearch.WordTrace tailWord_1975864 prefixEnd_1975864 1014567939915362656713173 := by
  unfold tailWord_1975864
  simp only [CollatzResearch.WordTrace]
  refine ⟨36032840256894826775243323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48043787009193102366991097 36032840256894826775243323)
  ·
    refine ⟨54049260385342240162864985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36032840256894826775243323 54049260385342240162864985)
    ·
      refine ⟨40536945289006680122148739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54049260385342240162864985 40536945289006680122148739)
      ·
        refine ⟨60805417933510020183223109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40536945289006680122148739 60805417933510020183223109)
        ·
          refine ⟨11401015862533128784354333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60805417933510020183223109 11401015862533128784354333)
          ·
            refine ⟨4275380948449923294132875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11401015862533128784354333 4275380948449923294132875)
            ·
              refine ⟨6413071422674884941199313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275380948449923294132875 6413071422674884941199313)
              ·
                refine ⟨4809803567006163705899485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413071422674884941199313 4809803567006163705899485)
                ·
                  refine ⟨1803676337627311389712307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4809803567006163705899485 1803676337627311389712307)
                  ·
                    refine ⟨2705514506440967084568461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1803676337627311389712307 2705514506440967084568461)
                    ·
                      refine ⟨1014567939915362656713173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2705514506440967084568461 1014567939915362656713173)
                      ·
                        rfl

theorem cell23_1975864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_1975864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975864 prefixEnd_1975864 := by exact prefixLift 1975864
  have htrace : WordTrace (prefixWord ++ tailWord_1975864) baseStart_1975864 baseEnd_1975864 := by
    simpa [prefixWord, tailWord_1975864, baseEnd_1975864] using wordTrace_append hprefix tailTrace_1975864
  have hstable : (prefixWord ++ tailWord_1975864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975864).length < 2 ^ (prefixWord ++ tailWord_1975864).sum := by decide
  have hdescent : baseEnd_1975864 < baseStart_1975864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975884 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_1975884 : Nat := 118140960795 + 1975884 * 2 ^ 59
def prefixEnd_1975884 : Nat := 4983230072969 + 3 ^ 40 * 1975884 * 2
def baseEnd_1975884 : Nat := 338192736509484192821027

theorem tailTrace_1975884 : CollatzResearch.WordTrace tailWord_1975884 prefixEnd_1975884 338192736509484192821027 := by
  unfold tailWord_1975884
  simp only [CollatzResearch.WordTrace]
  refine ⟨36033204986858598483107353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48044273315811464644143137 36033204986858598483107353)
  ·
    refine ⟨27024903740143948862330515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36033204986858598483107353 27024903740143948862330515)
    ·
      refine ⟨40537355610215923293495773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27024903740143948862330515 40537355610215923293495773)
      ·
        refine ⟨15201508353830971235060915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40537355610215923293495773 15201508353830971235060915)
        ·
          refine ⟨22802262530746456852591373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15201508353830971235060915 22802262530746456852591373)
          ·
            refine ⟨8550848449029921319721765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22802262530746456852591373 8550848449029921319721765)
            ·
              refine ⟨1603284084193110247447831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8550848449029921319721765 1603284084193110247447831)
              ·
                refine ⟨2404926126289665371171747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603284084193110247447831 2404926126289665371171747)
                ·
                  refine ⟨3607389189434498056757621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2404926126289665371171747 3607389189434498056757621)
                  ·
                    refine ⟨338192736509484192821027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3607389189434498056757621 338192736509484192821027)
                    ·
                      rfl

theorem cell23_1975884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_1975884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975884 prefixEnd_1975884 := by exact prefixLift 1975884
  have htrace : WordTrace (prefixWord ++ tailWord_1975884) baseStart_1975884 baseEnd_1975884 := by
    simpa [prefixWord, tailWord_1975884, baseEnd_1975884] using wordTrace_append hprefix tailTrace_1975884
  have hstable : (prefixWord ++ tailWord_1975884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975884).length < 2 ^ (prefixWord ++ tailWord_1975884).sum := by decide
  have hdescent : baseEnd_1975884 < baseStart_1975884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975907 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1975907 : Nat := 118140960795 + 1975907 * 2 ^ 59
def prefixEnd_1975907 : Nat := 4983230072969 + 3 ^ 40 * 1975907 * 2
def baseEnd_1975907 : Nat := 1014590019583505988475475

theorem tailTrace_1975907 : CollatzResearch.WordTrace tailWord_1975907 prefixEnd_1975907 1014590019583505988475475 := by
  unfold tailWord_1975907
  simp only [CollatzResearch.WordTrace]
  refine ⟨72067248852633871894301975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48044832568422581262867983 72067248852633871894301975)
  ·
    refine ⟨108100873278950807841452963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72067248852633871894301975 108100873278950807841452963)
    ·
      refine ⟨162151309918426211762179445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108100873278950807841452963 162151309918426211762179445)
      ·
        refine ⟨15201685304852457352704323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162151309918426211762179445 15201685304852457352704323)
        ·
          refine ⟨22802527957278686029056485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15201685304852457352704323 22802527957278686029056485)
          ·
            refine ⟨4275473991989753630448091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22802527957278686029056485 4275473991989753630448091)
            ·
              refine ⟨6413210987984630445672137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275473991989753630448091 6413210987984630445672137)
              ·
                refine ⟨4809908240988472834254103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413210987984630445672137 4809908240988472834254103)
                ·
                  refine ⟨7214862361482709251381155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809908240988472834254103 7214862361482709251381155)
                  ·
                    refine ⟨10822293542224063877071733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7214862361482709251381155 10822293542224063877071733)
                    ·
                      refine ⟨1014590019583505988475475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10822293542224063877071733 1014590019583505988475475)
                      ·
                        rfl

theorem cell23_1975907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1975907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975907 prefixEnd_1975907 := by exact prefixLift 1975907
  have htrace : WordTrace (prefixWord ++ tailWord_1975907) baseStart_1975907 baseEnd_1975907 := by
    simpa [prefixWord, tailWord_1975907, baseEnd_1975907] using wordTrace_append hprefix tailTrace_1975907
  have hstable : (prefixWord ++ tailWord_1975907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975907).length < 2 ^ (prefixWord ++ tailWord_1975907).sum := by decide
  have hdescent : baseEnd_1975907 < baseStart_1975907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975914 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1975914 : Nat := 118140960795 + 1975914 * 2 ^ 59
def prefixEnd_1975914 : Nat := 4983230072969 + 3 ^ 40 * 1975914 * 2
def baseEnd_1975914 : Nat := 338197871316029153695981

theorem tailTrace_1975914 : CollatzResearch.WordTrace tailWord_1975914 prefixEnd_1975914 338197871316029153695981 := by
  unfold tailWord_1975914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016876040902128022451699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48045002775739008059871197 18016876040902128022451699)
  ·
    refine ⟨27025314061353192033677549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18016876040902128022451699 27025314061353192033677549)
    ·
      refine ⟨10134492773007447012629081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27025314061353192033677549 10134492773007447012629081)
      ·
        refine ⟨7600869579755585259471811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10134492773007447012629081 7600869579755585259471811)
        ·
          refine ⟨11401304369633377889207717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7600869579755585259471811 11401304369633377889207717)
          ·
            refine ⟨2137744569306258354226447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11401304369633377889207717 2137744569306258354226447)
            ·
              refine ⟨3206616853959387531339671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137744569306258354226447 3206616853959387531339671)
              ·
                refine ⟨4809925280939081297009507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3206616853959387531339671 4809925280939081297009507)
                ·
                  refine ⟨7214887921408621945514261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4809925280939081297009507 7214887921408621945514261)
                  ·
                    refine ⟨338197871316029153695981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7214887921408621945514261 338197871316029153695981)
                    ·
                      rfl

theorem cell23_1975914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1975914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975914 prefixEnd_1975914 := by exact prefixLift 1975914
  have htrace : WordTrace (prefixWord ++ tailWord_1975914) baseStart_1975914 baseEnd_1975914 := by
    simpa [prefixWord, tailWord_1975914, baseEnd_1975914] using wordTrace_append hprefix tailTrace_1975914
  have hstable : (prefixWord ++ tailWord_1975914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975914).length < 2 ^ (prefixWord ++ tailWord_1975914).sum := by decide
  have hdescent : baseEnd_1975914 < baseStart_1975914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975944 : List Nat := [2, 1, 3, 5, 1, 2, 9]
def baseStart_1975944 : Nat := 118140960795 + 1975944 * 2 ^ 59
def prefixEnd_1975944 : Nat := 4983230072969 + 3 ^ 40 * 1975944 * 2
def baseEnd_1975944 : Nat := 12526037263799041280405

theorem tailTrace_1975944 : CollatzResearch.WordTrace tailWord_1975944 prefixEnd_1975944 12526037263799041280405 := by
  unfold tailWord_1975944
  simp only [CollatzResearch.WordTrace]
  refine ⟨36034299176749913606699443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48045732235666551475599257 36034299176749913606699443)
  ·
    refine ⟨54051448765124870410049165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36034299176749913606699443 54051448765124870410049165)
    ·
      refine ⟨20269293286921826403768437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54051448765124870410049165 20269293286921826403768437)
      ·
        refine ⟨1900246245648921225353291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20269293286921826403768437 1900246245648921225353291)
        ·
          refine ⟨2850369368473381838029937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900246245648921225353291 2850369368473381838029937)
          ·
            refine ⟨2137777026355036378522453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850369368473381838029937 2137777026355036378522453)
            ·
              refine ⟨12526037263799041280405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2137777026355036378522453 12526037263799041280405)
              ·
                rfl

theorem cell23_1975944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 9].length) (baseStart_1975944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975944 prefixEnd_1975944 := by exact prefixLift 1975944
  have htrace : WordTrace (prefixWord ++ tailWord_1975944) baseStart_1975944 baseEnd_1975944 := by
    simpa [prefixWord, tailWord_1975944, baseEnd_1975944] using wordTrace_append hprefix tailTrace_1975944
  have hstable : (prefixWord ++ tailWord_1975944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975944).length < 2 ^ (prefixWord ++ tailWord_1975944).sum := by decide
  have hdescent : baseEnd_1975944 < baseStart_1975944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975980 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1975980 : Nat := 118140960795 + 1975980 * 2 ^ 59
def prefixEnd_1975980 : Nat := 4983230072969 + 3 ^ 40 * 1975980 * 2
def baseEnd_1975980 : Nat := 1014627503671284202862639

theorem tailTrace_1975980 : CollatzResearch.WordTrace tailWord_1975980 prefixEnd_1975980 1014627503671284202862639 := by
  unfold tailWord_1975980
  simp only [CollatzResearch.WordTrace]
  refine ⟨36034955690684702680854697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48046607587579603574472929 36034955690684702680854697)
  ·
    refine ⟨27026216768013527010641023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36034955690684702680854697 27026216768013527010641023)
    ·
      refine ⟨40539325152020290515961535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27026216768013527010641023 40539325152020290515961535)
      ·
        refine ⟨60808987728030435773942303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40539325152020290515961535 60808987728030435773942303)
        ·
          refine ⟨91213481592045653660913455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60808987728030435773942303 91213481592045653660913455)
          ·
            refine ⟨136820222388068480491370183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91213481592045653660913455 136820222388068480491370183)
            ·
              refine ⟨205230333582102720737055275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136820222388068480491370183 205230333582102720737055275)
              ·
                refine ⟨307845500373154081105582913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205230333582102720737055275 307845500373154081105582913)
                ·
                  refine ⟨230884125279865560829187185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307845500373154081105582913 230884125279865560829187185)
                  ·
                    refine ⟨173163093959899170621890389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 230884125279865560829187185 173163093959899170621890389)
                    ·
                      refine ⟨1014627503671284202862639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 173163093959899170621890389 1014627503671284202862639)
                      ·
                        rfl

theorem cell23_1975980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1975980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975980 prefixEnd_1975980 := by exact prefixLift 1975980
  have htrace : WordTrace (prefixWord ++ tailWord_1975980) baseStart_1975980 baseEnd_1975980 := by
    simpa [prefixWord, tailWord_1975980, baseEnd_1975980] using wordTrace_append hprefix tailTrace_1975980
  have hstable : (prefixWord ++ tailWord_1975980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975980).length < 2 ^ (prefixWord ++ tailWord_1975980).sum := by decide
  have hdescent : baseEnd_1975980 < baseStart_1975980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975981 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_1975981 : Nat := 118140960795 + 1975981 * 2 ^ 59
def prefixEnd_1975981 : Nat := 4983230072969 + 3 ^ 40 * 1975981 * 2
def baseEnd_1975981 : Nat := 1014628017151938698950135

theorem tailTrace_1975981 : CollatzResearch.WordTrace tailWord_1975981 prefixEnd_1975981 1014628017151938698950135 := by
  unfold tailWord_1975981
  simp only [CollatzResearch.WordTrace]
  refine ⟨72069947854365782532495797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48046631902910521688330531 72069947854365782532495797)
  ·
    refine ⟨6756557611346792112421481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72069947854365782532495797 6756557611346792112421481)
    ·
      refine ⟨5067418208510094084316111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6756557611346792112421481 5067418208510094084316111)
      ·
        refine ⟨7601127312765141126474167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067418208510094084316111 7601127312765141126474167)
        ·
          refine ⟨11401690969147711689711251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7601127312765141126474167 11401690969147711689711251)
          ·
            refine ⟨17102536453721567534566877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11401690969147711689711251 17102536453721567534566877)
            ·
              refine ⟨6413451170145587825462579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17102536453721567534566877 6413451170145587825462579)
              ·
                refine ⟨9620176755218381738193869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413451170145587825462579 9620176755218381738193869)
                ·
                  refine ⟨3607566283206893151822701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9620176755218381738193869 3607566283206893151822701)
                  ·
                    refine ⟨1352837356202584931933513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3607566283206893151822701 1352837356202584931933513)
                    ·
                      refine ⟨1014628017151938698950135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352837356202584931933513 1014628017151938698950135)
                      ·
                        rfl

theorem cell23_1975981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_1975981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975981 prefixEnd_1975981 := by exact prefixLift 1975981
  have htrace : WordTrace (prefixWord ++ tailWord_1975981) baseStart_1975981 baseEnd_1975981 := by
    simpa [prefixWord, tailWord_1975981, baseEnd_1975981] using wordTrace_append hprefix tailTrace_1975981
  have hstable : (prefixWord ++ tailWord_1975981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975981).length < 2 ^ (prefixWord ++ tailWord_1975981).sum := by decide
  have hdescent : baseEnd_1975981 < baseStart_1975981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975994 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2]
def baseStart_1975994 : Nat := 118140960795 + 1975994 * 2 ^ 59
def prefixEnd_1975994 : Nat := 4983230072969 + 3 ^ 40 * 1975994 * 2
def baseEnd_1975994 : Nat := 1014634692400447148087575

theorem tailTrace_1975994 : CollatzResearch.WordTrace tailWord_1975994 prefixEnd_1975994 1014634692400447148087575 := by
  unfold tailWord_1975994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017605500829671438179759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48046948002212457168479357 18017605500829671438179759)
  ·
    refine ⟨27026408251244507157269639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18017605500829671438179759 27026408251244507157269639)
    ·
      refine ⟨40539612376866760735904459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27026408251244507157269639 40539612376866760735904459)
      ·
        refine ⟨60809418565300141103856689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40539612376866760735904459 60809418565300141103856689)
        ·
          refine ⟨45607063923975105827892517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60809418565300141103856689 45607063923975105827892517)
          ·
            refine ⟨8551324485745332342729847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45607063923975105827892517 8551324485745332342729847)
            ·
              refine ⟨12826986728617998514094771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8551324485745332342729847 12826986728617998514094771)
              ·
                refine ⟨19240480092926997771142157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12826986728617998514094771 19240480092926997771142157)
                ·
                  refine ⟨7215180034847624164178309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19240480092926997771142157 7215180034847624164178309)
                  ·
                    refine ⟨1352846256533929530783433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7215180034847624164178309 1352846256533929530783433)
                    ·
                      refine ⟨1014634692400447148087575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352846256533929530783433 1014634692400447148087575)
                      ·
                        rfl

theorem cell23_1975994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_1975994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975994 prefixEnd_1975994 := by exact prefixLift 1975994
  have htrace : WordTrace (prefixWord ++ tailWord_1975994) baseStart_1975994 baseEnd_1975994 := by
    simpa [prefixWord, tailWord_1975994, baseEnd_1975994] using wordTrace_append hprefix tailTrace_1975994
  have hstable : (prefixWord ++ tailWord_1975994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975994).length < 2 ^ (prefixWord ++ tailWord_1975994).sum := by decide
  have hdescent : baseEnd_1975994 < baseStart_1975994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1975997 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1975997 : Nat := 118140960795 + 1975997 * 2 ^ 59
def prefixEnd_1975997 : Nat := 4983230072969 + 3 ^ 40 * 1975997 * 2
def baseEnd_1975997 : Nat := 1014636232842410636350061

theorem tailTrace_1975997 : CollatzResearch.WordTrace tailWord_1975997 prefixEnd_1975997 1014636232842410636350061 := by
  unfold tailWord_1975997
  simp only [CollatzResearch.WordTrace]
  refine ⟨72070531422307817265078245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48047020948205211510052163 72070531422307817265078245)
  ·
    refine ⟨13513224641682715737202171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72070531422307817265078245 13513224641682715737202171)
    ·
      refine ⟨20269836962524073605803257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13513224641682715737202171 20269836962524073605803257)
      ·
        refine ⟨15202377721893055204352443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20269836962524073605803257 15202377721893055204352443)
        ·
          refine ⟨22803566582839582806528665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15202377721893055204352443 22803566582839582806528665)
          ·
            refine ⟨17102674937129687104896499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22803566582839582806528665 17102674937129687104896499)
            ·
              refine ⟨25654012405694530657344749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17102674937129687104896499 25654012405694530657344749)
              ·
                refine ⟨9620254652135448996504281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25654012405694530657344749 9620254652135448996504281)
                ·
                  refine ⟨7215190989101586747378211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9620254652135448996504281 7215190989101586747378211)
                  ·
                    refine ⟨10822786483652380121067317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7215190989101586747378211 10822786483652380121067317)
                    ·
                      refine ⟨1014636232842410636350061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10822786483652380121067317 1014636232842410636350061)
                      ·
                        rfl

theorem cell23_1975997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1975997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1975997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1975997 prefixEnd_1975997 := by exact prefixLift 1975997
  have htrace : WordTrace (prefixWord ++ tailWord_1975997) baseStart_1975997 baseEnd_1975997 := by
    simpa [prefixWord, tailWord_1975997, baseEnd_1975997] using wordTrace_append hprefix tailTrace_1975997
  have hstable : (prefixWord ++ tailWord_1975997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1975997).length < 2 ^ (prefixWord ++ tailWord_1975997).sum := by decide
  have hdescent : baseEnd_1975997 < baseStart_1975997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1975997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976006 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1976006 : Nat := 118140960795 + 1976006 * 2 ^ 59
def prefixEnd_1976006 : Nat := 4983230072969 + 3 ^ 40 * 1976006 * 2
def baseEnd_1976006 : Nat := 1014640854168301101137521

theorem tailTrace_1976006 : CollatzResearch.WordTrace tailWord_1976006 prefixEnd_1976006 1014640854168301101137521 := by
  unfold tailWord_1976006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252214364977350368817371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48047239786183474534770581 2252214364977350368817371)
  ·
    refine ⟨3378321547466025553226057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252214364977350368817371 3378321547466025553226057)
    ·
      refine ⟨2533741160599519164919543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3378321547466025553226057 2533741160599519164919543)
      ·
        refine ⟨3800611740899278747379315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533741160599519164919543 3800611740899278747379315)
        ·
          refine ⟨5700917611348918121068973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800611740899278747379315 5700917611348918121068973)
          ·
            refine ⟨2137844104255844295400865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5700917611348918121068973 2137844104255844295400865)
            ·
              refine ⟨1603383078191883221550649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137844104255844295400865 1603383078191883221550649)
              ·
                refine ⟨1202537308643912416162987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603383078191883221550649 1202537308643912416162987)
                ·
                  refine ⟨1803805962965868624244481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202537308643912416162987 1803805962965868624244481)
                  ·
                    refine ⟨1352854472224401468183361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1803805962965868624244481 1352854472224401468183361)
                    ·
                      refine ⟨1014640854168301101137521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352854472224401468183361 1014640854168301101137521)
                      ·
                        rfl

theorem cell23_1976006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1976006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976006 prefixEnd_1976006 := by exact prefixLift 1976006
  have htrace : WordTrace (prefixWord ++ tailWord_1976006) baseStart_1976006 baseEnd_1976006 := by
    simpa [prefixWord, tailWord_1976006, baseEnd_1976006] using wordTrace_append hprefix tailTrace_1976006
  have hstable : (prefixWord ++ tailWord_1976006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976006).length < 2 ^ (prefixWord ++ tailWord_1976006).sum := by decide
  have hdescent : baseEnd_1976006 < baseStart_1976006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976007 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1976007 : Nat := 118140960795 + 1976007 * 2 ^ 59
def prefixEnd_1976007 : Nat := 4983230072969 + 3 ^ 40 * 1976007 * 2
def baseEnd_1976007 : Nat := 1014641367648955597225015

theorem tailTrace_1976007 : CollatzResearch.WordTrace tailWord_1976007 prefixEnd_1976007 1014641367648955597225015 := by
  unfold tailWord_1976007
  simp only [CollatzResearch.WordTrace]
  refine ⟨72070896152271588972942275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48047264101514392648628183 72070896152271588972942275)
  ·
    refine ⟨108106344228407383459413413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72070896152271588972942275 108106344228407383459413413)
    ·
      refine ⟨20269939542826384398640015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108106344228407383459413413 20269939542826384398640015)
      ·
        refine ⟨30404909314239576597960023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20269939542826384398640015 30404909314239576597960023)
        ·
          refine ⟨45607363971359364896940035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30404909314239576597960023 45607363971359364896940035)
          ·
            refine ⟨68411045957039047345410053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45607363971359364896940035 68411045957039047345410053)
            ·
              refine ⟨12827071116944821377264385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68411045957039047345410053 12827071116944821377264385)
              ·
                refine ⟨9620303337708616032948289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12827071116944821377264385 9620303337708616032948289)
                ·
                  refine ⟨7215227503281462024711217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9620303337708616032948289 7215227503281462024711217)
                  ·
                    refine ⟨5411420627461096518533413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7215227503281462024711217 5411420627461096518533413)
                    ·
                      refine ⟨1014641367648955597225015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5411420627461096518533413 1014641367648955597225015)
                      ·
                        rfl

theorem cell23_1976007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1976007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976007 prefixEnd_1976007 := by exact prefixLift 1976007
  have htrace : WordTrace (prefixWord ++ tailWord_1976007) baseStart_1976007 baseEnd_1976007 := by
    simpa [prefixWord, tailWord_1976007, baseEnd_1976007] using wordTrace_append hprefix tailTrace_1976007
  have hstable : (prefixWord ++ tailWord_1976007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976007).length < 2 ^ (prefixWord ++ tailWord_1976007).sum := by decide
  have hdescent : baseEnd_1976007 < baseStart_1976007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976047 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 1, 7]
def baseStart_1976047 : Nat := 118140960795 + 1976047 * 2 ^ 59
def prefixEnd_1976047 : Nat := 4983230072969 + 3 ^ 40 * 1976047 * 2
def baseEnd_1976047 : Nat := 338220635625045146908277

theorem tailTrace_1976047 : CollatzResearch.WordTrace tailWord_1976047 prefixEnd_1976047 338220635625045146908277 := by
  unfold tailWord_1976047
  simp only [CollatzResearch.WordTrace]
  refine ⟨72072355072126675804398395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48048236714751117202932263 72072355072126675804398395)
  ·
    refine ⟨108108532608190013706597593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72072355072126675804398395 108108532608190013706597593)
    ·
      refine ⟨81081399456142510279948195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108108532608190013706597593 81081399456142510279948195)
      ·
        refine ⟨121622099184213765419922293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81081399456142510279948195 121622099184213765419922293)
        ·
          refine ⟨11402071798520040508117715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121622099184213765419922293 11402071798520040508117715)
          ·
            refine ⟨17103107697780060762176573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402071798520040508117715 17103107697780060762176573)
            ·
              refine ⟨6413665386667522785816215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17103107697780060762176573 6413665386667522785816215)
              ·
                refine ⟨9620498080001284178724323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6413665386667522785816215 9620498080001284178724323)
                ·
                  refine ⟨14430747120001926268086485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9620498080001284178724323 14430747120001926268086485)
                  ·
                    refine ⟨338220635625045146908277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14430747120001926268086485 338220635625045146908277)
                    ·
                      rfl

theorem cell23_1976047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_1976047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976047 prefixEnd_1976047 := by exact prefixLift 1976047
  have htrace : WordTrace (prefixWord ++ tailWord_1976047) baseStart_1976047 baseEnd_1976047 := by
    simpa [prefixWord, tailWord_1976047, baseEnd_1976047] using wordTrace_append hprefix tailTrace_1976047
  have hstable : (prefixWord ++ tailWord_1976047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976047).length < 2 ^ (prefixWord ++ tailWord_1976047).sum := by decide
  have hdescent : baseEnd_1976047 < baseStart_1976047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976062 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1976062 : Nat := 118140960795 + 1976062 * 2 ^ 59
def prefixEnd_1976062 : Nat := 4983230072969 + 3 ^ 40 * 1976062 * 2
def baseEnd_1976062 : Nat := 1014669609084952882037263

theorem tailTrace_1976062 : CollatzResearch.WordTrace tailWord_1976062 prefixEnd_1976062 1014669609084952882037263 := by
  unfold tailWord_1976062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9009112770884041670774305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48048601444714888910796293 9009112770884041670774305)
  ·
    refine ⟨6756834578163031253080729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9009112770884041670774305 6756834578163031253080729)
    ·
      refine ⟨5067625933622273439810547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6756834578163031253080729 5067625933622273439810547)
      ·
        refine ⟨7601438900433410159715821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5067625933622273439810547 7601438900433410159715821)
        ·
          refine ⟨2850539587662528809893433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7601438900433410159715821 2850539587662528809893433)
          ·
            refine ⟨2137904690746896607420075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850539587662528809893433 2137904690746896607420075)
            ·
              refine ⟨3206857036120344911130113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137904690746896607420075 3206857036120344911130113)
              ·
                refine ⟨2405142777090258683347585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206857036120344911130113 2405142777090258683347585)
                ·
                  refine ⟨1803857082817694012510689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2405142777090258683347585 1803857082817694012510689)
                  ·
                    refine ⟨1352892812113270509383017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1803857082817694012510689 1352892812113270509383017)
                    ·
                      refine ⟨1014669609084952882037263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1352892812113270509383017 1014669609084952882037263)
                      ·
                        rfl

theorem cell23_1976062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1976062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976062 prefixEnd_1976062 := by exact prefixLift 1976062
  have htrace : WordTrace (prefixWord ++ tailWord_1976062) baseStart_1976062 baseEnd_1976062 := by
    simpa [prefixWord, tailWord_1976062, baseEnd_1976062] using wordTrace_append hprefix tailTrace_1976062
  have hstable : (prefixWord ++ tailWord_1976062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976062).length < 2 ^ (prefixWord ++ tailWord_1976062).sum := by decide
  have hdescent : baseEnd_1976062 < baseStart_1976062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976118 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1976118 : Nat := 118140960795 + 1976118 * 2 ^ 59
def prefixEnd_1976118 : Nat := 4983230072969 + 3 ^ 40 * 1976118 * 2
def baseEnd_1976118 : Nat := 1014698364001604662937005

theorem tailTrace_1976118 : CollatzResearch.WordTrace tailWord_1976118 prefixEnd_1976118 1014698364001604662937005 := by
  unfold tailWord_1976118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4504684040929340933139563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48049963103246303286822005 4504684040929340933139563)
  ·
    refine ⟨6757026061394011399709345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4504684040929340933139563 6757026061394011399709345)
    ·
      refine ⟨5067769546045508549782009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6757026061394011399709345 5067769546045508549782009)
      ·
        refine ⟨3800827159534131412336507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5067769546045508549782009 3800827159534131412336507)
        ·
          refine ⟨5701240739301197118504761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800827159534131412336507 5701240739301197118504761)
          ·
            refine ⟨4275930554475897838878571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5701240739301197118504761 4275930554475897838878571)
            ·
              refine ⟨6413895831713846758317857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275930554475897838878571 6413895831713846758317857)
              ·
                refine ⟨4810421873785385068738393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6413895831713846758317857 4810421873785385068738393)
                ·
                  refine ⟨3607816405339038801553795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810421873785385068738393 3607816405339038801553795)
                  ·
                    refine ⟨5411724608008558202330693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3607816405339038801553795 5411724608008558202330693)
                    ·
                      refine ⟨1014698364001604662937005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5411724608008558202330693 1014698364001604662937005)
                      ·
                        rfl

theorem cell23_1976118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1976118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976118 prefixEnd_1976118 := by exact prefixLift 1976118
  have htrace : WordTrace (prefixWord ++ tailWord_1976118) baseStart_1976118 baseEnd_1976118 := by
    simpa [prefixWord, tailWord_1976118, baseEnd_1976118] using wordTrace_append hprefix tailTrace_1976118
  have hstable : (prefixWord ++ tailWord_1976118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976118).length < 2 ^ (prefixWord ++ tailWord_1976118).sum := by decide
  have hdescent : baseEnd_1976118 < baseStart_1976118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976154 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 3, 5]
def baseStart_1976154 : Nat := 118140960795 + 1976154 * 2 ^ 59
def prefixEnd_1976154 : Nat := 4983230072969 + 3 ^ 40 * 1976154 * 2
def baseEnd_1976154 : Nat := 338238949768388840695613

theorem tailTrace_1976154 : CollatzResearch.WordTrace tailWord_1976154 prefixEnd_1976154 338238949768388840695613 := by
  unfold tailWord_1976154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18019064420684758269635879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48050838455159355385695677 18019064420684758269635879)
  ·
    refine ⟨27028596631027137404453819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18019064420684758269635879 27028596631027137404453819)
    ·
      refine ⟨40542894946540706106680729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27028596631027137404453819 40542894946540706106680729)
      ·
        refine ⟨30407171209905529580010547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40542894946540706106680729 30407171209905529580010547)
        ·
          refine ⟨45610756814858294370015821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30407171209905529580010547 45610756814858294370015821)
          ·
            refine ⟨17104033805571860388755933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45610756814858294370015821 17104033805571860388755933)
            ·
              refine ⟨6414012677089447645783475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17104033805571860388755933 6414012677089447645783475)
              ·
                refine ⟨9621019015634171468675213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6414012677089447645783475 9621019015634171468675213)
                ·
                  refine ⟨3607882130862814300753205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9621019015634171468675213 3607882130862814300753205)
                  ·
                    refine ⟨338238949768388840695613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3607882130862814300753205 338238949768388840695613)
                    ·
                      rfl

theorem cell23_1976154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_1976154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976154 prefixEnd_1976154 := by exact prefixLift 1976154
  have htrace : WordTrace (prefixWord ++ tailWord_1976154) baseStart_1976154 baseEnd_1976154 := by
    simpa [prefixWord, tailWord_1976154, baseEnd_1976154] using wordTrace_append hprefix tailTrace_1976154
  have hstable : (prefixWord ++ tailWord_1976154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976154).length < 2 ^ (prefixWord ++ tailWord_1976154).sum := by decide
  have hdescent : baseEnd_1976154 < baseStart_1976154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976184 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 8, 4]
def baseStart_1976184 : Nat := 118140960795 + 1976184 * 2 ^ 59
def prefixEnd_1976184 : Nat := 4983230072969 + 3 ^ 40 * 1976184 * 2
def baseEnd_1976184 : Nat := 338244084574933801570567

theorem tailTrace_1976184 : CollatzResearch.WordTrace tailWord_1976184 prefixEnd_1976184 338244084574933801570567 := by
  unfold tailWord_1976184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36038675936315174101067803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48051567915086898801423737 36038675936315174101067803)
  ·
    refine ⟨54058013904472761151601705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36038675936315174101067803 54058013904472761151601705)
    ·
      refine ⟨40543510428354570863701279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54058013904472761151601705 40543510428354570863701279)
      ·
        refine ⟨60815265642531856295551919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40543510428354570863701279 60815265642531856295551919)
        ·
          refine ⟨91222898463797784443327879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60815265642531856295551919 91222898463797784443327879)
          ·
            refine ⟨136834347695696676664991819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91222898463797784443327879 136834347695696676664991819)
            ·
              refine ⟨205251521543545014997487729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136834347695696676664991819 205251521543545014997487729)
              ·
                refine ⟨153938641157658761248115797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205251521543545014997487729 153938641157658761248115797)
                ·
                  refine ⟨1803968451066313608376357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 153938641157658761248115797 1803968451066313608376357)
                  ·
                    refine ⟨338244084574933801570567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803968451066313608376357 338244084574933801570567)
                    ·
                      rfl

theorem cell23_1976184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_1976184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976184 prefixEnd_1976184 := by exact prefixLift 1976184
  have htrace : WordTrace (prefixWord ++ tailWord_1976184) baseStart_1976184 baseEnd_1976184 := by
    simpa [prefixWord, tailWord_1976184, baseEnd_1976184] using wordTrace_append hprefix tailTrace_1976184
  have hstable : (prefixWord ++ tailWord_1976184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976184).length < 2 ^ (prefixWord ++ tailWord_1976184).sum := by decide
  have hdescent : baseEnd_1976184 < baseStart_1976184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976201 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 2, 4]
def baseStart_1976201 : Nat := 118140960795 + 1976201 * 2 ^ 59
def prefixEnd_1976201 : Nat := 4983230072969 + 3 ^ 40 * 1976201 * 2
def baseEnd_1976201 : Nat := 338246994298642612733041

theorem tailTrace_1976201 : CollatzResearch.WordTrace tailWord_1976201 prefixEnd_1976201 338246994298642612733041 := by
  unfold tailWord_1976201
  simp only [CollatzResearch.WordTrace]
  refine ⟨72077971913568760105504457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48051981275712506737002971 72077971913568760105504457)
  ·
    refine ⟨54058478935176570079128343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72077971913568760105504457 54058478935176570079128343)
    ·
      refine ⟨81087718402764855118692515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54058478935176570079128343 81087718402764855118692515)
      ·
        refine ⟨121631577604147282678038773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81087718402764855118692515 121631577604147282678038773)
        ·
          refine ⟨11402960400388807751066135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121631577604147282678038773 11402960400388807751066135)
          ·
            refine ⟨17104440600583211626599203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11402960400388807751066135 17104440600583211626599203)
            ·
              refine ⟨25656660900874817439898805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17104440600583211626599203 25656660900874817439898805)
              ·
                refine ⟨2405311959457014134990513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25656660900874817439898805 2405311959457014134990513)
                ·
                  refine ⟨1803983969592760601242885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2405311959457014134990513 1803983969592760601242885)
                  ·
                    refine ⟨338246994298642612733041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1803983969592760601242885 338246994298642612733041)
                    ·
                      rfl

theorem cell23_1976201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_1976201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976201 prefixEnd_1976201 := by exact prefixLift 1976201
  have htrace : WordTrace (prefixWord ++ tailWord_1976201) baseStart_1976201 baseEnd_1976201 := by
    simpa [prefixWord, tailWord_1976201, baseEnd_1976201] using wordTrace_append hprefix tailTrace_1976201
  have hstable : (prefixWord ++ tailWord_1976201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976201).length < 2 ^ (prefixWord ++ tailWord_1976201).sum := by decide
  have hdescent : baseEnd_1976201 < baseStart_1976201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976221 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1976221 : Nat := 118140960795 + 1976221 * 2 ^ 59
def prefixEnd_1976221 : Nat := 4983230072969 + 3 ^ 40 * 1976221 * 2
def baseEnd_1976221 : Nat := 1014751252509017759949031

theorem tailTrace_1976221 : CollatzResearch.WordTrace tailWord_1976221 prefixEnd_1976221 1014751252509017759949031 := by
  unfold tailWord_1976221
  simp only [CollatzResearch.WordTrace]
  refine ⟨72078701373496303521232517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48052467582330869014155011 72078701373496303521232517)
  ·
    refine ⟨13514756507530556910231097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72078701373496303521232517 13514756507530556910231097)
    ·
      refine ⟨10136067380647917682673323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13514756507530556910231097 10136067380647917682673323)
      ·
        refine ⟨15204101070971876524009985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10136067380647917682673323 15204101070971876524009985)
        ·
          refine ⟨11403075803228907393007489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15204101070971876524009985 11403075803228907393007489)
          ·
            refine ⟨8552306852421680544755617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11403075803228907393007489 8552306852421680544755617)
            ·
              refine ⟨6414230139316260408566713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8552306852421680544755617 6414230139316260408566713)
              ·
                refine ⟨4810672604487195306425035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6414230139316260408566713 4810672604487195306425035)
                ·
                  refine ⟨7216008906730792959637553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4810672604487195306425035 7216008906730792959637553)
                  ·
                    refine ⟨5412006680048094719728165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7216008906730792959637553 5412006680048094719728165)
                    ·
                      refine ⟨1014751252509017759949031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5412006680048094719728165 1014751252509017759949031)
                      ·
                        rfl

theorem cell23_1976221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1976221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976221 prefixEnd_1976221 := by exact prefixLift 1976221
  have htrace : WordTrace (prefixWord ++ tailWord_1976221) baseStart_1976221 baseEnd_1976221 := by
    simpa [prefixWord, tailWord_1976221, baseEnd_1976221] using wordTrace_append hprefix tailTrace_1976221
  have hstable : (prefixWord ++ tailWord_1976221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976221).length < 2 ^ (prefixWord ++ tailWord_1976221).sum := by decide
  have hdescent : baseEnd_1976221 < baseStart_1976221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976228 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_1976228 : Nat := 118140960795 + 1976228 * 2 ^ 59
def prefixEnd_1976228 : Nat := 4983230072969 + 3 ^ 40 * 1976228 * 2
def baseEnd_1976228 : Nat := 1014754846873599232561499

theorem tailTrace_1976228 : CollatzResearch.WordTrace tailWord_1976228 prefixEnd_1976228 1014754846873599232561499 := by
  unfold tailWord_1976228
  simp only [CollatzResearch.WordTrace]
  refine ⟨36039478342235471858368669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48052637789647295811158225 36039478342235471858368669)
  ·
    refine ⟨13514804378338301946888251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36039478342235471858368669 13514804378338301946888251)
    ·
      refine ⟨20272206567507452920332377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13514804378338301946888251 20272206567507452920332377)
      ·
        refine ⟨15204154925630589690249283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20272206567507452920332377 15204154925630589690249283)
        ·
          refine ⟨22806232388445884535373925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15204154925630589690249283 22806232388445884535373925)
          ·
            refine ⟨4276168572833603350382611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22806232388445884535373925 4276168572833603350382611)
            ·
              refine ⟨6414252859250405025573917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4276168572833603350382611 6414252859250405025573917)
              ·
                refine ⟨2405344822218901884590219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6414252859250405025573917 2405344822218901884590219)
                ·
                  refine ⟨3608017233328352826885329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405344822218901884590219 3608017233328352826885329)
                  ·
                    refine ⟨2706012924996264620163997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608017233328352826885329 2706012924996264620163997)
                    ·
                      refine ⟨1014754846873599232561499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2706012924996264620163997 1014754846873599232561499)
                      ·
                        rfl

theorem cell23_1976228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_1976228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976228 prefixEnd_1976228 := by exact prefixLift 1976228
  have htrace : WordTrace (prefixWord ++ tailWord_1976228) baseStart_1976228 baseEnd_1976228 := by
    simpa [prefixWord, tailWord_1976228, baseEnd_1976228] using wordTrace_append hprefix tailTrace_1976228
  have hstable : (prefixWord ++ tailWord_1976228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976228).length < 2 ^ (prefixWord ++ tailWord_1976228).sum := by decide
  have hdescent : baseEnd_1976228 < baseStart_1976228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976252 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1976252 : Nat := 118140960795 + 1976252 * 2 ^ 59
def prefixEnd_1976252 : Nat := 4983230072969 + 3 ^ 40 * 1976252 * 2
def baseEnd_1976252 : Nat := 338255723469769046220463

theorem tailTrace_1976252 : CollatzResearch.WordTrace tailWord_1976252 prefixEnd_1976252 338255723469769046220463 := by
  unfold tailWord_1976252
  simp only [CollatzResearch.WordTrace]
  refine ⟨36039916018191997907805505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48053221357589330543740673 36039916018191997907805505)
  ·
    refine ⟨27029937013643998430854129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36039916018191997907805505 27029937013643998430854129)
    ·
      refine ⟨20272452760232998823140597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27029937013643998430854129 20272452760232998823140597)
      ·
        refine ⟨1900542446271843639669431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20272452760232998823140597 1900542446271843639669431)
        ·
          refine ⟨2850813669407765459504147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900542446271843639669431 2850813669407765459504147)
          ·
            refine ⟨4276220504111648189256221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2850813669407765459504147 4276220504111648189256221)
            ·
              refine ⟨1603582689041868070971083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4276220504111648189256221 1603582689041868070971083)
              ·
                refine ⟨2405374033562802106456625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603582689041868070971083 2405374033562802106456625)
                ·
                  refine ⟨1804030525172101579842469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2405374033562802106456625 1804030525172101579842469)
                  ·
                    refine ⟨338255723469769046220463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804030525172101579842469 338255723469769046220463)
                    ·
                      rfl

theorem cell23_1976252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1976252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976252 prefixEnd_1976252 := by exact prefixLift 1976252
  have htrace : WordTrace (prefixWord ++ tailWord_1976252) baseStart_1976252 baseEnd_1976252 := by
    simpa [prefixWord, tailWord_1976252, baseEnd_1976252] using wordTrace_append hprefix tailTrace_1976252
  have hstable : (prefixWord ++ tailWord_1976252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976252).length < 2 ^ (prefixWord ++ tailWord_1976252).sum := by decide
  have hdescent : baseEnd_1976252 < baseStart_1976252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976318 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1976318 : Nat := 118140960795 + 1976318 * 2 ^ 59
def prefixEnd_1976318 : Nat := 4983230072969 + 3 ^ 40 * 1976318 * 2
def baseEnd_1976318 : Nat := 1014801060132503880436085

theorem tailTrace_1976318 : CollatzResearch.WordTrace tailWord_1976318 prefixEnd_1976318 1014801060132503880436085 := by
  unfold tailWord_1976318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9010279906768111135939201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48054826169429926058342405 9010279906768111135939201)
  ·
    refine ⟨6757709930076083351954401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9010279906768111135939201 6757709930076083351954401)
    ·
      refine ⟨5068282447557062513965801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6757709930076083351954401 5068282447557062513965801)
      ·
        refine ⟨3801211835667796885474351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5068282447557062513965801 3801211835667796885474351)
        ·
          refine ⟨5701817753501695328211527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801211835667796885474351 5701817753501695328211527)
          ·
            refine ⟨8552726630252542992317291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5701817753501695328211527 8552726630252542992317291)
            ·
              refine ⟨12829089945378814488475937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552726630252542992317291 12829089945378814488475937)
              ·
                refine ⟨9621817459034110866356953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12829089945378814488475937 9621817459034110866356953)
                ·
                  refine ⟨7216363094275583149767715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9621817459034110866356953 7216363094275583149767715)
                  ·
                    refine ⟨10824544641413374724651573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7216363094275583149767715 10824544641413374724651573)
                    ·
                      refine ⟨1014801060132503880436085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10824544641413374724651573 1014801060132503880436085)
                      ·
                        rfl

theorem cell23_1976318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1976318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976318 prefixEnd_1976318 := by exact prefixLift 1976318
  have htrace : WordTrace (prefixWord ++ tailWord_1976318) baseStart_1976318 baseEnd_1976318 := by
    simpa [prefixWord, tailWord_1976318, baseEnd_1976318] using wordTrace_append hprefix tailTrace_1976318
  have hstable : (prefixWord ++ tailWord_1976318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976318).length < 2 ^ (prefixWord ++ tailWord_1976318).sum := by decide
  have hdescent : baseEnd_1976318 < baseStart_1976318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976351 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 2, 5]
def baseStart_1976351 : Nat := 118140960795 + 1976351 * 2 ^ 59
def prefixEnd_1976351 : Nat := 4983230072969 + 3 ^ 40 * 1976351 * 2
def baseEnd_1976351 : Nat := 338272668331367417107811

theorem tailTrace_1976351 : CollatzResearch.WordTrace tailWord_1976351 prefixEnd_1976351 338272668331367417107811 := by
  unfold tailWord_1976351
  simp only [CollatzResearch.WordTrace]
  refine ⟨72083442863025335723464907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48055628575350223815643271 72083442863025335723464907)
  ·
    refine ⟨108125164294538003585197361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72083442863025335723464907 108125164294538003585197361)
    ·
      refine ⟨81093873220903502688898021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108125164294538003585197361 81093873220903502688898021)
      ·
        refine ⟨15205101228919406754168379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81093873220903502688898021 15205101228919406754168379)
        ·
          refine ⟨22807651843379110131252569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15205101228919406754168379 22807651843379110131252569)
          ·
            refine ⟨17105738882534332598439427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22807651843379110131252569 17105738882534332598439427)
            ·
              refine ⟨25658608323801498897659141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17105738882534332598439427 25658608323801498897659141)
              ·
                refine ⟨4810989060712781043311089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25658608323801498897659141 4810989060712781043311089)
                ·
                  refine ⟨3608241795534585782483317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4810989060712781043311089 3608241795534585782483317)
                  ·
                    refine ⟨338272668331367417107811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3608241795534585782483317 338272668331367417107811)
                    ·
                      rfl

theorem cell23_1976351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_1976351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976351 prefixEnd_1976351 := by exact prefixLift 1976351
  have htrace : WordTrace (prefixWord ++ tailWord_1976351) baseStart_1976351 baseEnd_1976351 := by
    simpa [prefixWord, tailWord_1976351, baseEnd_1976351] using wordTrace_append hprefix tailTrace_1976351
  have hstable : (prefixWord ++ tailWord_1976351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976351).length < 2 ^ (prefixWord ++ tailWord_1976351).sum := by decide
  have hdescent : baseEnd_1976351 < baseStart_1976351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976371 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 4]
def baseStart_1976371 : Nat := 118140960795 + 1976371 * 2 ^ 59
def prefixEnd_1976371 : Nat := 4983230072969 + 3 ^ 40 * 1976371 * 2
def baseEnd_1976371 : Nat := 1014828274607192173073341

theorem tailTrace_1976371 : CollatzResearch.WordTrace tailWord_1976371 prefixEnd_1976371 1014828274607192173073341 := by
  unfold tailWord_1976371
  simp only [CollatzResearch.WordTrace]
  refine ⟨72084172322952879139192967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48056114881968586092795311 72084172322952879139192967)
  ·
    refine ⟨108126258484429318708789451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72084172322952879139192967 108126258484429318708789451)
    ·
      refine ⟨162189387726643978063184177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108126258484429318708789451 162189387726643978063184177)
      ·
        refine ⟨121642040794982983547388133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162189387726643978063184177 121642040794982983547388133)
        ·
          refine ⟨22807882649059309415135275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121642040794982983547388133 22807882649059309415135275)
          ·
            refine ⟨34211823973588964122702913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22807882649059309415135275 34211823973588964122702913)
            ·
              refine ⟨25658867980191723092027185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34211823973588964122702913 25658867980191723092027185)
              ·
                refine ⟨19244150985143792319020389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25658867980191723092027185 19244150985143792319020389)
                ·
                  refine ⟨3608278309714461059816323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19244150985143792319020389 3608278309714461059816323)
                  ·
                    refine ⟨5412417464571691589724485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3608278309714461059816323 5412417464571691589724485)
                    ·
                      refine ⟨1014828274607192173073341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5412417464571691589724485 1014828274607192173073341)
                      ·
                        rfl

theorem cell23_1976371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_1976371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976371 prefixEnd_1976371 := by exact prefixLift 1976371
  have htrace : WordTrace (prefixWord ++ tailWord_1976371) baseStart_1976371 baseEnd_1976371 := by
    simpa [prefixWord, tailWord_1976371, baseEnd_1976371] using wordTrace_append hprefix tailTrace_1976371
  have hstable : (prefixWord ++ tailWord_1976371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976371).length < 2 ^ (prefixWord ++ tailWord_1976371).sum := by decide
  have hdescent : baseEnd_1976371 < baseStart_1976371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976385 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1976385 : Nat := 118140960795 + 1976385 * 2 ^ 59
def prefixEnd_1976385 : Nat := 4983230072969 + 3 ^ 40 * 1976385 * 2
def baseEnd_1976385 : Nat := 338278487778785039432759

theorem tailTrace_1976385 : CollatzResearch.WordTrace tailWord_1976385 prefixEnd_1976385 338278487778785039432759 := by
  unfold tailWord_1976385
  simp only [CollatzResearch.WordTrace]
  refine ⟨72084682944902159530202609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48056455296601439686801739 72084682944902159530202609)
  ·
    refine ⟨54063512208676619647651957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72084682944902159530202609 54063512208676619647651957)
    ·
      refine ⟨5068454269563433091967371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54063512208676619647651957 5068454269563433091967371)
      ·
        refine ⟨7602681404345149637951057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068454269563433091967371 7602681404345149637951057)
        ·
          refine ⟨5702011053258862228463293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7602681404345149637951057 5702011053258862228463293)
          ·
            refine ⟨2138254144972073335673735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5702011053258862228463293 2138254144972073335673735)
            ·
              refine ⟨3207381217458110003510603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138254144972073335673735 3207381217458110003510603)
              ·
                refine ⟨4811071826187165005265905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207381217458110003510603 4811071826187165005265905)
                ·
                  refine ⟨3608303869640373753949429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811071826187165005265905 3608303869640373753949429)
                  ·
                    refine ⟨338278487778785039432759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3608303869640373753949429 338278487778785039432759)
                    ·
                      rfl

theorem cell23_1976385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1976385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976385 prefixEnd_1976385 := by exact prefixLift 1976385
  have htrace : WordTrace (prefixWord ++ tailWord_1976385) baseStart_1976385 baseEnd_1976385 := by
    simpa [prefixWord, tailWord_1976385, baseEnd_1976385] using wordTrace_append hprefix tailTrace_1976385
  have hstable : (prefixWord ++ tailWord_1976385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976385).length < 2 ^ (prefixWord ++ tailWord_1976385).sum := by decide
  have hdescent : baseEnd_1976385 < baseStart_1976385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976449 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 1, 4]
def baseStart_1976449 : Nat := 118140960795 + 1976449 * 2 ^ 59
def prefixEnd_1976449 : Nat := 4983230072969 + 3 ^ 40 * 1976449 * 2
def baseEnd_1976449 : Nat := 338289442032747622632661

theorem tailTrace_1976449 : CollatzResearch.WordTrace tailWord_1976449 prefixEnd_1976449 338289442032747622632661 := by
  unfold tailWord_1976449
  simp only [CollatzResearch.WordTrace]
  refine ⟨72087017216670298460532401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48058011477780198973688267 72087017216670298460532401)
  ·
    refine ⟨54065262912502723845399301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72087017216670298460532401 54065262912502723845399301)
    ·
      refine ⟨10137236796094260721012369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54065262912502723845399301 10137236796094260721012369)
      ·
        refine ⟨7602927597070695540759277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10137236796094260721012369 7602927597070695540759277)
        ·
          refine ⟨2851097848901510827784729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7602927597070695540759277 2851097848901510827784729)
          ·
            refine ⟨2138323386676133120838547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2851097848901510827784729 2138323386676133120838547)
            ·
              refine ⟨3207485080014199681257821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138323386676133120838547 3207485080014199681257821)
              ·
                refine ⟨1202806905005324880471683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3207485080014199681257821 1202806905005324880471683)
                ·
                  refine ⟨1804210357507987320707525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202806905005324880471683 1804210357507987320707525)
                  ·
                    refine ⟨338289442032747622632661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804210357507987320707525 338289442032747622632661)
                    ·
                      rfl

theorem cell23_1976449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_1976449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976449 prefixEnd_1976449 := by exact prefixLift 1976449
  have htrace : WordTrace (prefixWord ++ tailWord_1976449) baseStart_1976449 baseEnd_1976449 := by
    simpa [prefixWord, tailWord_1976449, baseEnd_1976449] using wordTrace_append hprefix tailTrace_1976449
  have hstable : (prefixWord ++ tailWord_1976449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976449).length < 2 ^ (prefixWord ++ tailWord_1976449).sum := by decide
  have hdescent : baseEnd_1976449 < baseStart_1976449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976495 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 5, 2, 2]
def baseStart_1976495 : Nat := 118140960795 + 1976495 * 2 ^ 59
def prefixEnd_1976495 : Nat := 4983230072969 + 3 ^ 40 * 1976495 * 2
def baseEnd_1976495 : Nat := 1014891946208349687922771

theorem tailTrace_1976495 : CollatzResearch.WordTrace tailWord_1976495 prefixEnd_1976495 1014891946208349687922771 := by
  unfold tailWord_1976495
  simp only [CollatzResearch.WordTrace]
  refine ⟨72088694974503648316706939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48059129983002432211137959 72088694974503648316706939)
  ·
    refine ⟨108133042461755472475060409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72088694974503648316706939 108133042461755472475060409)
    ·
      refine ⟨81099781846316604356295307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108133042461755472475060409 81099781846316604356295307)
      ·
        refine ⟨121649672769474906534442961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81099781846316604356295307 121649672769474906534442961)
        ·
          refine ⟨91237254577106179900832221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121649672769474906534442961 91237254577106179900832221)
          ·
            refine ⟨34213970466414817462812083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91237254577106179900832221 34213970466414817462812083)
            ·
              refine ⟨51320955699622226194218125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34213970466414817462812083 51320955699622226194218125)
              ·
                refine ⟨19245358387358334822831797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51320955699622226194218125 19245358387358334822831797)
                ·
                  refine ⟨1804252348814843889640481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19245358387358334822831797 1804252348814843889640481)
                  ·
                    refine ⟨1353189261611132917230361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1804252348814843889640481 1353189261611132917230361)
                    ·
                      refine ⟨1014891946208349687922771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353189261611132917230361 1014891946208349687922771)
                      ·
                        rfl

theorem cell23_1976495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 2, 2].length) (baseStart_1976495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976495 prefixEnd_1976495 := by exact prefixLift 1976495
  have htrace : WordTrace (prefixWord ++ tailWord_1976495) baseStart_1976495 baseEnd_1976495 := by
    simpa [prefixWord, tailWord_1976495, baseEnd_1976495] using wordTrace_append hprefix tailTrace_1976495
  have hstable : (prefixWord ++ tailWord_1976495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976495).length < 2 ^ (prefixWord ++ tailWord_1976495).sum := by decide
  have hdescent : baseEnd_1976495 < baseStart_1976495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976512 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 1, 1, 4]
def baseStart_1976512 : Nat := 118140960795 + 1976512 * 2 ^ 59
def prefixEnd_1976512 : Nat := 4983230072969 + 3 ^ 40 * 1976512 * 2
def baseEnd_1976512 : Nat := 1014900675379476121410193

theorem tailTrace_1976512 : CollatzResearch.WordTrace tailWord_1976512 prefixEnd_1976512 1014900675379476121410193 := by
  unfold tailWord_1976512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044657507721030110037895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48059543343628040146717193 36044657507721030110037895)
  ·
    refine ⟨54066986261581545165056843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36044657507721030110037895 54066986261581545165056843)
    ·
      refine ⟨81100479392372317747585265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54066986261581545165056843 81100479392372317747585265)
      ·
        refine ⟨60825359544279238310688949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81100479392372317747585265 60825359544279238310688949)
        ·
          refine ⟨5702377457276178591627089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60825359544279238310688949 5702377457276178591627089)
          ·
            refine ⟨4276783092957133943720317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702377457276178591627089 4276783092957133943720317)
            ·
              refine ⟨1603793659858925228895119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4276783092957133943720317 1603793659858925228895119)
              ·
                refine ⟨2405690489788387843342679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603793659858925228895119 2405690489788387843342679)
                ·
                  refine ⟨3608535734682581765014019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405690489788387843342679 3608535734682581765014019)
                  ·
                    refine ⟨5412803602023872647521029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3608535734682581765014019 5412803602023872647521029)
                    ·
                      refine ⟨1014900675379476121410193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5412803602023872647521029 1014900675379476121410193)
                      ·
                        rfl

theorem cell23_1976512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_1976512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976512 prefixEnd_1976512 := by exact prefixLift 1976512
  have htrace : WordTrace (prefixWord ++ tailWord_1976512) baseStart_1976512 baseEnd_1976512 := by
    simpa [prefixWord, tailWord_1976512, baseEnd_1976512] using wordTrace_append hprefix tailTrace_1976512
  have hstable : (prefixWord ++ tailWord_1976512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976512).length < 2 ^ (prefixWord ++ tailWord_1976512).sum := by decide
  have hdescent : baseEnd_1976512 < baseStart_1976512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_1976521 : Nat := 118140960795 + 1976521 * 2 ^ 59
def prefixEnd_1976521 : Nat := 4983230072969 + 3 ^ 40 * 1976521 * 2
def baseEnd_1976521 : Nat := 1014905296705366586197651

theorem tailTrace_1976521 : CollatzResearch.WordTrace tailWord_1976521 prefixEnd_1976521 1014905296705366586197651 := by
  unfold tailWord_1976521
  simp only [CollatzResearch.WordTrace]
  refine ⟨72089643272409454757153417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48059762181606303171435611 72089643272409454757153417)
  ·
    refine ⟨54067232454307091067865063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72089643272409454757153417 54067232454307091067865063)
    ·
      refine ⟨81100848681460636601797595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54067232454307091067865063 81100848681460636601797595)
      ·
        refine ⟨121651273022190954902696393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81100848681460636601797595 121651273022190954902696393)
        ·
          refine ⟨91238454766643216177022295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121651273022190954902696393 91238454766643216177022295)
          ·
            refine ⟨136857682149964824265533443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91238454766643216177022295 136857682149964824265533443)
            ·
              refine ⟨205286523224947236398300165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136857682149964824265533443 205286523224947236398300165)
              ·
                refine ⟨38491223104677606824681281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205286523224947236398300165 38491223104677606824681281)
                ·
                  refine ⟨28868417328508205118510961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38491223104677606824681281 28868417328508205118510961)
                  ·
                    refine ⟨21651312996381153838883221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28868417328508205118510961 21651312996381153838883221)
                    ·
                      refine ⟨1014905296705366586197651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21651312996381153838883221 1014905296705366586197651)
                      ·
                        rfl

theorem cell23_1976521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_1976521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976521 prefixEnd_1976521 := by exact prefixLift 1976521
  have htrace : WordTrace (prefixWord ++ tailWord_1976521) baseStart_1976521 baseEnd_1976521 := by
    simpa [prefixWord, tailWord_1976521, baseEnd_1976521] using wordTrace_append hprefix tailTrace_1976521
  have hstable : (prefixWord ++ tailWord_1976521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976521).length < 2 ^ (prefixWord ++ tailWord_1976521).sum := by decide
  have hdescent : baseEnd_1976521 < baseStart_1976521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976545 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1976545 : Nat := 118140960795 + 1976545 * 2 ^ 59
def prefixEnd_1976545 : Nat := 4983230072969 + 3 ^ 40 * 1976545 * 2
def baseEnd_1976545 : Nat := 1014917620241074492297541

theorem tailTrace_1976545 : CollatzResearch.WordTrace tailWord_1976545 prefixEnd_1976545 1014917620241074492297541 := by
  unfold tailWord_1976545
  simp only [CollatzResearch.WordTrace]
  refine ⟨72090518624322506856027089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48060345749548337904018059 72090518624322506856027089)
  ·
    refine ⟨54067888968241880142020317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72090518624322506856027089 54067888968241880142020317)
    ·
      refine ⟨20275458363090705053257619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54067888968241880142020317 20275458363090705053257619)
      ·
        refine ⟨30413187544636057579886429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20275458363090705053257619 30413187544636057579886429)
        ·
          refine ⟨11404945329238521592457411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30413187544636057579886429 11404945329238521592457411)
          ·
            refine ⟨17107417993857782388686117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11404945329238521592457411 17107417993857782388686117)
            ·
              refine ⟨3207640873848334197878647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17107417993857782388686117 3207640873848334197878647)
              ·
                refine ⟨4811461310772501296817971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207640873848334197878647 4811461310772501296817971)
                ·
                  refine ⟨7217191966158751945226957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811461310772501296817971 7217191966158751945226957)
                  ·
                    refine ⟨2706446987309531979460109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7217191966158751945226957 2706446987309531979460109)
                    ·
                      refine ⟨1014917620241074492297541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2706446987309531979460109 1014917620241074492297541)
                      ·
                        rfl

theorem cell23_1976545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1976545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976545 prefixEnd_1976545 := by exact prefixLift 1976545
  have htrace : WordTrace (prefixWord ++ tailWord_1976545) baseStart_1976545 baseEnd_1976545 := by
    simpa [prefixWord, tailWord_1976545, baseEnd_1976545] using wordTrace_append hprefix tailTrace_1976545
  have hstable : (prefixWord ++ tailWord_1976545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976545).length < 2 ^ (prefixWord ++ tailWord_1976545).sum := by decide
  have hdescent : baseEnd_1976545 < baseStart_1976545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976555 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 3, 3, 2]
def baseStart_1976555 : Nat := 118140960795 + 1976555 * 2 ^ 59
def prefixEnd_1976555 : Nat := 4983230072969 + 3 ^ 40 * 1976555 * 2
def baseEnd_1976555 : Nat := 1014922755047619453172495

theorem tailTrace_1976555 : CollatzResearch.WordTrace tailWord_1976555 prefixEnd_1976555 1014922755047619453172495 := by
  unfold tailWord_1976555
  simp only [CollatzResearch.WordTrace]
  refine ⟨72090883354286278563891119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48060588902857519042594079 72090883354286278563891119)
  ·
    refine ⟨108136325031429417845836679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72090883354286278563891119 108136325031429417845836679)
    ·
      refine ⟨162204487547144126768755019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108136325031429417845836679 162204487547144126768755019)
      ·
        refine ⟨243306731320716190153132529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162204487547144126768755019 243306731320716190153132529)
        ·
          refine ⟨182480048490537142614849397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243306731320716190153132529 182480048490537142614849397)
          ·
            refine ⟨17107504545987857120142131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182480048490537142614849397 17107504545987857120142131)
            ·
              refine ⟨25661256818981785680213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17107504545987857120142131 25661256818981785680213197)
              ·
                refine ⟨9622971307118169630079949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25661256818981785680213197 9622971307118169630079949)
                ·
                  refine ⟨3608614240169313611279981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9622971307118169630079949 3608614240169313611279981)
                  ·
                    refine ⟨1353230340063492604229993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608614240169313611279981 1353230340063492604229993)
                    ·
                      refine ⟨1014922755047619453172495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353230340063492604229993 1014922755047619453172495)
                      ·
                        rfl

theorem cell23_1976555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3, 2].length) (baseStart_1976555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976555 prefixEnd_1976555 := by exact prefixLift 1976555
  have htrace : WordTrace (prefixWord ++ tailWord_1976555) baseStart_1976555 baseEnd_1976555 := by
    simpa [prefixWord, tailWord_1976555, baseEnd_1976555] using wordTrace_append hprefix tailTrace_1976555
  have hstable : (prefixWord ++ tailWord_1976555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976555).length < 2 ^ (prefixWord ++ tailWord_1976555).sum := by decide
  have hdescent : baseEnd_1976555 < baseStart_1976555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976558 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1976558 : Nat := 118140960795 + 1976558 * 2 ^ 59
def prefixEnd_1976558 : Nat := 4983230072969 + 3 ^ 40 * 1976558 * 2
def baseEnd_1976558 : Nat := 1014924295489582941434981

theorem tailTrace_1976558 : CollatzResearch.WordTrace tailWord_1976558 prefixEnd_1976558 1014924295489582941434981 := by
  unfold tailWord_1976558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9011374096659426259531291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48060661848850273384166885 9011374096659426259531291)
  ·
    refine ⟨13517061144989139389296937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9011374096659426259531291 13517061144989139389296937)
    ·
      refine ⟨10137795858741854541972703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13517061144989139389296937 10137795858741854541972703)
      ·
        refine ⟨15206693788112781812959055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10137795858741854541972703 15206693788112781812959055)
        ·
          refine ⟨22810040682169172719438583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206693788112781812959055 22810040682169172719438583)
          ·
            refine ⟨34215061023253759079157875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22810040682169172719438583 34215061023253759079157875)
            ·
              refine ⟨51322591534880638618736813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34215061023253759079157875 51322591534880638618736813)
              ·
                refine ⟨19245971825580239482026305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51322591534880638618736813 19245971825580239482026305)
                ·
                  refine ⟨14434478869185179611519729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19245971825580239482026305 14434478869185179611519729)
                  ·
                    refine ⟨10825859151888884708639797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14434478869185179611519729 10825859151888884708639797)
                    ·
                      refine ⟨1014924295489582941434981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10825859151888884708639797 1014924295489582941434981)
                      ·
                        rfl

theorem cell23_1976558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1976558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976558 prefixEnd_1976558 := by exact prefixLift 1976558
  have htrace : WordTrace (prefixWord ++ tailWord_1976558) baseStart_1976558 baseEnd_1976558 := by
    simpa [prefixWord, tailWord_1976558, baseEnd_1976558] using wordTrace_append hprefix tailTrace_1976558
  have hstable : (prefixWord ++ tailWord_1976558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976558).length < 2 ^ (prefixWord ++ tailWord_1976558).sum := by decide
  have hdescent : baseEnd_1976558 < baseStart_1976558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976606 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_1976606 : Nat := 118140960795 + 1976606 * 2 ^ 59
def prefixEnd_1976606 : Nat := 4983230072969 + 3 ^ 40 * 1976606 * 2
def baseEnd_1976606 : Nat := 1014948942560998753634761

theorem tailTrace_1976606 : CollatzResearch.WordTrace tailWord_1976606 prefixEnd_1976606 1014948942560998753634761 := by
  unfold tailWord_1976606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9011592934637689284249709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48061828984734342849331781 9011592934637689284249709)
  ·
    refine ⟨3379347350489133481593641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9011592934637689284249709 3379347350489133481593641)
    ·
      refine ⟨2534510512866850111195231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3379347350489133481593641 2534510512866850111195231)
      ·
        refine ⟨3801765769300275166792847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2534510512866850111195231 3801765769300275166792847)
        ·
          refine ⟨5702648653950412750189271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801765769300275166792847 5702648653950412750189271)
          ·
            refine ⟨8553972980925619125283907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5702648653950412750189271 8553972980925619125283907)
            ·
              refine ⟨12830959471388428687925861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8553972980925619125283907 12830959471388428687925861)
              ·
                refine ⟨2405804900885330378986099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12830959471388428687925861 2405804900885330378986099)
                ·
                  refine ⟨3608707351327995568479149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2405804900885330378986099 3608707351327995568479149)
                  ·
                    refine ⟨1353265256747998338179681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608707351327995568479149 1353265256747998338179681)
                    ·
                      refine ⟨1014948942560998753634761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353265256747998338179681 1014948942560998753634761)
                      ·
                        rfl

theorem cell23_1976606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_1976606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976606 prefixEnd_1976606 := by exact prefixLift 1976606
  have htrace : WordTrace (prefixWord ++ tailWord_1976606) baseStart_1976606 baseEnd_1976606 := by
    simpa [prefixWord, tailWord_1976606, baseEnd_1976606] using wordTrace_append hprefix tailTrace_1976606
  have hstable : (prefixWord ++ tailWord_1976606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976606).length < 2 ^ (prefixWord ++ tailWord_1976606).sum := by decide
  have hdescent : baseEnd_1976606 < baseStart_1976606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976648 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1976648 : Nat := 118140960795 + 1976648 * 2 ^ 59
def prefixEnd_1976648 : Nat := 4983230072969 + 3 ^ 40 * 1976648 * 2
def baseEnd_1976648 : Nat := 1014970508748487589309567

theorem tailTrace_1976648 : CollatzResearch.WordTrace tailWord_1976648 prefixEnd_1976648 1014970508748487589309567 := by
  unfold tailWord_1976648
  simp only [CollatzResearch.WordTrace]
  refine ⟨36047137671474677723513299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48062850228632903631351065 36047137671474677723513299)
  ·
    refine ⟨54070706507212016585269949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36047137671474677723513299 54070706507212016585269949)
    ·
      refine ⟨20276514940204506219476231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54070706507212016585269949 20276514940204506219476231)
      ·
        refine ⟨30414772410306759329214347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20276514940204506219476231 30414772410306759329214347)
        ·
          refine ⟨45622158615460138993821521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30414772410306759329214347 45622158615460138993821521)
          ·
            refine ⟨34216618961595104245366141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45622158615460138993821521 34216618961595104245366141)
            ·
              refine ⟨12831232110598164092012303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34216618961595104245366141 12831232110598164092012303)
              ·
                refine ⟨19246848165897246138018455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12831232110598164092012303 19246848165897246138018455)
                ·
                  refine ⟨28870272248845869207027683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19246848165897246138018455 28870272248845869207027683)
                  ·
                    refine ⟨43305408373268803810541525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28870272248845869207027683 43305408373268803810541525)
                    ·
                      refine ⟨1014970508748487589309567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43305408373268803810541525 1014970508748487589309567)
                      ·
                        rfl

theorem cell23_1976648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1976648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976648 prefixEnd_1976648 := by exact prefixLift 1976648
  have htrace : WordTrace (prefixWord ++ tailWord_1976648) baseStart_1976648 baseEnd_1976648 := by
    simpa [prefixWord, tailWord_1976648, baseEnd_1976648] using wordTrace_append hprefix tailTrace_1976648
  have hstable : (prefixWord ++ tailWord_1976648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976648).length < 2 ^ (prefixWord ++ tailWord_1976648).sum := by decide
  have hdescent : baseEnd_1976648 < baseStart_1976648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976670 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1976670 : Nat := 118140960795 + 1976670 * 2 ^ 59
def prefixEnd_1976670 : Nat := 4983230072969 + 3 ^ 40 * 1976670 * 2
def baseEnd_1976670 : Nat := 1014981805322886503234467

theorem tailTrace_1976670 : CollatzResearch.WordTrace tailWord_1976670 prefixEnd_1976670 1014981805322886503234467 := by
  unfold tailWord_1976670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9011884718608706650540933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48063385165913102136218309 9011884718608706650540933)
  ·
    refine ⟨1689728384739132496976425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9011884718608706650540933 1689728384739132496976425)
    ·
      refine ⟨1267296288554349372732319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689728384739132496976425 1267296288554349372732319)
      ·
        refine ⟨1900944432831524059098479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267296288554349372732319 1900944432831524059098479)
        ·
          refine ⟨2851416649247286088647719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900944432831524059098479 2851416649247286088647719)
          ·
            refine ⟨4277124973870929132971579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851416649247286088647719 4277124973870929132971579)
            ·
              refine ⟨6415687460806393699457369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277124973870929132971579 6415687460806393699457369)
              ·
                refine ⟨4811765595604795274593027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6415687460806393699457369 4811765595604795274593027)
                ·
                  refine ⟨7217648393407192911889541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4811765595604795274593027 7217648393407192911889541)
                  ·
                    refine ⟨1353309073763848670979289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7217648393407192911889541 1353309073763848670979289)
                    ·
                      refine ⟨1014981805322886503234467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353309073763848670979289 1014981805322886503234467)
                      ·
                        rfl

theorem cell23_1976670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1976670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976670 prefixEnd_1976670 := by exact prefixLift 1976670
  have htrace : WordTrace (prefixWord ++ tailWord_1976670) baseStart_1976670 baseEnd_1976670 := by
    simpa [prefixWord, tailWord_1976670, baseEnd_1976670] using wordTrace_append hprefix tailTrace_1976670
  have hstable : (prefixWord ++ tailWord_1976670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976670).length < 2 ^ (prefixWord ++ tailWord_1976670).sum := by decide
  have hdescent : baseEnd_1976670 < baseStart_1976670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976672 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 2, 5]
def baseStart_1976672 : Nat := 118140960795 + 1976672 * 2 ^ 59
def prefixEnd_1976672 : Nat := 4983230072969 + 3 ^ 40 * 1976672 * 2
def baseEnd_1976672 : Nat := 338327610761398498469819

theorem tailTrace_1976672 : CollatzResearch.WordTrace tailWord_1976672 prefixEnd_1976672 338327610761398498469819 := by
  unfold tailWord_1976672
  simp only [CollatzResearch.WordTrace]
  refine ⟨36047575347431203772950135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48063433796574938363933513 36047575347431203772950135)
  ·
    refine ⟨54071363021146805659425203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36047575347431203772950135 54071363021146805659425203)
    ·
      refine ⟨81107044531720208489137805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54071363021146805659425203 81107044531720208489137805)
      ·
        refine ⟨30415141699395078183426677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81107044531720208489137805 30415141699395078183426677)
        ·
          refine ⟨2851419534318288579696251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30415141699395078183426677 2851419534318288579696251)
          ·
            refine ⟨4277129301477432869544377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851419534318288579696251 4277129301477432869544377)
            ·
              refine ⟨3207846976108074652158283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277129301477432869544377 3207846976108074652158283)
              ·
                refine ⟨4811770464162111978237425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207846976108074652158283 4811770464162111978237425)
                ·
                  refine ⟨3608827848121583983678069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4811770464162111978237425 3608827848121583983678069)
                  ·
                    refine ⟨338327610761398498469819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3608827848121583983678069 338327610761398498469819)
                    ·
                      rfl

theorem cell23_1976672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_1976672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976672 prefixEnd_1976672 := by exact prefixLift 1976672
  have htrace : WordTrace (prefixWord ++ tailWord_1976672) baseStart_1976672 baseEnd_1976672 := by
    simpa [prefixWord, tailWord_1976672, baseEnd_1976672] using wordTrace_append hprefix tailTrace_1976672
  have hstable : (prefixWord ++ tailWord_1976672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976672).length < 2 ^ (prefixWord ++ tailWord_1976672).sum := by decide
  have hdescent : baseEnd_1976672 < baseStart_1976672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976695 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_1976695 : Nat := 118140960795 + 1976695 * 2 ^ 59
def prefixEnd_1976695 : Nat := 4983230072969 + 3 ^ 40 * 1976695 * 2
def baseEnd_1976695 : Nat := 1014994642339248905421851

theorem tailTrace_1976695 : CollatzResearch.WordTrace tailWord_1976695 prefixEnd_1976695 1014994642339248905421851 := by
  unfold tailWord_1976695
  simp only [CollatzResearch.WordTrace]
  refine ⟨72095989573779082473987539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48063993049186054982658359 72095989573779082473987539)
  ·
    refine ⟨108143984360668623710981309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72095989573779082473987539 108143984360668623710981309)
    ·
      refine ⟨40553994135250733891617991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108143984360668623710981309 40553994135250733891617991)
      ·
        refine ⟨60830991202876100837426987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40553994135250733891617991 60830991202876100837426987)
        ·
          refine ⟨91246486804314151256140481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60830991202876100837426987 91246486804314151256140481)
          ·
            refine ⟨68434865103235613442105361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91246486804314151256140481 68434865103235613442105361)
            ·
              refine ⟨51326148827426710081579021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68434865103235613442105361 51326148827426710081579021)
              ·
                refine ⟨19247305810285016280592133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51326148827426710081579021 19247305810285016280592133)
                ·
                  refine ⟨3608869839428440552611025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19247305810285016280592133 3608869839428440552611025)
                  ·
                    refine ⟨2706652379571330414458269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3608869839428440552611025 2706652379571330414458269)
                    ·
                      refine ⟨1014994642339248905421851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2706652379571330414458269 1014994642339248905421851)
                      ·
                        rfl

theorem cell23_1976695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_1976695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976695 prefixEnd_1976695 := by exact prefixLift 1976695
  have htrace : WordTrace (prefixWord ++ tailWord_1976695) baseStart_1976695 baseEnd_1976695 := by
    simpa [prefixWord, tailWord_1976695, baseEnd_1976695] using wordTrace_append hprefix tailTrace_1976695
  have hstable : (prefixWord ++ tailWord_1976695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976695).length < 2 ^ (prefixWord ++ tailWord_1976695).sum := by decide
  have hdescent : baseEnd_1976695 < baseStart_1976695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976715 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 6]
def baseStart_1976715 : Nat := 118140960795 + 1976715 * 2 ^ 59
def prefixEnd_1976715 : Nat := 4983230072969 + 3 ^ 40 * 1976715 * 2
def baseEnd_1976715 : Nat := 112778323550259869685751

theorem tailTrace_1976715 : CollatzResearch.WordTrace tailWord_1976715 prefixEnd_1976715 112778323550259869685751 := by
  unfold tailWord_1976715
  simp only [CollatzResearch.WordTrace]
  refine ⟨72096719033706625889715599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48064479355804417259810399 72096719033706625889715599)
  ·
    refine ⟨108145078550559938834573399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72096719033706625889715599 108145078550559938834573399)
    ·
      refine ⟨162217617825839908251860099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108145078550559938834573399 162217617825839908251860099)
      ·
        refine ⟨243326426738759862377790149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162217617825839908251860099 243326426738759862377790149)
        ·
          refine ⟨45623705013517474195835653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243326426738759862377790149 45623705013517474195835653)
          ·
            refine ⟨8554444690034526411719185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45623705013517474195835653 8554444690034526411719185)
            ·
              refine ⟨6415833517525894808789389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554444690034526411719185 6415833517525894808789389)
              ·
                refine ⟨2405937569072210553296021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6415833517525894808789389 2405937569072210553296021)
                ·
                  refine ⟨112778323550259869685751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2405937569072210553296021 112778323550259869685751)
                  ·
                    rfl

theorem cell23_1976715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 6].length) (baseStart_1976715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976715 prefixEnd_1976715 := by exact prefixLift 1976715
  have htrace : WordTrace (prefixWord ++ tailWord_1976715) baseStart_1976715 baseEnd_1976715 := by
    simpa [prefixWord, tailWord_1976715, baseEnd_1976715] using wordTrace_append hprefix tailTrace_1976715
  have hstable : (prefixWord ++ tailWord_1976715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976715).length < 2 ^ (prefixWord ++ tailWord_1976715).sum := by decide
  have hdescent : baseEnd_1976715 < baseStart_1976715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976759 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_1976759 : Nat := 118140960795 + 1976759 * 2 ^ 59
def prefixEnd_1976759 : Nat := 4983230072969 + 3 ^ 40 * 1976759 * 2
def baseEnd_1976759 : Nat := 1015027505101136655021557

theorem tailTrace_1976759 : CollatzResearch.WordTrace tailWord_1976759 prefixEnd_1976759 1015027505101136655021557 := by
  unfold tailWord_1976759
  simp only [CollatzResearch.WordTrace]
  refine ⟨72098323845547221404317331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48065549230364814269544887 72098323845547221404317331)
  ·
    refine ⟨108147485768320832106475997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72098323845547221404317331 108147485768320832106475997)
    ·
      refine ⟨40555307163120312039928499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108147485768320832106475997 40555307163120312039928499)
      ·
        refine ⟨60832960744680468059892749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40555307163120312039928499 60832960744680468059892749)
        ·
          refine ⟨22812360279255175522459781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60832960744680468059892749 22812360279255175522459781)
          ·
            refine ⟨4277317552360345410461209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22812360279255175522459781 4277317552360345410461209)
            ·
              refine ⟨3207988164270259057845907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277317552360345410461209 3207988164270259057845907)
              ·
                refine ⟨4811982246405388586768861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3207988164270259057845907 4811982246405388586768861)
                ·
                  refine ⟨1804493342402020720038323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4811982246405388586768861 1804493342402020720038323)
                  ·
                    refine ⟨2706740013603031080057485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1804493342402020720038323 2706740013603031080057485)
                    ·
                      refine ⟨1015027505101136655021557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2706740013603031080057485 1015027505101136655021557)
                      ·
                        rfl

theorem cell23_1976759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_1976759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976759 prefixEnd_1976759 := by exact prefixLift 1976759
  have htrace : WordTrace (prefixWord ++ tailWord_1976759) baseStart_1976759 baseEnd_1976759 := by
    simpa [prefixWord, tailWord_1976759, baseEnd_1976759] using wordTrace_append hprefix tailTrace_1976759
  have hstable : (prefixWord ++ tailWord_1976759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976759).length < 2 ^ (prefixWord ++ tailWord_1976759).sum := by decide
  have hdescent : baseEnd_1976759 < baseStart_1976759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976782 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2]
def baseStart_1976782 : Nat := 118140960795 + 1976782 * 2 ^ 59
def prefixEnd_1976782 : Nat := 4983230072969 + 3 ^ 40 * 1976782 * 2
def baseEnd_1976782 : Nat := 1015039315156190065033951

theorem tailTrace_1976782 : CollatzResearch.WordTrace tailWord_1976782 prefixEnd_1976782 1015039315156190065033951 := by
  unfold tailWord_1976782
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012395340557987041550575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48066108482975930888269733 9012395340557987041550575)
  ·
    refine ⟨13518593010836980562325863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9012395340557987041550575 13518593010836980562325863)
    ·
      refine ⟨20277889516255470843488795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13518593010836980562325863 20277889516255470843488795)
      ·
        refine ⟨30416834274383206265233193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20277889516255470843488795 30416834274383206265233193)
        ·
          refine ⟨22812625705787404698924895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30416834274383206265233193 22812625705787404698924895)
          ·
            refine ⟨34218938558681107048387343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22812625705787404698924895 34218938558681107048387343)
            ·
              refine ⟨51328407838021660572581015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34218938558681107048387343 51328407838021660572581015)
              ·
                refine ⟨76992611757032490858871523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51328407838021660572581015 76992611757032490858871523)
                ·
                  refine ⟨115488917635548736288307285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76992611757032490858871523 115488917635548736288307285)
                  ·
                    refine ⟨1353385753541586753378601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115488917635548736288307285 1353385753541586753378601)
                    ·
                      refine ⟨1015039315156190065033951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353385753541586753378601 1015039315156190065033951)
                      ·
                        rfl

theorem cell23_1976782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_1976782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976782 prefixEnd_1976782 := by exact prefixLift 1976782
  have htrace : WordTrace (prefixWord ++ tailWord_1976782) baseStart_1976782 baseEnd_1976782 := by
    simpa [prefixWord, tailWord_1976782, baseEnd_1976782] using wordTrace_append hprefix tailTrace_1976782
  have hstable : (prefixWord ++ tailWord_1976782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976782).length < 2 ^ (prefixWord ++ tailWord_1976782).sum := by decide
  have hdescent : baseEnd_1976782 < baseStart_1976782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976785 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_1976785 : Nat := 118140960795 + 1976785 * 2 ^ 59
def prefixEnd_1976785 : Nat := 4983230072969 + 3 ^ 40 * 1976785 * 2
def baseEnd_1976785 : Nat := 1015040855598153553296437

theorem tailTrace_1976785 : CollatzResearch.WordTrace tailWord_1976785 prefixEnd_1976785 1015040855598153553296437 := by
  unfold tailWord_1976785
  simp only [CollatzResearch.WordTrace]
  refine ⟨72099272143453027844763809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48066181428968685229842539 72099272143453027844763809)
  ·
    refine ⟨54074454107589770883572857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72099272143453027844763809 54074454107589770883572857)
    ·
      refine ⟨40555840580692328162679643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54074454107589770883572857 40555840580692328162679643)
      ·
        refine ⟨60833760871038492244019465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40555840580692328162679643 60833760871038492244019465)
        ·
          refine ⟨45625320653278869183014599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60833760871038492244019465 45625320653278869183014599)
          ·
            refine ⟨68437980979918303774521899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45625320653278869183014599 68437980979918303774521899)
            ·
              refine ⟨102656971469877455661782849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68437980979918303774521899 102656971469877455661782849)
              ·
                refine ⟨76992728602408091746337137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102656971469877455661782849 76992728602408091746337137)
                ·
                  refine ⟨57744546451806068809752853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76992728602408091746337137 57744546451806068809752853)
                  ·
                    refine ⟨2706775614928409475457165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57744546451806068809752853 2706775614928409475457165)
                    ·
                      refine ⟨1015040855598153553296437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2706775614928409475457165 1015040855598153553296437)
                      ·
                        rfl

theorem cell23_1976785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_1976785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976785 prefixEnd_1976785 := by exact prefixLift 1976785
  have htrace : WordTrace (prefixWord ++ tailWord_1976785) baseStart_1976785 baseEnd_1976785 := by
    simpa [prefixWord, tailWord_1976785, baseEnd_1976785] using wordTrace_append hprefix tailTrace_1976785
  have hstable : (prefixWord ++ tailWord_1976785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976785).length < 2 ^ (prefixWord ++ tailWord_1976785).sum := by decide
  have hdescent : baseEnd_1976785 < baseStart_1976785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976822 : List Nat := [5, 1, 1, 1, 2, 1, 4, 8]
def baseStart_1976822 : Nat := 118140960795 + 1976822 * 2 ^ 59
def prefixEnd_1976822 : Nat := 4983230072969 + 3 ^ 40 * 1976822 * 2
def baseEnd_1976822 : Nat := 37594809421569255871621

theorem tailTrace_1976822 : CollatzResearch.WordTrace tailWord_1976822 prefixEnd_1976822 37594809421569255871621 := by
  unfold tailWord_1976822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506288852769936447741295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48067081096212655442573813 4506288852769936447741295)
  ·
    refine ⟨6759433279154904671611943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4506288852769936447741295 6759433279154904671611943)
    ·
      refine ⟨10139149918732357007417915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759433279154904671611943 10139149918732357007417915)
      ·
        refine ⟨15208724878098535511126873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139149918732357007417915 15208724878098535511126873)
        ·
          refine ⟨11406543658573901633345155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15208724878098535511126873 11406543658573901633345155)
          ·
            refine ⟨17109815487860852450017733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11406543658573901633345155 17109815487860852450017733)
            ·
              refine ⟨3208090403973909834378325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17109815487860852450017733 3208090403973909834378325)
              ·
                refine ⟨37594809421569255871621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3208090403973909834378325 37594809421569255871621)
                ·
                  rfl

theorem cell23_1976822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_1976822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976822 prefixEnd_1976822 := by exact prefixLift 1976822
  have htrace : WordTrace (prefixWord ++ tailWord_1976822) baseStart_1976822 baseEnd_1976822 := by
    simpa [prefixWord, tailWord_1976822, baseEnd_1976822] using wordTrace_append hprefix tailTrace_1976822
  have hstable : (prefixWord ++ tailWord_1976822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976822).length < 2 ^ (prefixWord ++ tailWord_1976822).sum := by decide
  have hdescent : baseEnd_1976822 < baseStart_1976822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976836 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1976836 : Nat := 118140960795 + 1976836 * 2 ^ 59
def prefixEnd_1976836 : Nat := 4983230072969 + 3 ^ 40 * 1976836 * 2
def baseEnd_1976836 : Nat := 1015067043111532853758703

theorem tailTrace_1976836 : CollatzResearch.WordTrace tailWord_1976836 prefixEnd_1976836 1015067043111532853758703 := by
  unfold tailWord_1976836
  simp only [CollatzResearch.WordTrace]
  refine ⟨36050566133134131777435181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48067421510845509036580241 36050566133134131777435181)
  ·
    refine ⟨13518962299925299416538193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36050566133134131777435181 13518962299925299416538193)
    ·
      refine ⟨10139221724943974562403645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13518962299925299416538193 10139221724943974562403645)
      ·
        refine ⟨3802208146853990460901367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10139221724943974562403645 3802208146853990460901367)
        ·
          refine ⟨5703312220280985691352051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802208146853990460901367 5703312220280985691352051)
          ·
            refine ⟨8554968330421478537028077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703312220280985691352051 8554968330421478537028077)
            ·
              refine ⟨3208113123908054451385529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8554968330421478537028077 3208113123908054451385529)
              ·
                refine ⟨2406084842931040838539147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208113123908054451385529 2406084842931040838539147)
                ·
                  refine ⟨3609127264396561257808721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406084842931040838539147 3609127264396561257808721)
                  ·
                    refine ⟨2706845448297420943356541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3609127264396561257808721 2706845448297420943356541)
                    ·
                      refine ⟨1015067043111532853758703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2706845448297420943356541 1015067043111532853758703)
                      ·
                        rfl

theorem cell23_1976836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1976836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976836 prefixEnd_1976836 := by exact prefixLift 1976836
  have htrace : WordTrace (prefixWord ++ tailWord_1976836) baseStart_1976836 baseEnd_1976836 := by
    simpa [prefixWord, tailWord_1976836, baseEnd_1976836] using wordTrace_append hprefix tailTrace_1976836
  have hstable : (prefixWord ++ tailWord_1976836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976836).length < 2 ^ (prefixWord ++ tailWord_1976836).sum := by decide
  have hdescent : baseEnd_1976836 < baseStart_1976836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976875 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_1976875 : Nat := 118140960795 + 1976875 * 2 ^ 59
def prefixEnd_1976875 : Nat := 4983230072969 + 3 ^ 40 * 1976875 * 2
def baseEnd_1976875 : Nat := 1015087068857058201171023

theorem tailTrace_1976875 : CollatzResearch.WordTrace tailWord_1976875 prefixEnd_1976875 1015087068857058201171023 := by
  unfold tailWord_1976875
  simp only [CollatzResearch.WordTrace]
  refine ⟨72102554713126973215540079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48068369808751315477026719 72102554713126973215540079)
  ·
    refine ⟨108153832069690459823310119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72102554713126973215540079 108153832069690459823310119)
    ·
      refine ⟨162230748104535689734965179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108153832069690459823310119 162230748104535689734965179)
      ·
        refine ⟨243346122156803534602447769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162230748104535689734965179 243346122156803534602447769)
        ·
          refine ⟨182509591617602650951835827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243346122156803534602447769 182509591617602650951835827)
          ·
            refine ⟨273764387426403976427753741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182509591617602650951835827 273764387426403976427753741)
            ·
              refine ⟨102661645284901491160407653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 273764387426403976427753741 102661645284901491160407653)
              ·
                refine ⟨19249058490919029592576435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102661645284901491160407653 19249058490919029592576435)
                ·
                  refine ⟨28873587736378544388864653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19249058490919029592576435 28873587736378544388864653)
                  ·
                    refine ⟨10827595401141954145824245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28873587736378544388864653 10827595401141954145824245)
                    ·
                      refine ⟨1015087068857058201171023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10827595401141954145824245 1015087068857058201171023)
                      ·
                        rfl

theorem cell23_1976875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_1976875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976875 prefixEnd_1976875 := by exact prefixLift 1976875
  have htrace : WordTrace (prefixWord ++ tailWord_1976875) baseStart_1976875 baseEnd_1976875 := by
    simpa [prefixWord, tailWord_1976875, baseEnd_1976875] using wordTrace_append hprefix tailTrace_1976875
  have hstable : (prefixWord ++ tailWord_1976875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976875).length < 2 ^ (prefixWord ++ tailWord_1976875).sum := by decide
  have hdescent : baseEnd_1976875 < baseStart_1976875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976905 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_1976905 : Nat := 118140960795 + 1976905 * 2 ^ 59
def prefixEnd_1976905 : Nat := 4983230072969 + 3 ^ 40 * 1976905 * 2
def baseEnd_1976905 : Nat := 1015102473276693083795885

theorem tailTrace_1976905 : CollatzResearch.WordTrace tailWord_1976905 prefixEnd_1976905 1015102473276693083795885 := by
  unfold tailWord_1976905
  simp only [CollatzResearch.WordTrace]
  refine ⟨72103648903018288339132169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48069099268678858892754779 72103648903018288339132169)
  ·
    refine ⟨54077736677263716254349127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72103648903018288339132169 54077736677263716254349127)
    ·
      refine ⟨81116605015895574381523691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54077736677263716254349127 81116605015895574381523691)
      ·
        refine ⟨121674907523843361572285537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81116605015895574381523691 121674907523843361572285537)
        ·
          refine ⟨91256180642882521179214153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121674907523843361572285537 91256180642882521179214153)
          ·
            refine ⟨68442135482161890884410615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91256180642882521179214153 68442135482161890884410615)
            ·
              refine ⟨102663203223242836326615923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68442135482161890884410615 102663203223242836326615923)
              ·
                refine ⟨153994804834864254489923885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102663203223242836326615923 153994804834864254489923885)
                ·
                  refine ⟨57748051813074095433721457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153994804834864254489923885 57748051813074095433721457)
                  ·
                    refine ⟨43311038859805571575291093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57748051813074095433721457 43311038859805571575291093)
                    ·
                      refine ⟨1015102473276693083795885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43311038859805571575291093 1015102473276693083795885)
                      ·
                        rfl

theorem cell23_1976905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_1976905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976905 prefixEnd_1976905 := by exact prefixLift 1976905
  have htrace : WordTrace (prefixWord ++ tailWord_1976905) baseStart_1976905 baseEnd_1976905 := by
    simpa [prefixWord, tailWord_1976905, baseEnd_1976905] using wordTrace_append hprefix tailTrace_1976905
  have hstable : (prefixWord ++ tailWord_1976905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976905).length < 2 ^ (prefixWord ++ tailWord_1976905).sum := by decide
  have hdescent : baseEnd_1976905 < baseStart_1976905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976915 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_1976915 : Nat := 118140960795 + 1976915 * 2 ^ 59
def prefixEnd_1976915 : Nat := 4983230072969 + 3 ^ 40 * 1976915 * 2
def baseEnd_1976915 : Nat := 1015107608083238044670839

theorem tailTrace_1976915 : CollatzResearch.WordTrace tailWord_1976915 prefixEnd_1976915 1015107608083238044670839 := by
  unfold tailWord_1976915
  simp only [CollatzResearch.WordTrace]
  refine ⟨72104013632982060046996199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48069342421988040031330799 72104013632982060046996199)
  ·
    refine ⟨108156020449473090070494299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72104013632982060046996199 108156020449473090070494299)
    ·
      refine ⟨162234030674209635105741449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108156020449473090070494299 162234030674209635105741449)
      ·
        refine ⟨121675523005657226329306087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162234030674209635105741449 121675523005657226329306087)
        ·
          refine ⟨182513284508485839493959131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121675523005657226329306087 182513284508485839493959131)
          ·
            refine ⟨273769926762728759240938697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182513284508485839493959131 273769926762728759240938697)
            ·
              refine ⟨205327445072046569430704023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273769926762728759240938697 205327445072046569430704023)
              ·
                refine ⟨307991167608069854146056035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205327445072046569430704023 307991167608069854146056035)
                ·
                  refine ⟨461986751412104781219084053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307991167608069854146056035 461986751412104781219084053)
                  ·
                    refine ⟨21655628972442411619644565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 461986751412104781219084053 21655628972442411619644565)
                    ·
                      refine ⟨1015107608083238044670839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21655628972442411619644565 1015107608083238044670839)
                      ·
                        rfl

theorem cell23_1976915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_1976915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976915 prefixEnd_1976915 := by exact prefixLift 1976915
  have htrace : WordTrace (prefixWord ++ tailWord_1976915) baseStart_1976915 baseEnd_1976915 := by
    simpa [prefixWord, tailWord_1976915, baseEnd_1976915] using wordTrace_append hprefix tailTrace_1976915
  have hstable : (prefixWord ++ tailWord_1976915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976915).length < 2 ^ (prefixWord ++ tailWord_1976915).sum := by decide
  have hdescent : baseEnd_1976915 < baseStart_1976915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976929 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 5]
def baseStart_1976929 : Nat := 118140960795 + 1976929 * 2 ^ 59
def prefixEnd_1976929 : Nat := 4983230072969 + 3 ^ 40 * 1976929 * 2
def baseEnd_1976929 : Nat := 112790532979155665543975

theorem tailTrace_1976929 : CollatzResearch.WordTrace tailWord_1976929 prefixEnd_1976929 112790532979155665543975 := by
  unfold tailWord_1976929
  simp only [CollatzResearch.WordTrace]
  refine ⟨72104524254931340438005841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48069682836620893625337227 72104524254931340438005841)
  ·
    refine ⟨54078393191198505328504381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72104524254931340438005841 54078393191198505328504381)
    ·
      refine ⟨20279397446699439498189143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54078393191198505328504381 20279397446699439498189143)
      ·
        refine ⟨30419096170049159247283715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20279397446699439498189143 30419096170049159247283715)
        ·
          refine ⟨45628644255073738870925573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30419096170049159247283715 45628644255073738870925573)
          ·
            refine ⟨8555370797826326038298545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45628644255073738870925573 8555370797826326038298545)
            ·
              refine ⟨6416528098369744528723909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8555370797826326038298545 6416528098369744528723909)
              ·
                refine ⟨1203099018444327099135733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6416528098369744528723909 1203099018444327099135733)
                ·
                  refine ⟨112790532979155665543975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203099018444327099135733 112790532979155665543975)
                  ·
                    rfl

theorem cell23_1976929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 5].length) (baseStart_1976929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976929 prefixEnd_1976929 := by exact prefixLift 1976929
  have htrace : WordTrace (prefixWord ++ tailWord_1976929) baseStart_1976929 baseEnd_1976929 := by
    simpa [prefixWord, tailWord_1976929, baseEnd_1976929] using wordTrace_append hprefix tailTrace_1976929
  have hstable : (prefixWord ++ tailWord_1976929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976929).length < 2 ^ (prefixWord ++ tailWord_1976929).sum := by decide
  have hdescent : baseEnd_1976929 < baseStart_1976929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1976986 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1976986 : Nat := 118140960795 + 1976986 * 2 ^ 59
def prefixEnd_1976986 : Nat := 4983230072969 + 3 ^ 40 * 1976986 * 2
def baseEnd_1976986 : Nat := 1015144065209707266883013

theorem tailTrace_1976986 : CollatzResearch.WordTrace tailWord_1976986 prefixEnd_1976986 1015144065209707266883013 := by
  unfold tailWord_1976986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18026650803931209793207703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48071068810483226115220541 18026650803931209793207703)
  ·
    refine ⟨27039976205896814689811555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18026650803931209793207703 27039976205896814689811555)
    ·
      refine ⟨40559964308845222034717333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27039976205896814689811555 40559964308845222034717333)
      ·
        refine ⟨1901248326977119782877375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40559964308845222034717333 1901248326977119782877375)
        ·
          refine ⟨2851872490465679674316063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901248326977119782877375 2851872490465679674316063)
          ·
            refine ⟨4277808735698519511474095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851872490465679674316063 4277808735698519511474095)
            ·
              refine ⟨6416713103547779267211143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277808735698519511474095 6416713103547779267211143)
              ·
                refine ⟨9625069655321668900816715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6416713103547779267211143 9625069655321668900816715)
                ·
                  refine ⟨14437604482982503351225073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9625069655321668900816715 14437604482982503351225073)
                  ·
                    refine ⟨10828203362236877513418805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14437604482982503351225073 10828203362236877513418805)
                    ·
                      refine ⟨1015144065209707266883013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10828203362236877513418805 1015144065209707266883013)
                      ·
                        rfl

theorem cell23_1976986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1976986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1976986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1976986 prefixEnd_1976986 := by exact prefixLift 1976986
  have htrace : WordTrace (prefixWord ++ tailWord_1976986) baseStart_1976986 baseEnd_1976986 := by
    simpa [prefixWord, tailWord_1976986, baseEnd_1976986] using wordTrace_append hprefix tailTrace_1976986
  have hstable : (prefixWord ++ tailWord_1976986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1976986).length < 2 ^ (prefixWord ++ tailWord_1976986).sum := by decide
  have hdescent : baseEnd_1976986 < baseStart_1976986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1976986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977036 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 6]
def baseStart_1977036 : Nat := 118140960795 + 1977036 * 2 ^ 59
def prefixEnd_1977036 : Nat := 4983230072969 + 3 ^ 40 * 1977036 * 2
def baseEnd_1977036 : Nat := 112796637693603563473087

theorem tailTrace_1977036 : CollatzResearch.WordTrace tailWord_1977036 prefixEnd_1977036 112796637693603563473087 := by
  unfold tailWord_1977036
  simp only [CollatzResearch.WordTrace]
  refine ⟨36054213432771848856075481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48072284577029131808100641 36054213432771848856075481)
  ·
    refine ⟨27040660074578886642056611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36054213432771848856075481 27040660074578886642056611)
    ·
      refine ⟨40560990111868329963084917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27040660074578886642056611 40560990111868329963084917)
      ·
        refine ⟨3802592822987655934039211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40560990111868329963084917 3802592822987655934039211)
        ·
          refine ⟨5703889234481483901058817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802592822987655934039211 5703889234481483901058817)
          ·
            refine ⟨4277916925861112925794113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5703889234481483901058817 4277916925861112925794113)
            ·
              refine ⟨3208437694395834694345585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277916925861112925794113 3208437694395834694345585)
              ·
                refine ⟨2406328270796876020759189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208437694395834694345585 2406328270796876020759189)
                ·
                  refine ⟨112796637693603563473087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2406328270796876020759189 112796637693603563473087)
                  ·
                    rfl

theorem cell23_1977036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_1977036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977036 prefixEnd_1977036 := by exact prefixLift 1977036
  have htrace : WordTrace (prefixWord ++ tailWord_1977036) baseStart_1977036 baseEnd_1977036 := by
    simpa [prefixWord, tailWord_1977036, baseEnd_1977036] using wordTrace_append hprefix tailTrace_1977036
  have hstable : (prefixWord ++ tailWord_1977036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977036).length < 2 ^ (prefixWord ++ tailWord_1977036).sum := by decide
  have hdescent : baseEnd_1977036 < baseStart_1977036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977039 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 5, 5, 2]
def baseStart_1977039 : Nat := 118140960795 + 1977039 * 2 ^ 59
def prefixEnd_1977039 : Nat := 4983230072969 + 3 ^ 40 * 1977039 * 2
def baseEnd_1977039 : Nat := 1015171279684395559520269

theorem tailTrace_1977039 : CollatzResearch.WordTrace tailWord_1977039 prefixEnd_1977039 1015171279684395559520269 := by
  unfold tailWord_1977039
  simp only [CollatzResearch.WordTrace]
  refine ⟨72108536284532829224510171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48072357523021886149673447 72108536284532829224510171)
  ·
    refine ⟨108162804426799243836765257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72108536284532829224510171 108162804426799243836765257)
    ·
      refine ⟨81122103320099432877573943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108162804426799243836765257 81122103320099432877573943)
      ·
        refine ⟨121683154980149149316360915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81122103320099432877573943 121683154980149149316360915)
        ·
          refine ⟨182524732470223723974541373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121683154980149149316360915 182524732470223723974541373)
          ·
            refine ⟨68446774676333896490453015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182524732470223723974541373 68446774676333896490453015)
            ·
              refine ⟨102670162014500844735679523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68446774676333896490453015 102670162014500844735679523)
              ·
                refine ⟨154005243021751267103519285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102670162014500844735679523 154005243021751267103519285)
                ·
                  refine ⟨14437991533289181290954933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154005243021751267103519285 14437991533289181290954933)
                  ·
                    refine ⟨1353561706245860746027025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14437991533289181290954933 1353561706245860746027025)
                    ·
                      refine ⟨1015171279684395559520269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353561706245860746027025 1015171279684395559520269)
                      ·
                        rfl

theorem cell23_1977039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5, 2].length) (baseStart_1977039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977039 prefixEnd_1977039 := by exact prefixLift 1977039
  have htrace : WordTrace (prefixWord ++ tailWord_1977039) baseStart_1977039 baseEnd_1977039 := by
    simpa [prefixWord, tailWord_1977039, baseEnd_1977039] using wordTrace_append hprefix tailTrace_1977039
  have hstable : (prefixWord ++ tailWord_1977039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977039).length < 2 ^ (prefixWord ++ tailWord_1977039).sum := by decide
  have hdescent : baseEnd_1977039 < baseStart_1977039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977079 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 4, 4]
def baseStart_1977079 : Nat := 118140960795 + 1977079 * 2 ^ 59
def prefixEnd_1977079 : Nat := 4983230072969 + 3 ^ 40 * 1977079 * 2
def baseEnd_1977079 : Nat := 338397272970191801006695

theorem tailTrace_1977079 : CollatzResearch.WordTrace tailWord_1977079 prefixEnd_1977079 338397272970191801006695 := by
  unfold tailWord_1977079
  simp only [CollatzResearch.WordTrace]
  refine ⟨72109995204387916055966291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48073330136258610703977527 72109995204387916055966291)
  ·
    refine ⟨108164992806581874083949437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72109995204387916055966291 108164992806581874083949437)
    ·
      refine ⟨40561872302468202781481039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108164992806581874083949437 40561872302468202781481039)
      ·
        refine ⟨60842808453702304172221559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40561872302468202781481039 60842808453702304172221559)
        ·
          refine ⟨91264212680553456258332339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60842808453702304172221559 91264212680553456258332339)
          ·
            refine ⟨136896319020830184387498509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91264212680553456258332339 136896319020830184387498509)
            ·
              refine ⟨51336119632811319145311941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136896319020830184387498509 51336119632811319145311941)
              ·
                refine ⟨9625522431152122339745989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51336119632811319145311941 9625522431152122339745989)
                ·
                  refine ⟨1804785455841022938702373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9625522431152122339745989 1804785455841022938702373)
                  ·
                    refine ⟨338397272970191801006695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804785455841022938702373 338397272970191801006695)
                    ·
                      rfl

theorem cell23_1977079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_1977079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977079 prefixEnd_1977079 := by exact prefixLift 1977079
  have htrace : WordTrace (prefixWord ++ tailWord_1977079) baseStart_1977079 baseEnd_1977079 := by
    simpa [prefixWord, tailWord_1977079, baseEnd_1977079] using wordTrace_append hprefix tailTrace_1977079
  have hstable : (prefixWord ++ tailWord_1977079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977079).length < 2 ^ (prefixWord ++ tailWord_1977079).sum := by decide
  have hdescent : baseEnd_1977079 < baseStart_1977079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977089 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1977089 : Nat := 118140960795 + 1977089 * 2 ^ 59
def prefixEnd_1977089 : Nat := 4983230072969 + 3 ^ 40 * 1977089 * 2
def baseEnd_1977089 : Nat := 1015196953717120363895039

theorem tailTrace_1977089 : CollatzResearch.WordTrace tailWord_1977089 prefixEnd_1977089 1015196953717120363895039 := by
  unfold tailWord_1977089
  simp only [CollatzResearch.WordTrace]
  refine ⟨72110359934351687763830321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48073573289567791842553547 72110359934351687763830321)
  ·
    refine ⟨54082769950763765822872741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72110359934351687763830321 54082769950763765822872741)
    ·
      refine ⟨10140519365768206091788639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54082769950763765822872741 10140519365768206091788639)
      ·
        refine ⟨15210779048652309137682959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10140519365768206091788639 15210779048652309137682959)
        ·
          refine ⟨22816168572978463706524439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15210779048652309137682959 22816168572978463706524439)
          ·
            refine ⟨34224252859467695559786659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22816168572978463706524439 34224252859467695559786659)
            ·
              refine ⟨51336379289201543339679989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34224252859467695559786659 51336379289201543339679989)
              ·
                refine ⟨4812785558362644688094999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51336379289201543339679989 4812785558362644688094999)
                ·
                  refine ⟨7219178337543967032142499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812785558362644688094999 7219178337543967032142499)
                  ·
                    refine ⟨10828767506315950548213749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7219178337543967032142499 10828767506315950548213749)
                    ·
                      refine ⟨1015196953717120363895039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10828767506315950548213749 1015196953717120363895039)
                      ·
                        rfl

theorem cell23_1977089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1977089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977089 prefixEnd_1977089 := by exact prefixLift 1977089
  have htrace : WordTrace (prefixWord ++ tailWord_1977089) baseStart_1977089 baseEnd_1977089 := by
    simpa [prefixWord, tailWord_1977089, baseEnd_1977089] using wordTrace_append hprefix tailTrace_1977089
  have hstable : (prefixWord ++ tailWord_1977089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977089).length < 2 ^ (prefixWord ++ tailWord_1977089).sum := by decide
  have hdescent : baseEnd_1977089 < baseStart_1977089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977096 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 4, 4]
def baseStart_1977096 : Nat := 118140960795 + 1977096 * 2 ^ 59
def prefixEnd_1977096 : Nat := 4983230072969 + 3 ^ 40 * 1977096 * 2
def baseEnd_1977096 : Nat := 338400182693900612169169

theorem tailTrace_1977096 : CollatzResearch.WordTrace tailWord_1977096 prefixEnd_1977096 338400182693900612169169 := by
  unfold tailWord_1977096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055307622663163979667571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48073743496884218639556761 36055307622663163979667571)
  ·
    refine ⟨54082961433994745969501357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36055307622663163979667571 54082961433994745969501357)
    ·
      refine ⟨20281110537748029738563009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54082961433994745969501357 20281110537748029738563009)
      ·
        refine ⟨15210832903311022303922257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20281110537748029738563009 15210832903311022303922257)
        ·
          refine ⟨11408124677483266727941693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15210832903311022303922257 11408124677483266727941693)
          ·
            refine ⟨4278046754056225022978135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11408124677483266727941693 4278046754056225022978135)
            ·
              refine ⟨6417070131084337534467203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278046754056225022978135 6417070131084337534467203)
              ·
                refine ⟨9625605196626506301700805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417070131084337534467203 9625605196626506301700805)
                ·
                  refine ⟨1804800974367469931568901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9625605196626506301700805 1804800974367469931568901)
                  ·
                    refine ⟨338400182693900612169169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804800974367469931568901 338400182693900612169169)
                    ·
                      rfl

theorem cell23_1977096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_1977096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977096 prefixEnd_1977096 := by exact prefixLift 1977096
  have htrace : WordTrace (prefixWord ++ tailWord_1977096) baseStart_1977096 baseEnd_1977096 := by
    simpa [prefixWord, tailWord_1977096, baseEnd_1977096] using wordTrace_append hprefix tailTrace_1977096
  have hstable : (prefixWord ++ tailWord_1977096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977096).length < 2 ^ (prefixWord ++ tailWord_1977096).sum := by decide
  have hdescent : baseEnd_1977096 < baseStart_1977096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977103 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 3, 2, 2]
def baseStart_1977103 : Nat := 118140960795 + 1977103 * 2 ^ 59
def prefixEnd_1977103 : Nat := 4983230072969 + 3 ^ 40 * 1977103 * 2
def baseEnd_1977103 : Nat := 1015204142446283309119975

theorem tailTrace_1977103 : CollatzResearch.WordTrace tailWord_1977103 prefixEnd_1977103 1015204142446283309119975 := by
  unfold tailWord_1977103
  simp only [CollatzResearch.WordTrace]
  refine ⟨72110870556300968154839963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48073913704200645436559975 72110870556300968154839963)
  ·
    refine ⟨108166305834451452232259945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72110870556300968154839963 108166305834451452232259945)
    ·
      refine ⟨81124729375838589174194959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108166305834451452232259945 81124729375838589174194959)
      ·
        refine ⟨121687094063757883761292439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81124729375838589174194959 121687094063757883761292439)
        ·
          refine ⟨182530641095636825641938659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121687094063757883761292439 182530641095636825641938659)
          ·
            refine ⟨273795961643455238462907989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182530641095636825641938659 273795961643455238462907989)
            ·
              refine ⟨3208546425509241075737203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 273795961643455238462907989 3208546425509241075737203)
              ·
                refine ⟨4812819638263861613605805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208546425509241075737203 4812819638263861613605805)
                ·
                  refine ⟨1804807364348948105102177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4812819638263861613605805 1804807364348948105102177)
                  ·
                    refine ⟨1353605523261711078826633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1804807364348948105102177 1353605523261711078826633)
                    ·
                      refine ⟨1015204142446283309119975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353605523261711078826633 1015204142446283309119975)
                      ·
                        rfl

theorem cell23_1977103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 2, 2].length) (baseStart_1977103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977103 prefixEnd_1977103 := by exact prefixLift 1977103
  have htrace : WordTrace (prefixWord ++ tailWord_1977103) baseStart_1977103 baseEnd_1977103 := by
    simpa [prefixWord, tailWord_1977103, baseEnd_1977103] using wordTrace_append hprefix tailTrace_1977103
  have hstable : (prefixWord ++ tailWord_1977103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977103).length < 2 ^ (prefixWord ++ tailWord_1977103).sum := by decide
  have hdescent : baseEnd_1977103 < baseStart_1977103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977116 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1977116 : Nat := 118140960795 + 1977116 * 2 ^ 59
def prefixEnd_1977116 : Nat := 4983230072969 + 3 ^ 40 * 1977116 * 2
def baseEnd_1977116 : Nat := 1015210817694791758257415

theorem tailTrace_1977116 : CollatzResearch.WordTrace tailWord_1977116 prefixEnd_1977116 1015210817694791758257415 := by
  unfold tailWord_1977116
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055672352626935687531601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48074229803502580916708801 36055672352626935687531601)
  ·
    refine ⟨27041754264470201765648701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36055672352626935687531601 27041754264470201765648701)
    ·
      refine ⟨10140657849176325662118263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27041754264470201765648701 10140657849176325662118263)
      ·
        refine ⟨15210986773764488493177395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10140657849176325662118263 15210986773764488493177395)
        ·
          refine ⟨22816480160646732739766093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15210986773764488493177395 22816480160646732739766093)
          ·
            refine ⟨8556180060242524777412285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22816480160646732739766093 8556180060242524777412285)
            ·
              refine ⟨3208567522590946791529607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8556180060242524777412285 3208567522590946791529607)
              ·
                refine ⟨4812851283886420187294411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208567522590946791529607 4812851283886420187294411)
                ·
                  refine ⟨7219276925829630280941617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4812851283886420187294411 7219276925829630280941617)
                  ·
                    refine ⟨5414457694372222710706213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7219276925829630280941617 5414457694372222710706213)
                    ·
                      refine ⟨1015210817694791758257415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5414457694372222710706213 1015210817694791758257415)
                      ·
                        rfl

theorem cell23_1977116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1977116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977116 prefixEnd_1977116 := by exact prefixLift 1977116
  have htrace : WordTrace (prefixWord ++ tailWord_1977116) baseStart_1977116 baseEnd_1977116 := by
    simpa [prefixWord, tailWord_1977116, baseEnd_1977116] using wordTrace_append hprefix tailTrace_1977116
  have hstable : (prefixWord ++ tailWord_1977116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977116).length < 2 ^ (prefixWord ++ tailWord_1977116).sum := by decide
  have hdescent : baseEnd_1977116 < baseStart_1977116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977159 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1977159 : Nat := 118140960795 + 1977159 * 2 ^ 59
def prefixEnd_1977159 : Nat := 4983230072969 + 3 ^ 40 * 1977159 * 2
def baseEnd_1977159 : Nat := 1015232897362935090019717

theorem tailTrace_1977159 : CollatzResearch.WordTrace tailWord_1977159 prefixEnd_1977159 1015232897362935090019717 := by
  unfold tailWord_1977159
  simp only [CollatzResearch.WordTrace]
  refine ⟨72112913044098089718878531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48075275362732059812585687 72112913044098089718878531)
  ·
    refine ⟨108169369566147134578317797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72112913044098089718878531 108169369566147134578317797)
    ·
      refine ⟨20281756793652587733434587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108169369566147134578317797 20281756793652587733434587)
      ·
        refine ⟨30422635190478881600151881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20281756793652587733434587 30422635190478881600151881)
        ·
          refine ⟨22816976392859161200113911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30422635190478881600151881 22816976392859161200113911)
          ·
            refine ⟨34225464589288741800170867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22816976392859161200113911 34225464589288741800170867)
            ·
              refine ⟨51338196883933112700256301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34225464589288741800170867 51338196883933112700256301)
              ·
                refine ⟨19251823831474917262596113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51338196883933112700256301 19251823831474917262596113)
                ·
                  refine ⟨14438867873606187946947085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19251823831474917262596113 14438867873606187946947085)
                  ·
                    refine ⟨5414575452602320480105157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14438867873606187946947085 5414575452602320480105157)
                    ·
                      refine ⟨1015232897362935090019717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5414575452602320480105157 1015232897362935090019717)
                      ·
                        rfl

theorem cell23_1977159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1977159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977159 prefixEnd_1977159 := by exact prefixLift 1977159
  have htrace : WordTrace (prefixWord ++ tailWord_1977159) baseStart_1977159 baseEnd_1977159 := by
    simpa [prefixWord, tailWord_1977159, baseEnd_1977159] using wordTrace_append hprefix tailTrace_1977159
  have hstable : (prefixWord ++ tailWord_1977159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977159).length < 2 ^ (prefixWord ++ tailWord_1977159).sum := by decide
  have hdescent : baseEnd_1977159 < baseStart_1977159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977176 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 5, 4, 2]
def baseStart_1977176 : Nat := 118140960795 + 1977176 * 2 ^ 59
def prefixEnd_1977176 : Nat := 4983230072969 + 3 ^ 40 * 1977176 * 2
def baseEnd_1977176 : Nat := 1015241626534061523507139

theorem tailTrace_1977176 : CollatzResearch.WordTrace tailWord_1977176 prefixEnd_1977176 1015241626534061523507139 := by
  unfold tailWord_1977176
  simp only [CollatzResearch.WordTrace]
  refine ⟨36056766542518250811123691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48075688723357667748164921 36056766542518250811123691)
  ·
    refine ⟨54085149813777376216685537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36056766542518250811123691 54085149813777376216685537)
    ·
      refine ⟨40563862360333032162514153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54085149813777376216685537 40563862360333032162514153)
      ·
        refine ⟨30422896770249774121885615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40563862360333032162514153 30422896770249774121885615)
        ·
          refine ⟨45634345155374661182828423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30422896770249774121885615 45634345155374661182828423)
          ·
            refine ⟨68451517733061991774242635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45634345155374661182828423 68451517733061991774242635)
            ·
              refine ⟨102677276599592987661363953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68451517733061991774242635 102677276599592987661363953)
              ·
                refine ⟨77007957449694740746022965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102677276599592987661363953 77007957449694740746022965)
                ·
                  refine ⟨7219496010908881944939653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77007957449694740746022965 7219496010908881944939653)
                  ·
                    refine ⟨1353655502045415364676185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7219496010908881944939653 1353655502045415364676185)
                    ·
                      refine ⟨1015241626534061523507139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353655502045415364676185 1015241626534061523507139)
                      ·
                        rfl

theorem cell23_1977176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_1977176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977176 prefixEnd_1977176 := by exact prefixLift 1977176
  have htrace : WordTrace (prefixWord ++ tailWord_1977176) baseStart_1977176 baseEnd_1977176 := by
    simpa [prefixWord, tailWord_1977176, baseEnd_1977176] using wordTrace_append hprefix tailTrace_1977176
  have hstable : (prefixWord ++ tailWord_1977176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977176).length < 2 ^ (prefixWord ++ tailWord_1977176).sum := by decide
  have hdescent : baseEnd_1977176 < baseStart_1977176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977180 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1977180 : Nat := 118140960795 + 1977180 * 2 ^ 59
def prefixEnd_1977180 : Nat := 4983230072969 + 3 ^ 40 * 1977180 * 2
def baseEnd_1977180 : Nat := 1015243680456679507857121

theorem tailTrace_1977180 : CollatzResearch.WordTrace tailWord_1977180 prefixEnd_1977180 1015243680456679507857121 := by
  unfold tailWord_1977180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36056839488511005152696497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48075785984681340203595329 36056839488511005152696497)
  ·
    refine ⟨27042629616383253864522373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36056839488511005152696497 27042629616383253864522373)
    ·
      refine ⟨5070493053071860099597945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27042629616383253864522373 5070493053071860099597945)
      ·
        refine ⟨3802869789803895074698459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5070493053071860099597945 3802869789803895074698459)
        ·
          refine ⟨5704304684705842612047689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802869789803895074698459 5704304684705842612047689)
          ·
            refine ⟨4278228513529381959035767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704304684705842612047689 4278228513529381959035767)
            ·
              refine ⟨6417342770294072938553651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278228513529381959035767 6417342770294072938553651)
              ·
                refine ⟨9626014155441109407830477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6417342770294072938553651 9626014155441109407830477)
                ·
                  refine ⟨3609755308290416027936429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9626014155441109407830477 3609755308290416027936429)
                  ·
                    refine ⟨1353658240608906010476161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3609755308290416027936429 1353658240608906010476161)
                    ·
                      refine ⟨1015243680456679507857121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353658240608906010476161 1015243680456679507857121)
                      ·
                        rfl

theorem cell23_1977180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1977180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977180 prefixEnd_1977180 := by exact prefixLift 1977180
  have htrace : WordTrace (prefixWord ++ tailWord_1977180) baseStart_1977180 baseEnd_1977180 := by
    simpa [prefixWord, tailWord_1977180, baseEnd_1977180] using wordTrace_append hprefix tailTrace_1977180
  have hstable : (prefixWord ++ tailWord_1977180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977180).length < 2 ^ (prefixWord ++ tailWord_1977180).sum := by decide
  have hdescent : baseEnd_1977180 < baseStart_1977180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977250 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1977250 : Nat := 118140960795 + 1977250 * 2 ^ 59
def prefixEnd_1977250 : Nat := 4983230072969 + 3 ^ 40 * 1977250 * 2
def baseEnd_1977250 : Nat := 112808847122499359331311

theorem tailTrace_1977250 : CollatzResearch.WordTrace tailWord_1977250 prefixEnd_1977250 112808847122499359331311 := by
  unfold tailWord_1977250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029058021692103065110301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48077488057845608173627469 18029058021692103065110301)
  ·
    refine ⟨6760896758134538649416363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18029058021692103065110301 6760896758134538649416363)
    ·
      refine ⟨10141345137201807974124545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6760896758134538649416363 10141345137201807974124545)
      ·
        refine ⟨7606008852901355980593409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10141345137201807974124545 7606008852901355980593409)
        ·
          refine ⟨5704506639676016985445057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606008852901355980593409 5704506639676016985445057)
          ·
            refine ⟨4278379979757012739083793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704506639676016985445057 4278379979757012739083793)
            ·
              refine ⟨3208784984817759554312845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278379979757012739083793 3208784984817759554312845)
              ·
                refine ⟨1203294369306659832867317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208784984817759554312845 1203294369306659832867317)
                ·
                  refine ⟨112808847122499359331311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203294369306659832867317 112808847122499359331311)
                  ·
                    rfl

theorem cell23_1977250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1977250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977250 prefixEnd_1977250 := by exact prefixLift 1977250
  have htrace : WordTrace (prefixWord ++ tailWord_1977250) baseStart_1977250 baseEnd_1977250 := by
    simpa [prefixWord, tailWord_1977250, baseEnd_1977250] using wordTrace_append hprefix tailTrace_1977250
  have hstable : (prefixWord ++ tailWord_1977250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977250).length < 2 ^ (prefixWord ++ tailWord_1977250).sum := by decide
  have hdescent : baseEnd_1977250 < baseStart_1977250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977261 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1977261 : Nat := 118140960795 + 1977261 * 2 ^ 59
def prefixEnd_1977261 : Nat := 4983230072969 + 3 ^ 40 * 1977261 * 2
def baseEnd_1977261 : Nat := 1015285272389693690944249

theorem tailTrace_1977261 : CollatzResearch.WordTrace tailWord_1977261 prefixEnd_1977261 1015285272389693690944249 := by
  unfold tailWord_1977261
  simp only [CollatzResearch.WordTrace]
  refine ⟨72116633289728561139091637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48077755526485707426061091 72116633289728561139091637)
  ·
    refine ⟨6760934370912052606789841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72116633289728561139091637 6760934370912052606789841)
    ·
      refine ⟨5070700778184039455092381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6760934370912052606789841 5070700778184039455092381)
      ·
        refine ⟨1901512791819014795659643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5070700778184039455092381 1901512791819014795659643)
        ·
          refine ⟨2852269187728522193489465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901512791819014795659643 2852269187728522193489465)
          ·
            refine ⟨2139201890796391645117099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852269187728522193489465 2139201890796391645117099)
            ·
              refine ⟨3208802836194587467675649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139201890796391645117099 3208802836194587467675649)
              ·
                refine ⟨2406602127145940600756737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208802836194587467675649 2406602127145940600756737)
                ·
                  refine ⟨1804951595359455450567553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2406602127145940600756737 1804951595359455450567553)
                  ·
                    refine ⟨1353713696519591587925665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1804951595359455450567553 1353713696519591587925665)
                    ·
                      refine ⟨1015285272389693690944249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353713696519591587925665 1015285272389693690944249)
                      ·
                        rfl

theorem cell23_1977261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1977261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977261 prefixEnd_1977261 := by exact prefixLift 1977261
  have htrace : WordTrace (prefixWord ++ tailWord_1977261) baseStart_1977261 baseEnd_1977261 := by
    simpa [prefixWord, tailWord_1977261, baseEnd_1977261] using wordTrace_append hprefix tailTrace_1977261
  have hstable : (prefixWord ++ tailWord_1977261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977261).length < 2 ^ (prefixWord ++ tailWord_1977261).sum := by decide
  have hdescent : baseEnd_1977261 < baseStart_1977261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977289 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 12]
def baseStart_1977289 : Nat := 118140960795 + 1977289 * 2 ^ 59
def prefixEnd_1977289 : Nat := 4983230072969 + 3 ^ 40 * 1977289 * 2
def baseEnd_1977289 : Nat := 112811072205335509043791

theorem tailTrace_1977289 : CollatzResearch.WordTrace tailWord_1977289 prefixEnd_1977289 112811072205335509043791 := by
  unfold tailWord_1977289
  simp only [CollatzResearch.WordTrace]
  refine ⟨72117654533627121921110921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48078436355751414614073947 72117654533627121921110921)
  ·
    refine ⟨54088240900220341440833191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72117654533627121921110921 54088240900220341440833191)
    ·
      refine ⟨81132361350330512161249787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54088240900220341440833191 81132361350330512161249787)
      ·
        refine ⟨121698542025495768241874681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81132361350330512161249787 121698542025495768241874681)
        ·
          refine ⟨91273906519121826181406011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121698542025495768241874681 91273906519121826181406011)
          ·
            refine ⟨136910859778682739272109017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91273906519121826181406011 136910859778682739272109017)
            ·
              refine ⟨102683144834012054454081763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136910859778682739272109017 102683144834012054454081763)
              ·
                refine ⟨154024717251018081681122645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102683144834012054454081763 154024717251018081681122645)
                ·
                  refine ⟨112811072205335509043791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 154024717251018081681122645 112811072205335509043791)
                  ·
                    rfl

theorem cell23_1977289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_1977289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977289 prefixEnd_1977289 := by exact prefixLift 1977289
  have htrace : WordTrace (prefixWord ++ tailWord_1977289) baseStart_1977289 baseEnd_1977289 := by
    simpa [prefixWord, tailWord_1977289, baseEnd_1977289] using wordTrace_append hprefix tailTrace_1977289
  have hstable : (prefixWord ++ tailWord_1977289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977289).length < 2 ^ (prefixWord ++ tailWord_1977289).sum := by decide
  have hdescent : baseEnd_1977289 < baseStart_1977289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977306 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_1977306 : Nat := 118140960795 + 1977306 * 2 ^ 59
def prefixEnd_1977306 : Nat := 4983230072969 + 3 ^ 40 * 1977306 * 2
def baseEnd_1977306 : Nat := 112812042113238446097949

theorem tailTrace_1977306 : CollatzResearch.WordTrace tailWord_1977306 prefixEnd_1977306 112812042113238446097949 := by
  unfold tailWord_1977306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029568643641383456119943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48078849716377022549653181 18029568643641383456119943)
  ·
    refine ⟨27044352965462075184179915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18029568643641383456119943 27044352965462075184179915)
    ·
      refine ⟨40566529448193112776269873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27044352965462075184179915 40566529448193112776269873)
      ·
        refine ⟨30424897086144834582202405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40566529448193112776269873 30424897086144834582202405)
        ·
          refine ⟨5704668203652156484162951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30424897086144834582202405 5704668203652156484162951)
          ·
            refine ⟨8557002305478234726244427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704668203652156484162951 8557002305478234726244427)
            ·
              refine ⟨12835503458217352089366641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8557002305478234726244427 12835503458217352089366641)
              ·
                refine ⟨9626627593663014067024981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12835503458217352089366641 9626627593663014067024981)
                ·
                  refine ⟨112812042113238446097949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9626627593663014067024981 112812042113238446097949)
                  ·
                    rfl

theorem cell23_1977306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_1977306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977306 prefixEnd_1977306 := by exact prefixLift 1977306
  have htrace : WordTrace (prefixWord ++ tailWord_1977306) baseStart_1977306 baseEnd_1977306 := by
    simpa [prefixWord, tailWord_1977306, baseEnd_1977306] using wordTrace_append hprefix tailTrace_1977306
  have hstable : (prefixWord ++ tailWord_1977306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977306).length < 2 ^ (prefixWord ++ tailWord_1977306).sum := by decide
  have hdescent : baseEnd_1977306 < baseStart_1977306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977327 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 1, 4]
def baseStart_1977327 : Nat := 118140960795 + 1977327 * 2 ^ 59
def prefixEnd_1977327 : Nat := 4983230072969 + 3 ^ 40 * 1977327 * 2
def baseEnd_1977327 : Nat := 338439720704296810906315

theorem tailTrace_1977327 : CollatzResearch.WordTrace tailWord_1977327 prefixEnd_1977327 338439720704296810906315 := by
  unfold tailWord_1977327
  simp only [CollatzResearch.WordTrace]
  refine ⟨72119040507489454410994235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48079360338326302940662823 72119040507489454410994235)
  ·
    refine ⟨108178560761234181616491353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72119040507489454410994235 108178560761234181616491353)
    ·
      refine ⟨81133920570925636212368515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108178560761234181616491353 81133920570925636212368515)
      ·
        refine ⟨121700880856388454318552773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81133920570925636212368515 121700880856388454318552773)
        ·
          refine ⟨22818915160572835184728645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121700880856388454318552773 22818915160572835184728645)
          ·
            refine ⟨4278546592607406597136621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22818915160572835184728645 4278546592607406597136621)
            ·
              refine ⟨1604454972227777473926233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4278546592607406597136621 1604454972227777473926233)
              ·
                refine ⟨1203341229170833105444675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604454972227777473926233 1203341229170833105444675)
                ·
                  refine ⟨1805011843756249658167013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203341229170833105444675 1805011843756249658167013)
                  ·
                    refine ⟨338439720704296810906315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805011843756249658167013 338439720704296810906315)
                    ·
                      rfl

theorem cell23_1977327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 4].length) (baseStart_1977327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977327 prefixEnd_1977327 := by exact prefixLift 1977327
  have htrace : WordTrace (prefixWord ++ tailWord_1977327) baseStart_1977327 baseEnd_1977327 := by
    simpa [prefixWord, tailWord_1977327, baseEnd_1977327] using wordTrace_append hprefix tailTrace_1977327
  have hstable : (prefixWord ++ tailWord_1977327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977327).length < 2 ^ (prefixWord ++ tailWord_1977327).sum := by decide
  have hdescent : baseEnd_1977327 < baseStart_1977327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977336 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_1977336 : Nat := 118140960795 + 1977336 * 2 ^ 59
def prefixEnd_1977336 : Nat := 4983230072969 + 3 ^ 40 * 1977336 * 2
def baseEnd_1977336 : Nat := 338441261146260299168801

theorem tailTrace_1977336 : CollatzResearch.WordTrace tailWord_1977336 prefixEnd_1977336 338441261146260299168801 := by
  unfold tailWord_1977336
  simp only [CollatzResearch.WordTrace]
  refine ⟨36059684382228424474035931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48079579176304565965381241 36059684382228424474035931)
  ·
    refine ⟨54089526573342636711053897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36059684382228424474035931 54089526573342636711053897)
    ·
      refine ⟨40567144930006977533290423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54089526573342636711053897 40567144930006977533290423)
      ·
        refine ⟨60850717395010466299935635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40567144930006977533290423 60850717395010466299935635)
        ·
          refine ⟨91276076092515699449903453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60850717395010466299935635 91276076092515699449903453)
          ·
            refine ⟨34228528534693387293713795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91276076092515699449903453 34228528534693387293713795)
            ·
              refine ⟨51342792802040080940570693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34228528534693387293713795 51342792802040080940570693)
              ·
                refine ⟨9626773650382515176357005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51342792802040080940570693 9626773650382515176357005)
                ·
                  refine ⟨3610040118893443191133877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9626773650382515176357005 3610040118893443191133877)
                  ·
                    refine ⟨338441261146260299168801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3610040118893443191133877 338441261146260299168801)
                    ·
                      rfl

theorem cell23_1977336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_1977336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977336 prefixEnd_1977336 := by exact prefixLift 1977336
  have htrace : WordTrace (prefixWord ++ tailWord_1977336) baseStart_1977336 baseEnd_1977336 := by
    simpa [prefixWord, tailWord_1977336, baseEnd_1977336] using wordTrace_append hprefix tailTrace_1977336
  have hstable : (prefixWord ++ tailWord_1977336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977336).length < 2 ^ (prefixWord ++ tailWord_1977336).sum := by decide
  have hdescent : baseEnd_1977336 < baseStart_1977336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977340 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 6]
def baseStart_1977340 : Nat := 118140960795 + 1977340 * 2 ^ 59
def prefixEnd_1977340 : Nat := 4983230072969 + 3 ^ 40 * 1977340 * 2
def baseEnd_1977340 : Nat := 112813981929044320206265

theorem tailTrace_1977340 : CollatzResearch.WordTrace tailWord_1977340 prefixEnd_1977340 112813981929044320206265 := by
  unfold tailWord_1977340
  simp only [CollatzResearch.WordTrace]
  refine ⟨36059757328221178815608737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48079676437628238420811649 36059757328221178815608737)
  ·
    refine ⟨27044817996165884111706553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36059757328221178815608737 27044817996165884111706553)
    ·
      refine ⟨20283613497124413083779915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27044817996165884111706553 20283613497124413083779915)
      ·
        refine ⟨30425420245686619625669873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20283613497124413083779915 30425420245686619625669873)
        ·
          refine ⟨22819065184264964719252405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30425420245686619625669873 22819065184264964719252405)
          ·
            refine ⟨2139287361024840442429913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22819065184264964719252405 2139287361024840442429913)
            ·
              refine ⟨1604465520768630331822435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139287361024840442429913 1604465520768630331822435)
              ·
                refine ⟨2406698281152945497733653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604465520768630331822435 2406698281152945497733653)
                ·
                  refine ⟨112813981929044320206265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2406698281152945497733653 112813981929044320206265)
                  ·
                    rfl

theorem cell23_1977340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_1977340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977340 prefixEnd_1977340 := by exact prefixLift 1977340
  have htrace : WordTrace (prefixWord ++ tailWord_1977340) baseStart_1977340 baseEnd_1977340 := by
    simpa [prefixWord, tailWord_1977340, baseEnd_1977340] using wordTrace_append hprefix tailTrace_1977340
  have hstable : (prefixWord ++ tailWord_1977340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977340).length < 2 ^ (prefixWord ++ tailWord_1977340).sum := by decide
  have hdescent : baseEnd_1977340 < baseStart_1977340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977370 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_1977370 : Nat := 118140960795 + 1977370 * 2 ^ 59
def prefixEnd_1977370 : Nat := 4983230072969 + 3 ^ 40 * 1977370 * 2
def baseEnd_1977370 : Nat := 338447080593677921493749

theorem tailTrace_1977370 : CollatzResearch.WordTrace tailWord_1977370 prefixEnd_1977370 338447080593677921493749 := by
  unfold tailWord_1977370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18030152211583418188702391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48080405897555781836539709 18030152211583418188702391)
  ·
    refine ⟨27045228317375127283053587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18030152211583418188702391 27045228317375127283053587)
    ·
      refine ⟨40567842476062690924580381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27045228317375127283053587 40567842476062690924580381)
      ·
        refine ⟨15212940928523509096717643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40567842476062690924580381 15212940928523509096717643)
        ·
          refine ⟨22819411392785263645076465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15212940928523509096717643 22819411392785263645076465)
          ·
            refine ⟨17114558544588947733807349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22819411392785263645076465 17114558544588947733807349)
            ·
              refine ⟨1604489863555213850044439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17114558544588947733807349 1604489863555213850044439)
              ·
                refine ⟨2406734795332820775066659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604489863555213850044439 2406734795332820775066659)
                ·
                  refine ⟨3610102192999231162599989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2406734795332820775066659 3610102192999231162599989)
                  ·
                    refine ⟨338447080593677921493749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3610102192999231162599989 338447080593677921493749)
                    ·
                      rfl

theorem cell23_1977370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_1977370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977370 prefixEnd_1977370 := by exact prefixLift 1977370
  have htrace : WordTrace (prefixWord ++ tailWord_1977370) baseStart_1977370 baseEnd_1977370 := by
    simpa [prefixWord, tailWord_1977370, baseEnd_1977370] using wordTrace_append hprefix tailTrace_1977370
  have hstable : (prefixWord ++ tailWord_1977370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977370).length < 2 ^ (prefixWord ++ tailWord_1977370).sum := by decide
  have hdescent : baseEnd_1977370 < baseStart_1977370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977393 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1977393 : Nat := 118140960795 + 1977393 * 2 ^ 59
def prefixEnd_1977393 : Nat := 4983230072969 + 3 ^ 40 * 1977393 * 2
def baseEnd_1977393 : Nat := 1015353051836087174493641

theorem tailTrace_1977393 : CollatzResearch.WordTrace tailWord_1977393 prefixEnd_1977393 1015353051836087174493641 := by
  unfold tailWord_1977393
  simp only [CollatzResearch.WordTrace]
  refine ⟨72121447725250347682896833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48080965150166898455264555 72121447725250347682896833)
  ·
    refine ⟨54091085793937760762172625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72121447725250347682896833 54091085793937760762172625)
    ·
      refine ⟨40568314345453320571629469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54091085793937760762172625 40568314345453320571629469)
      ·
        refine ⟨15213117879544995214361051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40568314345453320571629469 15213117879544995214361051)
        ·
          refine ⟨22819676819317492821541577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15213117879544995214361051 22819676819317492821541577)
          ·
            refine ⟨17114757614488119616156183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22819676819317492821541577 17114757614488119616156183)
            ·
              refine ⟨25672136421732179424234275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17114757614488119616156183 25672136421732179424234275)
              ·
                refine ⟨38508204632598269136351413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25672136421732179424234275 38508204632598269136351413)
                ·
                  refine ⟨3610144184306087731532945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38508204632598269136351413 3610144184306087731532945)
                  ·
                    refine ⟨2707608138229565798649709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3610144184306087731532945 2707608138229565798649709)
                    ·
                      refine ⟨1015353051836087174493641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2707608138229565798649709 1015353051836087174493641)
                      ·
                        rfl

theorem cell23_1977393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1977393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977393 prefixEnd_1977393 := by exact prefixLift 1977393
  have htrace : WordTrace (prefixWord ++ tailWord_1977393) baseStart_1977393 baseEnd_1977393 := by
    simpa [prefixWord, tailWord_1977393, baseEnd_1977393] using wordTrace_append hprefix tailTrace_1977393
  have hstable : (prefixWord ++ tailWord_1977393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977393).length < 2 ^ (prefixWord ++ tailWord_1977393).sum := by decide
  have hdescent : baseEnd_1977393 < baseStart_1977393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977400 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 2, 4]
def baseStart_1977400 : Nat := 118140960795 + 1977400 * 2 ^ 59
def prefixEnd_1977400 : Nat := 4983230072969 + 3 ^ 40 * 1977400 * 2
def baseEnd_1977400 : Nat := 338452215400222882368703

theorem tailTrace_1977400 : CollatzResearch.WordTrace tailWord_1977400 prefixEnd_1977400 338452215400222882368703 := by
  unfold tailWord_1977400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060851518112493939200827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48081135357483325252267769 36060851518112493939200827)
  ·
    refine ⟨54091277277168740908801241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36060851518112493939200827 54091277277168740908801241)
    ·
      refine ⟨40568457957876555681600931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54091277277168740908801241 40568457957876555681600931)
      ·
        refine ⟨60852686936814833522401397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40568457957876555681600931 60852686936814833522401397)
        ·
          refine ⟨5704939400326390642725131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60852686936814833522401397 5704939400326390642725131)
          ·
            refine ⟨8557409100489585964087697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704939400326390642725131 8557409100489585964087697)
            ·
              refine ⟨6418056825367189473065773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8557409100489585964087697 6418056825367189473065773)
              ·
                refine ⟨2406771309512696052399665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6418056825367189473065773 2406771309512696052399665)
                ·
                  refine ⟨1805078482134522039299749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2406771309512696052399665 1805078482134522039299749)
                  ·
                    refine ⟨338452215400222882368703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805078482134522039299749 338452215400222882368703)
                    ·
                      rfl

theorem cell23_1977400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_1977400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977400 prefixEnd_1977400 := by exact prefixLift 1977400
  have htrace : WordTrace (prefixWord ++ tailWord_1977400) baseStart_1977400 baseEnd_1977400 := by
    simpa [prefixWord, tailWord_1977400, baseEnd_1977400] using wordTrace_append hprefix tailTrace_1977400
  have hstable : (prefixWord ++ tailWord_1977400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977400).length < 2 ^ (prefixWord ++ tailWord_1977400).sum := by decide
  have hdescent : baseEnd_1977400 < baseStart_1977400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977440 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 4, 1, 3]
def baseStart_1977440 : Nat := 118140960795 + 1977440 * 2 ^ 59
def prefixEnd_1977440 : Nat := 4983230072969 + 3 ^ 40 * 1977440 * 2
def baseEnd_1977440 : Nat := 1015377185426848490605925

theorem tailTrace_1977440 : CollatzResearch.WordTrace tailWord_1977440 prefixEnd_1977440 1015377185426848490605925 := by
  unfold tailWord_1977440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36061580978040037354928887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48082107970720049806571849 36061580978040037354928887)
  ·
    refine ⟨54092371467060056032393331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36061580978040037354928887 54092371467060056032393331)
    ·
      refine ⟨81138557200590084048589997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54092371467060056032393331 81138557200590084048589997)
      ·
        refine ⟨30426958950221281518221249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81138557200590084048589997 30426958950221281518221249)
        ·
          refine ⟨22820219212665961138665937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30426958950221281518221249 22820219212665961138665937)
          ·
            refine ⟨17115164409499470853999453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22820219212665961138665937 17115164409499470853999453)
            ·
              refine ⟨6418186653562301570249795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17115164409499470853999453 6418186653562301570249795)
              ·
                refine ⟨9627279980343452355374693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418186653562301570249795 9627279980343452355374693)
                ·
                  refine ⟨1805114996314397316632755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9627279980343452355374693 1805114996314397316632755)
                  ·
                    refine ⟨2707672494471595974949133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1805114996314397316632755 2707672494471595974949133)
                    ·
                      refine ⟨1015377185426848490605925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2707672494471595974949133 1015377185426848490605925)
                      ·
                        rfl

theorem cell23_1977440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_1977440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977440 prefixEnd_1977440 := by exact prefixLift 1977440
  have htrace : WordTrace (prefixWord ++ tailWord_1977440) baseStart_1977440 baseEnd_1977440 := by
    simpa [prefixWord, tailWord_1977440, baseEnd_1977440] using wordTrace_append hprefix tailTrace_1977440
  have hstable : (prefixWord ++ tailWord_1977440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977440).length < 2 ^ (prefixWord ++ tailWord_1977440).sum := by decide
  have hdescent : baseEnd_1977440 < baseStart_1977440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977493 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1977493 : Nat := 118140960795 + 1977493 * 2 ^ 59
def prefixEnd_1977493 : Nat := 4983230072969 + 3 ^ 40 * 1977493 * 2
def baseEnd_1977493 : Nat := 1015404399901536783243181

theorem tailTrace_1977493 : CollatzResearch.WordTrace tailWord_1977493 prefixEnd_1977493 1015404399901536783243181 := by
  unfold tailWord_1977493
  simp only [CollatzResearch.WordTrace]
  refine ⟨72125095024888064761537133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48083396683258709841024755 72125095024888064761537133)
  ·
    refine ⟨27046910634333024285576425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72125095024888064761537133 27046910634333024285576425)
    ·
      refine ⟨20285182975749768214182319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27046910634333024285576425 20285182975749768214182319)
      ·
        refine ⟨30427774463624652321273479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20285182975749768214182319 30427774463624652321273479)
        ·
          refine ⟨45641661695436978481910219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30427774463624652321273479 45641661695436978481910219)
          ·
            refine ⟨68462492543155467722865329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45641661695436978481910219 68462492543155467722865329)
            ·
              refine ⟨51346869407366600792148997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68462492543155467722865329 51346869407366600792148997)
              ·
                refine ⟨9627538013881237648527937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51346869407366600792148997 9627538013881237648527937)
                ·
                  refine ⟨7220653510410928236395953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9627538013881237648527937 7220653510410928236395953)
                  ·
                    refine ⟨5415490132808196177296965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7220653510410928236395953 5415490132808196177296965)
                    ·
                      refine ⟨1015404399901536783243181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5415490132808196177296965 1015404399901536783243181)
                      ·
                        rfl

theorem cell23_1977493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1977493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977493 prefixEnd_1977493 := by exact prefixLift 1977493
  have htrace : WordTrace (prefixWord ++ tailWord_1977493) baseStart_1977493 baseEnd_1977493 := by
    simpa [prefixWord, tailWord_1977493, baseEnd_1977493] using wordTrace_append hprefix tailTrace_1977493
  have hstable : (prefixWord ++ tailWord_1977493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977493).length < 2 ^ (prefixWord ++ tailWord_1977493).sum := by decide
  have hdescent : baseEnd_1977493 < baseStart_1977493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977533 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1977533 : Nat := 118140960795 + 1977533 * 2 ^ 59
def prefixEnd_1977533 : Nat := 4983230072969 + 3 ^ 40 * 1977533 * 2
def baseEnd_1977533 : Nat := 338474979709238875580999

theorem tailTrace_1977533 : CollatzResearch.WordTrace tailWord_1977533 prefixEnd_1977533 338474979709238875580999 := by
  unfold tailWord_1977533
  simp only [CollatzResearch.WordTrace]
  refine ⟨72126553944743151592993253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48084369296495434395328835 72126553944743151592993253)
  ·
    refine ⟨13523728864639340923686235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72126553944743151592993253 13523728864639340923686235)
    ·
      refine ⟨20285593296959011385529353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13523728864639340923686235 20285593296959011385529353)
      ·
        refine ⟨15214194972719258539147015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20285593296959011385529353 15214194972719258539147015)
        ·
          refine ⟨22821292459078887808720523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214194972719258539147015 22821292459078887808720523)
          ·
            refine ⟨34231938688618331713080785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22821292459078887808720523 34231938688618331713080785)
            ·
              refine ⟨25673954016463748784810589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34231938688618331713080785 25673954016463748784810589)
              ·
                refine ⟨9627732756173905794303971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25673954016463748784810589 9627732756173905794303971)
                ·
                  refine ⟨14441599134260858691455957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9627732756173905794303971 14441599134260858691455957)
                  ·
                    refine ⟨338474979709238875580999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14441599134260858691455957 338474979709238875580999)
                    ·
                      rfl

theorem cell23_1977533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1977533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977533 prefixEnd_1977533 := by exact prefixLift 1977533
  have htrace : WordTrace (prefixWord ++ tailWord_1977533) baseStart_1977533 baseEnd_1977533 := by
    simpa [prefixWord, tailWord_1977533, baseEnd_1977533] using wordTrace_append hprefix tailTrace_1977533
  have hstable : (prefixWord ++ tailWord_1977533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977533).length < 2 ^ (prefixWord ++ tailWord_1977533).sum := by decide
  have hdescent : baseEnd_1977533 < baseStart_1977533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977553 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_1977553 : Nat := 118140960795 + 1977553 * 2 ^ 59
def prefixEnd_1977553 : Nat := 4983230072969 + 3 ^ 40 * 1977553 * 2
def baseEnd_1977553 : Nat := 1015435208740806548492905

theorem tailTrace_1977553 : CollatzResearch.WordTrace tailWord_1977553 prefixEnd_1977553 1015435208740806548492905 := by
  unfold tailWord_1977553
  simp only [CollatzResearch.WordTrace]
  refine ⟨72127283404670695008721313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48084855603113796672480875 72127283404670695008721313)
  ·
    refine ⟨54095462553503021256540985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72127283404670695008721313 54095462553503021256540985)
    ·
      refine ⟨40571596915127265942405739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54095462553503021256540985 40571596915127265942405739)
      ·
        refine ⟨60857395372690898913608609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40571596915127265942405739 60857395372690898913608609)
        ·
          refine ⟨45643046529518174185206457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60857395372690898913608609 45643046529518174185206457)
          ·
            refine ⟨34232284897138630638904843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45643046529518174185206457 34232284897138630638904843)
            ·
              refine ⟨51348427345707945958357265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34232284897138630638904843 51348427345707945958357265)
              ·
                refine ⟨38511320509280959468767949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51348427345707945958357265 38511320509280959468767949)
                ·
                  refine ⟨14441745190980359800787981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38511320509280959468767949 14441745190980359800787981)
                  ·
                    refine ⟨5415654446617634925295493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14441745190980359800787981 5415654446617634925295493)
                    ·
                      refine ⟨1015435208740806548492905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5415654446617634925295493 1015435208740806548492905)
                      ·
                        rfl

theorem cell23_1977553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_1977553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977553 prefixEnd_1977553 := by exact prefixLift 1977553
  have htrace : WordTrace (prefixWord ++ tailWord_1977553) baseStart_1977553 baseEnd_1977553 := by
    simpa [prefixWord, tailWord_1977553, baseEnd_1977553] using wordTrace_append hprefix tailTrace_1977553
  have hstable : (prefixWord ++ tailWord_1977553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977553).length < 2 ^ (prefixWord ++ tailWord_1977553).sum := by decide
  have hdescent : baseEnd_1977553 < baseStart_1977553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977557 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1977557 : Nat := 118140960795 + 1977557 * 2 ^ 59
def prefixEnd_1977557 : Nat := 4983230072969 + 3 ^ 40 * 1977557 * 2
def baseEnd_1977557 : Nat := 1015437262663424532842887

theorem tailTrace_1977557 : CollatzResearch.WordTrace tailWord_1977557 prefixEnd_1977557 1015437262663424532842887 := by
  unfold tailWord_1977557
  simp only [CollatzResearch.WordTrace]
  refine ⟨72127429296656203691866925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48084952864437469127911283 72127429296656203691866925)
  ·
    refine ⟨27047785986246076384450097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72127429296656203691866925 27047785986246076384450097)
    ·
      refine ⟨20285839489684557288337573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27047785986246076384450097 20285839489684557288337573)
      ·
        refine ⟨3803594904315854491563295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20285839489684557288337573 3803594904315854491563295)
        ·
          refine ⟨5705392356473781737344943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803594904315854491563295 5705392356473781737344943)
          ·
            refine ⟨8558088534710672606017415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705392356473781737344943 8558088534710672606017415)
            ·
              refine ⟨12837132802066008909026123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558088534710672606017415 12837132802066008909026123)
              ·
                refine ⟨19255699203099013363539185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12837132802066008909026123 19255699203099013363539185)
                ·
                  refine ⟨14441774402324260022654389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19255699203099013363539185 14441774402324260022654389)
                  ·
                    refine ⟨1353916350217899377123849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14441774402324260022654389 1353916350217899377123849)
                    ·
                      refine ⟨1015437262663424532842887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353916350217899377123849 1015437262663424532842887)
                      ·
                        rfl

theorem cell23_1977557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1977557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977557 prefixEnd_1977557 := by exact prefixLift 1977557
  have htrace : WordTrace (prefixWord ++ tailWord_1977557) baseStart_1977557 baseEnd_1977557 := by
    simpa [prefixWord, tailWord_1977557, baseEnd_1977557] using wordTrace_append hprefix tailTrace_1977557
  have hstable : (prefixWord ++ tailWord_1977557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977557).length < 2 ^ (prefixWord ++ tailWord_1977557).sum := by decide
  have hdescent : baseEnd_1977557 < baseStart_1977557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977580 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_1977580 : Nat := 118140960795 + 1977580 * 2 ^ 59
def prefixEnd_1977580 : Nat := 4983230072969 + 3 ^ 40 * 1977580 * 2
def baseEnd_1977580 : Nat := 338483024239492647618427

theorem tailTrace_1977580 : CollatzResearch.WordTrace tailWord_1977580 prefixEnd_1977580 338483024239492647618427 := by
  unfold tailWord_1977580
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064134087786439309977097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48085512117048585746636129 36064134087786439309977097)
  ·
    refine ⟨27048100565839829482482823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36064134087786439309977097 27048100565839829482482823)
    ·
      refine ⟨40572150848759744223724235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27048100565839829482482823 40572150848759744223724235)
      ·
        refine ⟨60858226273139616335586353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40572150848759744223724235 60858226273139616335586353)
        ·
          refine ⟨45643669704854712251689765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60858226273139616335586353 45643669704854712251689765)
          ·
            refine ⟨8558188069660258547191831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45643669704854712251689765 8558188069660258547191831)
            ·
              refine ⟨12837282104490387820787747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558188069660258547191831 12837282104490387820787747)
              ·
                refine ⟨19255923156735581731181621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12837282104490387820787747 19255923156735581731181621)
                ·
                  refine ⟨1805242795943960787298277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19255923156735581731181621 1805242795943960787298277)
                  ·
                    refine ⟨338483024239492647618427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805242795943960787298277 338483024239492647618427)
                    ·
                      rfl

theorem cell23_1977580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_1977580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977580 prefixEnd_1977580 := by exact prefixLift 1977580
  have htrace : WordTrace (prefixWord ++ tailWord_1977580) baseStart_1977580 baseEnd_1977580 := by
    simpa [prefixWord, tailWord_1977580, baseEnd_1977580] using wordTrace_append hprefix tailTrace_1977580
  have hstable : (prefixWord ++ tailWord_1977580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977580).length < 2 ^ (prefixWord ++ tailWord_1977580).sum := by decide
  have hdescent : baseEnd_1977580 < baseStart_1977580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977587 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 4]
def baseStart_1977587 : Nat := 118140960795 + 1977587 * 2 ^ 59
def prefixEnd_1977587 : Nat := 4983230072969 + 3 ^ 40 * 1977587 * 2
def baseEnd_1977587 : Nat := 1015452667083059415467749

theorem tailTrace_1977587 : CollatzResearch.WordTrace tailWord_1977587 prefixEnd_1977587 1015452667083059415467749 := by
  unfold tailWord_1977587
  simp only [CollatzResearch.WordTrace]
  refine ⟨72128523486547518815459015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48085682324365012543639343 72128523486547518815459015)
  ·
    refine ⟨108192785229821278223188523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72128523486547518815459015 108192785229821278223188523)
    ·
      refine ⟨162289177844731917334782785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108192785229821278223188523 162289177844731917334782785)
      ·
        refine ⟨121716883383548938001087089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162289177844731917334782785 121716883383548938001087089)
        ·
          refine ⟨91287662537661703500815317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121716883383548938001087089 91287662537661703500815317)
          ·
            refine ⟨2139554590726446175800359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 91287662537661703500815317 2139554590726446175800359)
            ·
              refine ⟨3209331886089669263700539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139554590726446175800359 3209331886089669263700539)
              ·
                refine ⟨4813997829134503895550809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3209331886089669263700539 4813997829134503895550809)
                ·
                  refine ⟨3610498371850877921663107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4813997829134503895550809 3610498371850877921663107)
                  ·
                    refine ⟨5415747557776316882494661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3610498371850877921663107 5415747557776316882494661)
                    ·
                      refine ⟨1015452667083059415467749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5415747557776316882494661 1015452667083059415467749)
                      ·
                        rfl

theorem cell23_1977587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_1977587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977587 prefixEnd_1977587 := by exact prefixLift 1977587
  have htrace : WordTrace (prefixWord ++ tailWord_1977587) baseStart_1977587 baseEnd_1977587 := by
    simpa [prefixWord, tailWord_1977587, baseEnd_1977587] using wordTrace_append hprefix tailTrace_1977587
  have hstable : (prefixWord ++ tailWord_1977587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977587).length < 2 ^ (prefixWord ++ tailWord_1977587).sum := by decide
  have hdescent : baseEnd_1977587 < baseStart_1977587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977588 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 5]
def baseStart_1977588 : Nat := 118140960795 + 1977588 * 2 ^ 59
def prefixEnd_1977588 : Nat := 4983230072969 + 3 ^ 40 * 1977588 * 2
def baseEnd_1977588 : Nat := 112828131173745990172805

theorem tailTrace_1977588 : CollatzResearch.WordTrace tailWord_1977588 prefixEnd_1977588 112828131173745990172805 := by
  unfold tailWord_1977588
  simp only [CollatzResearch.WordTrace]
  refine ⟨36064279979771947993122709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48085706639695930657496945 36064279979771947993122709)
  ·
    refine ⟨1690513124051810062177627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36064279979771947993122709 1690513124051810062177627)
    ·
      refine ⟨2535769686077715093266441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690513124051810062177627 2535769686077715093266441)
      ·
        refine ⟨1901827264558286319949831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535769686077715093266441 1901827264558286319949831)
        ·
          refine ⟨2852740896837429479924747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901827264558286319949831 2852740896837429479924747)
          ·
            refine ⟨4279111345256144219887121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852740896837429479924747 4279111345256144219887121)
            ·
              refine ⟨3209333508942108164915341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279111345256144219887121 3209333508942108164915341)
              ·
                refine ⟨1203500065853290561843253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3209333508942108164915341 1203500065853290561843253)
                ·
                  refine ⟨112828131173745990172805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203500065853290561843253 112828131173745990172805)
                  ·
                    rfl

theorem cell23_1977588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_1977588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977588 prefixEnd_1977588 := by exact prefixLift 1977588
  have htrace : WordTrace (prefixWord ++ tailWord_1977588) baseStart_1977588 baseEnd_1977588 := by
    simpa [prefixWord, tailWord_1977588, baseEnd_1977588] using wordTrace_append hprefix tailTrace_1977588
  have hstable : (prefixWord ++ tailWord_1977588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977588).length < 2 ^ (prefixWord ++ tailWord_1977588).sum := by decide
  have hdescent : baseEnd_1977588 < baseStart_1977588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977593 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 8]
def baseStart_1977593 : Nat := 118140960795 + 1977593 * 2 ^ 59
def prefixEnd_1977593 : Nat := 4983230072969 + 3 ^ 40 * 1977593 * 2
def baseEnd_1977593 : Nat := 112828416440776265776969

theorem tailTrace_1977593 : CollatzResearch.WordTrace tailWord_1977593 prefixEnd_1977593 112828416440776265776969 := by
  unfold tailWord_1977593
  simp only [CollatzResearch.WordTrace]
  refine ⟨72128742324525781840177433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48085828216350521226784955 72128742324525781840177433)
  ·
    refine ⟨54096556743394336380133075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72128742324525781840177433 54096556743394336380133075)
    ·
      refine ⟨81144835115091504570199613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54096556743394336380133075 81144835115091504570199613)
      ·
        refine ⟨30429313168159314213824855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81144835115091504570199613 30429313168159314213824855)
        ·
          refine ⟨45643969752238971320737283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30429313168159314213824855 45643969752238971320737283)
          ·
            refine ⟨68465954628358456981105925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45643969752238971320737283 68465954628358456981105925)
            ·
              refine ⟨12837366492817210683957361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68465954628358456981105925 12837366492817210683957361)
              ·
                refine ⟨9628024869612908012968021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12837366492817210683957361 9628024869612908012968021)
                ·
                  refine ⟨112828416440776265776969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9628024869612908012968021 112828416440776265776969)
                  ·
                    rfl

theorem cell23_1977593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_1977593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977593 prefixEnd_1977593 := by exact prefixLift 1977593
  have htrace : WordTrace (prefixWord ++ tailWord_1977593) baseStart_1977593 baseEnd_1977593 := by
    simpa [prefixWord, tailWord_1977593, baseEnd_1977593] using wordTrace_append hprefix tailTrace_1977593
  have hstable : (prefixWord ++ tailWord_1977593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977593).length < 2 ^ (prefixWord ++ tailWord_1977593).sum := by decide
  have hdescent : baseEnd_1977593 < baseStart_1977593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977614 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_1977614 : Nat := 118140960795 + 1977614 * 2 ^ 59
def prefixEnd_1977614 : Nat := 4983230072969 + 3 ^ 40 * 1977614 * 2
def baseEnd_1977614 : Nat := 338488843686910269943375

theorem tailTrace_1977614 : CollatzResearch.WordTrace tailWord_1977614 prefixEnd_1977614 338488843686910269943375 := by
  unfold tailWord_1977614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016188532181212803336487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48086338838299801617794597 9016188532181212803336487)
  ·
    refine ⟨13524282798271819205004731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9016188532181212803336487 13524282798271819205004731)
    ·
      refine ⟨20286424197407728807507097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13524282798271819205004731 20286424197407728807507097)
      ·
        refine ⟨15214818148055796605630323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20286424197407728807507097 15214818148055796605630323)
        ·
          refine ⟨22822227222083694908445485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214818148055796605630323 22822227222083694908445485)
          ·
            refine ⟨8558335208281385590667057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22822227222083694908445485 8558335208281385590667057)
            ·
              refine ⟨6418751406211039193000293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558335208281385590667057 6418751406211039193000293)
              ·
                refine ⟨1203515888664569848687555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6418751406211039193000293 1203515888664569848687555)
                ·
                  refine ⟨1805273832996854773031333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203515888664569848687555 1805273832996854773031333)
                  ·
                    refine ⟨338488843686910269943375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805273832996854773031333 338488843686910269943375)
                    ·
                      rfl

theorem cell23_1977614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_1977614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977614 prefixEnd_1977614 := by exact prefixLift 1977614
  have htrace : WordTrace (prefixWord ++ tailWord_1977614) baseStart_1977614 baseEnd_1977614 := by
    simpa [prefixWord, tailWord_1977614, baseEnd_1977614] using wordTrace_append hprefix tailTrace_1977614
  have hstable : (prefixWord ++ tailWord_1977614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977614).length < 2 ^ (prefixWord ++ tailWord_1977614).sum := by decide
  have hdescent : baseEnd_1977614 < baseStart_1977614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977647 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 2, 3, 2]
def baseStart_1977647 : Nat := 118140960795 + 1977647 * 2 ^ 59
def prefixEnd_1977647 : Nat := 4983230072969 + 3 ^ 40 * 1977647 * 2
def baseEnd_1977647 : Nat := 1015483475922329180717473

theorem tailTrace_1977647 : CollatzResearch.WordTrace tailWord_1977647 prefixEnd_1977647 1015483475922329180717473 := by
  unfold tailWord_1977647
  simp only [CollatzResearch.WordTrace]
  refine ⟨72130711866330149062643195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48087141244220099375095463 72130711866330149062643195)
  ·
    refine ⟨108196067799495223593964793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72130711866330149062643195 108196067799495223593964793)
    ·
      refine ⟨81147050849621417695473595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108196067799495223593964793 81147050849621417695473595)
      ·
        refine ⟨121720576274432126543210393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81147050849621417695473595 121720576274432126543210393)
        ·
          refine ⟨91290432205824094907407795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121720576274432126543210393 91290432205824094907407795)
          ·
            refine ⟨136935648308736142361111693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91290432205824094907407795 136935648308736142361111693)
            ·
              refine ⟨51350868115776053385416885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136935648308736142361111693 51350868115776053385416885)
              ·
                refine ⟨4814143885854005004882833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51350868115776053385416885 4814143885854005004882833)
                ·
                  refine ⟨3610607914390503753662125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4814143885854005004882833 3610607914390503753662125)
                  ·
                    refine ⟨1353977967896438907623297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610607914390503753662125 1353977967896438907623297)
                    ·
                      refine ⟨1015483475922329180717473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1353977967896438907623297 1015483475922329180717473)
                      ·
                        rfl

theorem cell23_1977647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3, 2].length) (baseStart_1977647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977647 prefixEnd_1977647 := by exact prefixLift 1977647
  have htrace : WordTrace (prefixWord ++ tailWord_1977647) baseStart_1977647 baseEnd_1977647 := by
    simpa [prefixWord, tailWord_1977647, baseEnd_1977647] using wordTrace_append hprefix tailTrace_1977647
  have hstable : (prefixWord ++ tailWord_1977647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977647).length < 2 ^ (prefixWord ++ tailWord_1977647).sum := by decide
  have hdescent : baseEnd_1977647 < baseStart_1977647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977680 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_1977680 : Nat := 118140960795 + 1977680 * 2 ^ 59
def prefixEnd_1977680 : Nat := 4983230072969 + 3 ^ 40 * 1977680 * 2
def baseEnd_1977680 : Nat := 1015500420783927551604821

theorem tailTrace_1977680 : CollatzResearch.WordTrace tailWord_1977680 prefixEnd_1977680 1015500420783927551604821 := by
  unfold tailWord_1977680
  simp only [CollatzResearch.WordTrace]
  refine ⟨36065957737605297849297247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48087943650140397132396329 36065957737605297849297247)
  ·
    refine ⟨54098936606407946773945871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36065957737605297849297247 54098936606407946773945871)
    ·
      refine ⟨81148404909611920160918807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54098936606407946773945871 81148404909611920160918807)
      ·
        refine ⟨121722607364417880241378211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81148404909611920160918807 121722607364417880241378211)
        ·
          refine ⟨182583911046626820362067317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121722607364417880241378211 182583911046626820362067317)
          ·
            refine ⟨17117241660621264408943811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182583911046626820362067317 17117241660621264408943811)
            ·
              refine ⟨25675862490931896613415717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17117241660621264408943811 25675862490931896613415717)
              ·
                refine ⟨4814224217049730615015447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25675862490931896613415717 4814224217049730615015447)
                ·
                  refine ⟨7221336325574595922523171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4814224217049730615015447 7221336325574595922523171)
                  ·
                    refine ⟨10832004488361893883784757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7221336325574595922523171 10832004488361893883784757)
                    ·
                      refine ⟨1015500420783927551604821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10832004488361893883784757 1015500420783927551604821)
                      ·
                        rfl

theorem cell23_1977680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_1977680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977680 prefixEnd_1977680 := by exact prefixLift 1977680
  have htrace : WordTrace (prefixWord ++ tailWord_1977680) baseStart_1977680 baseEnd_1977680 := by
    simpa [prefixWord, tailWord_1977680, baseEnd_1977680] using wordTrace_append hprefix tailTrace_1977680
  have hstable : (prefixWord ++ tailWord_1977680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977680).length < 2 ^ (prefixWord ++ tailWord_1977680).sum := by decide
  have hdescent : baseEnd_1977680 < baseStart_1977680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977690 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1977690 : Nat := 118140960795 + 1977690 * 2 ^ 59
def prefixEnd_1977690 : Nat := 4983230072969 + 3 ^ 40 * 1977690 * 2
def baseEnd_1977690 : Nat := 1015505555590472512479775

theorem tailTrace_1977690 : CollatzResearch.WordTrace tailWord_1977690 prefixEnd_1977690 1015505555590472512479775 := by
  unfold tailWord_1977690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18033070051293591851614631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48088186803449578270972349 18033070051293591851614631)
  ·
    refine ⟨27049605076940387777421947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18033070051293591851614631 27049605076940387777421947)
    ·
      refine ⟨40574407615410581666132921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27049605076940387777421947 40574407615410581666132921)
      ·
        refine ⟨30430805711557936249599691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40574407615410581666132921 30430805711557936249599691)
        ·
          refine ⟨45646208567336904374399537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30430805711557936249599691 45646208567336904374399537)
          ·
            refine ⟨34234656425502678280799653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45646208567336904374399537 34234656425502678280799653)
            ·
              refine ⟨6418998079781752177649935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34234656425502678280799653 6418998079781752177649935)
              ·
                refine ⟨9628497119672628266474903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6418998079781752177649935 9628497119672628266474903)
                ·
                  refine ⟨14442745679508942399712355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9628497119672628266474903 14442745679508942399712355)
                  ·
                    refine ⟨21664118519263413599568533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14442745679508942399712355 21664118519263413599568533)
                    ·
                      refine ⟨1015505555590472512479775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21664118519263413599568533 1015505555590472512479775)
                      ·
                        rfl

theorem cell23_1977690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1977690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977690 prefixEnd_1977690 := by exact prefixLift 1977690
  have htrace : WordTrace (prefixWord ++ tailWord_1977690) baseStart_1977690 baseEnd_1977690 := by
    simpa [prefixWord, tailWord_1977690, baseEnd_1977690] using wordTrace_append hprefix tailTrace_1977690
  have hstable : (prefixWord ++ tailWord_1977690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977690).length < 2 ^ (prefixWord ++ tailWord_1977690).sum := by decide
  have hdescent : baseEnd_1977690 < baseStart_1977690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977700 : List Nat := [2, 3, 1, 1, 3, 2, 2, 9]
def baseStart_1977700 : Nat := 118140960795 + 1977700 * 2 ^ 59
def prefixEnd_1977700 : Nat := 4983230072969 + 3 ^ 40 * 1977700 * 2
def baseEnd_1977700 : Nat := 37611507051741387902027

theorem tailTrace_1977700 : CollatzResearch.WordTrace tailWord_1977700 prefixEnd_1977700 37611507051741387902027 := by
  unfold tailWord_1977700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36066322467569069557161277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48088429956758759409548369 36066322467569069557161277)
  ·
    refine ⟨13524870925338401083935479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36066322467569069557161277 13524870925338401083935479)
    ·
      refine ⟨20287306388007601625903219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13524870925338401083935479 20287306388007601625903219)
      ·
        refine ⟨30430959582011402438854829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20287306388007601625903219 30430959582011402438854829)
        ·
          refine ⟨11411609843254275914570561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30430959582011402438854829 11411609843254275914570561)
          ·
            refine ⟨8558707382440706935927921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11411609843254275914570561 8558707382440706935927921)
            ·
              refine ⟨6419030536830530201945941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8558707382440706935927921 6419030536830530201945941)
              ·
                refine ⟨37611507051741387902027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6419030536830530201945941 37611507051741387902027)
                ·
                  rfl

theorem cell23_1977700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 9].length) (baseStart_1977700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977700 prefixEnd_1977700 := by exact prefixLift 1977700
  have htrace : WordTrace (prefixWord ++ tailWord_1977700) baseStart_1977700 baseEnd_1977700 := by
    simpa [prefixWord, tailWord_1977700, baseEnd_1977700] using wordTrace_append hprefix tailTrace_1977700
  have hstable : (prefixWord ++ tailWord_1977700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977700).length < 2 ^ (prefixWord ++ tailWord_1977700).sum := by decide
  have hdescent : baseEnd_1977700 < baseStart_1977700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977711 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 1, 2, 2]
def baseStart_1977711 : Nat := 118140960795 + 1977711 * 2 ^ 59
def prefixEnd_1977711 : Nat := 4983230072969 + 3 ^ 40 * 1977711 * 2
def baseEnd_1977711 : Nat := 1015516338684216930317179

theorem tailTrace_1977711 : CollatzResearch.WordTrace tailWord_1977711 prefixEnd_1977711 1015516338684216930317179 := by
  unfold tailWord_1977711
  simp only [CollatzResearch.WordTrace]
  refine ⟨72133046138098287992972987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48088697425398858661981991 72133046138098287992972987)
  ·
    refine ⟨108199569207147431989459481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72133046138098287992972987 108199569207147431989459481)
    ·
      refine ⟨81149676905360573992094611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108199569207147431989459481 81149676905360573992094611)
      ·
        refine ⟨121724515358040860988141917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81149676905360573992094611 121724515358040860988141917)
        ·
          refine ⟨45646693259265322870553219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121724515358040860988141917 45646693259265322870553219)
          ·
            refine ⟨68470039888897984305829829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45646693259265322870553219 68470039888897984305829829)
            ·
              refine ⟨12838132479168372057343093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68470039888897984305829829 12838132479168372057343093)
              ·
                refine ⟨1203574919922034880375915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12838132479168372057343093 1203574919922034880375915)
                ·
                  refine ⟨1805362379883052320563873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203574919922034880375915 1805362379883052320563873)
                  ·
                    refine ⟨1354021784912289240422905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1805362379883052320563873 1354021784912289240422905)
                    ·
                      refine ⟨1015516338684216930317179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354021784912289240422905 1015516338684216930317179)
                      ·
                        rfl

theorem cell23_1977711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 1, 2, 2].length) (baseStart_1977711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977711 prefixEnd_1977711 := by exact prefixLift 1977711
  have htrace : WordTrace (prefixWord ++ tailWord_1977711) baseStart_1977711 baseEnd_1977711 := by
    simpa [prefixWord, tailWord_1977711, baseEnd_1977711] using wordTrace_append hprefix tailTrace_1977711
  have hstable : (prefixWord ++ tailWord_1977711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977711).length < 2 ^ (prefixWord ++ tailWord_1977711).sum := by decide
  have hdescent : baseEnd_1977711 < baseStart_1977711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977717 : List Nat := [1, 3, 4, 1, 4, 10]
def baseStart_1977717 : Nat := 118140960795 + 1977717 * 2 ^ 59
def prefixEnd_1977717 : Nat := 4983230072969 + 3 ^ 40 * 1977717 * 2
def baseEnd_1977717 : Nat := 4179092261597300028157

theorem tailTrace_1977717 : CollatzResearch.WordTrace tailWord_1977717 prefixEnd_1977717 4179092261597300028157 := by
  unfold tailWord_1977717
  simp only [CollatzResearch.WordTrace]
  refine ⟨72133264976076551017691405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48088843317384367345127603 72133264976076551017691405)
  ·
    refine ⟨27049974366028706631634277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72133264976076551017691405 27049974366028706631634277)
    ·
      refine ⟨5071870193630382493431427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27049974366028706631634277 5071870193630382493431427)
      ·
        refine ⟨7607805290445573740147141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5071870193630382493431427 7607805290445573740147141)
        ·
          refine ⟨1426463491958545076277589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7607805290445573740147141 1426463491958545076277589)
          ·
            refine ⟨4179092261597300028157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1426463491958545076277589 4179092261597300028157)
            ·
              rfl

theorem cell23_1977717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 10].length) (baseStart_1977717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977717 prefixEnd_1977717 := by exact prefixLift 1977717
  have htrace : WordTrace (prefixWord ++ tailWord_1977717) baseStart_1977717 baseEnd_1977717 := by
    simpa [prefixWord, tailWord_1977717, baseEnd_1977717] using wordTrace_append hprefix tailTrace_1977717
  have hstable : (prefixWord ++ tailWord_1977717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977717).length < 2 ^ (prefixWord ++ tailWord_1977717).sum := by decide
  have hdescent : baseEnd_1977717 < baseStart_1977717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977754 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2]
def baseStart_1977754 : Nat := 118140960795 + 1977754 * 2 ^ 59
def prefixEnd_1977754 : Nat := 4983230072969 + 3 ^ 40 * 1977754 * 2
def baseEnd_1977754 : Nat := 1015538418352360262079481

theorem tailTrace_1977754 : CollatzResearch.WordTrace tailWord_1977754 prefixEnd_1977754 1015538418352360262079481 := by
  unfold tailWord_1977754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18033653619235626584197079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48089742984628337557858877 18033653619235626584197079)
  ·
    refine ⟨27050480428853439876295619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18033653619235626584197079 27050480428853439876295619)
    ·
      refine ⟨40575720643280159814443429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27050480428853439876295619 40575720643280159814443429)
      ·
        refine ⟨7607947620615029965208143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40575720643280159814443429 7607947620615029965208143)
        ·
          refine ⟨11411921430922544947812215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7607947620615029965208143 11411921430922544947812215)
          ·
            refine ⟨17117882146383817421718323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11411921430922544947812215 17117882146383817421718323)
            ·
              refine ⟨25676823219575726132577485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17117882146383817421718323 25676823219575726132577485)
              ·
                refine ⟨9628808707340897299716557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25676823219575726132577485 9628808707340897299716557)
                ·
                  refine ⟨3610803265252836487393709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9628808707340897299716557 3610803265252836487393709)
                  ·
                    refine ⟨1354051224469813682772641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610803265252836487393709 1354051224469813682772641)
                    ·
                      refine ⟨1015538418352360262079481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354051224469813682772641 1015538418352360262079481)
                      ·
                        rfl

theorem cell23_1977754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_1977754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977754 prefixEnd_1977754 := by exact prefixLift 1977754
  have htrace : WordTrace (prefixWord ++ tailWord_1977754) baseStart_1977754 baseEnd_1977754 := by
    simpa [prefixWord, tailWord_1977754, baseEnd_1977754] using wordTrace_append hprefix tailTrace_1977754
  have hstable : (prefixWord ++ tailWord_1977754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977754).length < 2 ^ (prefixWord ++ tailWord_1977754).sum := by decide
  have hdescent : baseEnd_1977754 < baseStart_1977754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977760 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_1977760 : Nat := 118140960795 + 1977760 * 2 ^ 59
def prefixEnd_1977760 : Nat := 4983230072969 + 3 ^ 40 * 1977760 * 2
def baseEnd_1977760 : Nat := 338513833078762412868151

theorem tailTrace_1977760 : CollatzResearch.WordTrace tailWord_1977760 prefixEnd_1977760 338513833078762412868151 := by
  unfold tailWord_1977760
  simp only [CollatzResearch.WordTrace]
  refine ⟨36067416657460384680753367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48089888876613846241004489 36067416657460384680753367)
  ·
    refine ⟨54101124986190577021130051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36067416657460384680753367 54101124986190577021130051)
    ·
      refine ⟨81151687479285865531695077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54101124986190577021130051 81151687479285865531695077)
      ·
        refine ⟨15215941402366099787192827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81151687479285865531695077 15215941402366099787192827)
        ·
          refine ⟨22823912103549149680789241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15215941402366099787192827 22823912103549149680789241)
          ·
            refine ⟨17117934077661862260591931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22823912103549149680789241 17117934077661862260591931)
            ·
              refine ⟨25676901116492793390887897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17117934077661862260591931 25676901116492793390887897)
              ·
                refine ⟨19257675837369595043165923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25676901116492793390887897 19257675837369595043165923)
                ·
                  refine ⟨28886513756054392564748885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19257675837369595043165923 28886513756054392564748885)
                  ·
                    refine ⟨338513833078762412868151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28886513756054392564748885 338513833078762412868151)
                    ·
                      rfl

theorem cell23_1977760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_1977760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977760 prefixEnd_1977760 := by exact prefixLift 1977760
  have htrace : WordTrace (prefixWord ++ tailWord_1977760) baseStart_1977760 baseEnd_1977760 := by
    simpa [prefixWord, tailWord_1977760, baseEnd_1977760] using wordTrace_append hprefix tailTrace_1977760
  have hstable : (prefixWord ++ tailWord_1977760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977760).length < 2 ^ (prefixWord ++ tailWord_1977760).sum := by decide
  have hdescent : baseEnd_1977760 < baseStart_1977760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977841 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 5]
def baseStart_1977841 : Nat := 118140960795 + 1977841 * 2 ^ 59
def prefixEnd_1977841 : Nat := 4983230072969 + 3 ^ 40 * 1977841 * 2
def baseEnd_1977841 : Nat := 112842565685477935743509

theorem tailTrace_1977841 : CollatzResearch.WordTrace tailWord_1977841 prefixEnd_1977841 112842565685477935743509 := by
  unfold tailWord_1977841
  simp only [CollatzResearch.WordTrace]
  refine ⟨72137787627627320195205377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48091858418418213463470251 72137787627627320195205377)
  ·
    refine ⟨54103340720720490146404033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72137787627627320195205377 54103340720720490146404033)
    ·
      refine ⟨40577505540540367609803025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54103340720720490146404033 40577505540540367609803025)
      ·
        refine ⟨30433129155405275707352269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40577505540540367609803025 30433129155405275707352269)
        ·
          refine ⟨11412423433276978390257101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30433129155405275707352269 11412423433276978390257101)
          ·
            refine ⟨4279658787478866896346413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11412423433276978390257101 4279658787478866896346413)
            ·
              refine ⟨1604872045304575086129905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4279658787478866896346413 1604872045304575086129905)
              ·
                refine ⟨1203654033978431314597429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604872045304575086129905 1203654033978431314597429)
                ·
                  refine ⟨112842565685477935743509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203654033978431314597429 112842565685477935743509)
                  ·
                    rfl

theorem cell23_1977841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 5].length) (baseStart_1977841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977841 prefixEnd_1977841 := by exact prefixLift 1977841
  have htrace : WordTrace (prefixWord ++ tailWord_1977841) baseStart_1977841 baseEnd_1977841 := by
    simpa [prefixWord, tailWord_1977841, baseEnd_1977841] using wordTrace_append hprefix tailTrace_1977841
  have hstable : (prefixWord ++ tailWord_1977841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977841).length < 2 ^ (prefixWord ++ tailWord_1977841).sum := by decide
  have hdescent : baseEnd_1977841 < baseStart_1977841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1977981 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_1977981 : Nat := 118140960795 + 1977981 * 2 ^ 59
def prefixEnd_1977981 : Nat := 4983230072969 + 3 ^ 40 * 1977981 * 2
def baseEnd_1977981 : Nat := 1015654978460930873940937

theorem tailTrace_1977981 : CollatzResearch.WordTrace tailWord_1977981 prefixEnd_1977981 1015654978460930873940937 := by
  unfold tailWord_1977981
  simp only [CollatzResearch.WordTrace]
  refine ⟨72142893847120124105301797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48095262564746749403534531 72142893847120124105301797)
  ·
    refine ⟨13526792596335023269744087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72142893847120124105301797 13526792596335023269744087)
    ·
      refine ⟨20290188894502534904616131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13526792596335023269744087 20290188894502534904616131)
      ·
        refine ⟨30435283341753802356924197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20290188894502534904616131 30435283341753802356924197)
        ·
          refine ⟨5706615626578837941923287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30435283341753802356924197 5706615626578837941923287)
          ·
            refine ⟨8559923439868256912884931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5706615626578837941923287 8559923439868256912884931)
            ·
              refine ⟨12839885159802385369327397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8559923439868256912884931 12839885159802385369327397)
              ·
                refine ⟨2407478467462947256748887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12839885159802385369327397 2407478467462947256748887)
                ·
                  refine ⟨3611217701194420885123331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407478467462947256748887 3611217701194420885123331)
                  ·
                    refine ⟨5416826551791631327684997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3611217701194420885123331 5416826551791631327684997)
                    ·
                      refine ⟨1015654978460930873940937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5416826551791631327684997 1015654978460930873940937)
                      ·
                        rfl

theorem cell23_1977981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_1977981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1977981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1977981 prefixEnd_1977981 := by exact prefixLift 1977981
  have htrace : WordTrace (prefixWord ++ tailWord_1977981) baseStart_1977981 baseEnd_1977981 := by
    simpa [prefixWord, tailWord_1977981, baseEnd_1977981] using wordTrace_append hprefix tailTrace_1977981
  have hstable : (prefixWord ++ tailWord_1977981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1977981).length < 2 ^ (prefixWord ++ tailWord_1977981).sum := by decide
  have hdescent : baseEnd_1977981 < baseStart_1977981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1977981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978071 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 3, 4, 2]
def baseStart_1978071 : Nat := 118140960795 + 1978071 * 2 ^ 59
def prefixEnd_1978071 : Nat := 4983230072969 + 3 ^ 40 * 1978071 * 2
def baseEnd_1978071 : Nat := 1015701191719835521815523

theorem tailTrace_1978071 : CollatzResearch.WordTrace tailWord_1978071 prefixEnd_1978071 1015701191719835521815523 := by
  unfold tailWord_1978071
  simp only [CollatzResearch.WordTrace]
  refine ⟨72146176416794069476078067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48097450944529379650718711 72146176416794069476078067)
  ·
    refine ⟨108219264625191104214117101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72146176416794069476078067 108219264625191104214117101)
    ·
      refine ⟨40582224234446664080293913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108219264625191104214117101 40582224234446664080293913)
      ·
        refine ⟨30436668175834998060220435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40582224234446664080293913 30436668175834998060220435)
        ·
          refine ⟨45655002263752497090330653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30436668175834998060220435 45655002263752497090330653)
          ·
            refine ⟨17120625848907186408873995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45655002263752497090330653 17120625848907186408873995)
            ·
              refine ⟨25680938773360779613310993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17120625848907186408873995 25680938773360779613310993)
              ·
                refine ⟨19260704080020584709983245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25680938773360779613310993 19260704080020584709983245)
                ·
                  refine ⟨7222764030007719266243717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19260704080020584709983245 7222764030007719266243717)
                  ·
                    refine ⟨1354268255626447362420697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222764030007719266243717 1354268255626447362420697)
                    ·
                      refine ⟨1015701191719835521815523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354268255626447362420697 1015701191719835521815523)
                      ·
                        rfl

theorem cell23_1978071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_1978071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978071 prefixEnd_1978071 := by exact prefixLift 1978071
  have htrace : WordTrace (prefixWord ++ tailWord_1978071) baseStart_1978071 baseEnd_1978071 := by
    simpa [prefixWord, tailWord_1978071, baseEnd_1978071] using wordTrace_append hprefix tailTrace_1978071
  have hstable : (prefixWord ++ tailWord_1978071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978071).length < 2 ^ (prefixWord ++ tailWord_1978071).sum := by decide
  have hdescent : baseEnd_1978071 < baseStart_1978071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978081 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1978081 : Nat := 118140960795 + 1978081 * 2 ^ 59
def prefixEnd_1978081 : Nat := 4983230072969 + 3 ^ 40 * 1978081 * 2
def baseEnd_1978081 : Nat := 338568775508793494230159

theorem tailTrace_1978081 : CollatzResearch.WordTrace tailWord_1978081 prefixEnd_1978081 338568775508793494230159 := by
  unfold tailWord_1978081
  simp only [CollatzResearch.WordTrace]
  refine ⟨72146541146757841183942097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48097694097838560789294731 72146541146757841183942097)
  ·
    refine ⟨54109905860068380887956573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72146541146757841183942097 54109905860068380887956573)
    ·
      refine ⟨20291214697525642832983715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54109905860068380887956573 20291214697525642832983715)
      ·
        refine ⟨30436822046288464249475573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20291214697525642832983715 30436822046288464249475573)
        ·
          refine ⟨2853452066839543523388335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30436822046288464249475573 2853452066839543523388335)
          ·
            refine ⟨4280178100259315285082503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853452066839543523388335 4280178100259315285082503)
            ·
              refine ⟨6420267150388972927623755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4280178100259315285082503 6420267150388972927623755)
              ·
                refine ⟨9630400725583459391435633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420267150388972927623755 9630400725583459391435633)
                ·
                  refine ⟨7222800544187594543576725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9630400725583459391435633 7222800544187594543576725)
                  ·
                    refine ⟨338568775508793494230159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7222800544187594543576725 338568775508793494230159)
                    ·
                      rfl

theorem cell23_1978081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1978081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978081 prefixEnd_1978081 := by exact prefixLift 1978081
  have htrace : WordTrace (prefixWord ++ tailWord_1978081) baseStart_1978081 baseEnd_1978081 := by
    simpa [prefixWord, tailWord_1978081, baseEnd_1978081] using wordTrace_append hprefix tailTrace_1978081
  have hstable : (prefixWord ++ tailWord_1978081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978081).length < 2 ^ (prefixWord ++ tailWord_1978081).sum := by decide
  have hdescent : baseEnd_1978081 < baseStart_1978081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978088 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1978088 : Nat := 118140960795 + 1978088 * 2 ^ 59
def prefixEnd_1978088 : Nat := 4983230072969 + 3 ^ 40 * 1978088 * 2
def baseEnd_1978088 : Nat := 1015709920890961955302945

theorem tailTrace_1978088 : CollatzResearch.WordTrace tailWord_1978088 prefixEnd_1978088 1015709920890961955302945 := by
  unfold tailWord_1978088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36073398228866240689723459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48097864305154987586297945 36073398228866240689723459)
  ·
    refine ⟨54110097343299361034585189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36073398228866240689723459 54110097343299361034585189)
    ·
      refine ⟨10145643251868630193984723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54110097343299361034585189 10145643251868630193984723)
      ·
        refine ⟨15218464877802945290977085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10145643251868630193984723 15218464877802945290977085)
        ·
          refine ⟨5706924329176104484116407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15218464877802945290977085 5706924329176104484116407)
          ·
            refine ⟨8560386493764156726174611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5706924329176104484116407 8560386493764156726174611)
            ·
              refine ⟨12840579740646235089261917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560386493764156726174611 12840579740646235089261917)
              ·
                refine ⟨4815217402742338158473219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12840579740646235089261917 4815217402742338158473219)
                ·
                  refine ⟨7222826104113507237709829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4815217402742338158473219 7222826104113507237709829)
                  ·
                    refine ⟨1354279894521282607070593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7222826104113507237709829 1354279894521282607070593)
                    ·
                      refine ⟨1015709920890961955302945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354279894521282607070593 1015709920890961955302945)
                      ·
                        rfl

theorem cell23_1978088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1978088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978088 prefixEnd_1978088 := by exact prefixLift 1978088
  have htrace : WordTrace (prefixWord ++ tailWord_1978088) baseStart_1978088 baseEnd_1978088 := by
    simpa [prefixWord, tailWord_1978088, baseEnd_1978088] using wordTrace_append hprefix tailTrace_1978088
  have hstable : (prefixWord ++ tailWord_1978088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978088).length < 2 ^ (prefixWord ++ tailWord_1978088).sum := by decide
  have hdescent : baseEnd_1978088 < baseStart_1978088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978111 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 5]
def baseStart_1978111 : Nat := 118140960795 + 1978111 * 2 ^ 59
def prefixEnd_1978111 : Nat := 4983230072969 + 3 ^ 40 * 1978111 * 2
def baseEnd_1978111 : Nat := 112857970105112818368371

theorem tailTrace_1978111 : CollatzResearch.WordTrace tailWord_1978111 prefixEnd_1978111 112857970105112818368371 := by
  unfold tailWord_1978111
  simp only [CollatzResearch.WordTrace]
  refine ⟨72147635336649156307534187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48098423557766104205022791 72147635336649156307534187)
  ·
    refine ⟨108221453004973734461301281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72147635336649156307534187 108221453004973734461301281)
    ·
      refine ⟨81166089753730300845975961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108221453004973734461301281 81166089753730300845975961)
      ·
        refine ⟨60874567315297725634481971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81166089753730300845975961 60874567315297725634481971)
        ·
          refine ⟨91311850972946588451722957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60874567315297725634481971 91311850972946588451722957)
          ·
            refine ⟨34241944114854970669396109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91311850972946588451722957 34241944114854970669396109)
            ·
              refine ⟨12840729043070614001023541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34241944114854970669396109 12840729043070614001023541)
              ·
                refine ⟨1203818347787870062595957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12840729043070614001023541 1203818347787870062595957)
                ·
                  refine ⟨112857970105112818368371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1203818347787870062595957 112857970105112818368371)
                  ·
                    rfl

theorem cell23_1978111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 5].length) (baseStart_1978111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978111 prefixEnd_1978111 := by exact prefixLift 1978111
  have htrace : WordTrace (prefixWord ++ tailWord_1978111) baseStart_1978111 baseEnd_1978111 := by
    simpa [prefixWord, tailWord_1978111, baseEnd_1978111] using wordTrace_append hprefix tailTrace_1978111
  have hstable : (prefixWord ++ tailWord_1978111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978111).length < 2 ^ (prefixWord ++ tailWord_1978111).sum := by decide
  have hdescent : baseEnd_1978111 < baseStart_1978111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978122 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_1978122 : Nat := 118140960795 + 1978122 * 2 ^ 59
def prefixEnd_1978122 : Nat := 4983230072969 + 3 ^ 40 * 1978122 * 2
def baseEnd_1978122 : Nat := 1015727379233214822277789

theorem tailTrace_1978122 : CollatzResearch.WordTrace tailWord_1978122 prefixEnd_1978122 1015727379233214822277789 := by
  unfold tailWord_1978122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18037009134902326296546155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48098691026406203457456413 18037009134902326296546155)
  ·
    refine ⟨27055513702353489444819233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18037009134902326296546155 27055513702353489444819233)
    ·
      refine ⟨20291635276765117083614425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27055513702353489444819233 20291635276765117083614425)
      ·
        refine ⟨15218726457573837812710819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20291635276765117083614425 15218726457573837812710819)
        ·
          refine ⟨22828089686360756719066229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15218726457573837812710819 22828089686360756719066229)
          ·
            refine ⟨2140133408096320942412459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22828089686360756719066229 2140133408096320942412459)
            ·
              refine ⟨3210200112144481413618689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140133408096320942412459 3210200112144481413618689)
              ·
                refine ⟨2407650084108361060214017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210200112144481413618689 2407650084108361060214017)
                ·
                  refine ⟨1805737563081270795160513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2407650084108361060214017 1805737563081270795160513)
                  ·
                    refine ⟨1354303172310953096370385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1805737563081270795160513 1354303172310953096370385)
                    ·
                      refine ⟨1015727379233214822277789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354303172310953096370385 1015727379233214822277789)
                      ·
                        rfl

theorem cell23_1978122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_1978122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978122 prefixEnd_1978122 := by exact prefixLift 1978122
  have htrace : WordTrace (prefixWord ++ tailWord_1978122) baseStart_1978122 baseEnd_1978122 := by
    simpa [prefixWord, tailWord_1978122, baseEnd_1978122] using wordTrace_append hprefix tailTrace_1978122
  have hstable : (prefixWord ++ tailWord_1978122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978122).length < 2 ^ (prefixWord ++ tailWord_1978122).sum := by decide
  have hdescent : baseEnd_1978122 < baseStart_1978122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978131 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 2, 5, 2]
def baseStart_1978131 : Nat := 118140960795 + 1978131 * 2 ^ 59
def prefixEnd_1978131 : Nat := 4983230072969 + 3 ^ 40 * 1978131 * 2
def baseEnd_1978131 : Nat := 1015732000559105287065247

theorem tailTrace_1978131 : CollatzResearch.WordTrace tailWord_1978131 prefixEnd_1978131 1015732000559105287065247 := by
  unfold tailWord_1978131
  simp only [CollatzResearch.WordTrace]
  refine ⟨72148364796576699723262247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48098909864384466482174831 72148364796576699723262247)
  ·
    refine ⟨108222547194865049584893371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72148364796576699723262247 108222547194865049584893371)
    ·
      refine ⟨162333820792297574377340057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108222547194865049584893371 162333820792297574377340057)
      ·
        refine ⟨121750365594223180783005043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162333820792297574377340057 121750365594223180783005043)
        ·
          refine ⟨182625548391334771174507565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121750365594223180783005043 182625548391334771174507565)
          ·
            refine ⟨68484580646750539190440337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182625548391334771174507565 68484580646750539190440337)
            ·
              refine ⟨51363435485062904392830253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68484580646750539190440337 51363435485062904392830253)
              ·
                refine ⟨19261288306898589147311345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51363435485062904392830253 19261288306898589147311345)
                ·
                  refine ⟨14445966230173941860483509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19261288306898589147311345 14445966230173941860483509)
                  ·
                    refine ⟨1354309334078807049420329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14445966230173941860483509 1354309334078807049420329)
                    ·
                      refine ⟨1015732000559105287065247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354309334078807049420329 1015732000559105287065247)
                      ·
                        rfl

theorem cell23_1978131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5, 2].length) (baseStart_1978131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978131 prefixEnd_1978131 := by exact prefixLift 1978131
  have htrace : WordTrace (prefixWord ++ tailWord_1978131) baseStart_1978131 baseEnd_1978131 := by
    simpa [prefixWord, tailWord_1978131, baseEnd_1978131] using wordTrace_append hprefix tailTrace_1978131
  have hstable : (prefixWord ++ tailWord_1978131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978131).length < 2 ^ (prefixWord ++ tailWord_1978131).sum := by decide
  have hdescent : baseEnd_1978131 < baseStart_1978131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978161 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1978161 : Nat := 118140960795 + 1978161 * 2 ^ 59
def prefixEnd_1978161 : Nat := 4983230072969 + 3 ^ 40 * 1978161 * 2
def baseEnd_1978161 : Nat := 1015747404978740169690109

theorem tailTrace_1978161 : CollatzResearch.WordTrace tailWord_1978161 prefixEnd_1978161 1015747404978740169690109 := by
  unfold tailWord_1978161
  simp only [CollatzResearch.WordTrace]
  refine ⟨72149458986468014846854337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48099639324312009897902891 72149458986468014846854337)
  ·
    refine ⟨54112094239851011135140753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72149458986468014846854337 54112094239851011135140753)
    ·
      refine ⟨40584070679888258351355565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54112094239851011135140753 40584070679888258351355565)
      ·
        refine ⟨15219026504958096881758337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40584070679888258351355565 15219026504958096881758337)
        ·
          refine ⟨11414269878718572661318753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15219026504958096881758337 11414269878718572661318753)
          ·
            refine ⟨8560702409038929495989065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11414269878718572661318753 8560702409038929495989065)
            ·
              refine ⟨6420526806779197121991799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8560702409038929495989065 6420526806779197121991799)
              ·
                refine ⟨9630790210168795682987699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6420526806779197121991799 9630790210168795682987699)
                ·
                  refine ⟨14446185315253193524481549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9630790210168795682987699 14446185315253193524481549)
                  ·
                    refine ⟨5417319493219947571680581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14446185315253193524481549 5417319493219947571680581)
                    ·
                      refine ⟨1015747404978740169690109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5417319493219947571680581 1015747404978740169690109)
                      ·
                        rfl

theorem cell23_1978161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1978161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978161 prefixEnd_1978161 := by exact prefixLift 1978161
  have htrace : WordTrace (prefixWord ++ tailWord_1978161) baseStart_1978161 baseEnd_1978161 := by
    simpa [prefixWord, tailWord_1978161, baseEnd_1978161] using wordTrace_append hprefix tailTrace_1978161
  have hstable : (prefixWord ++ tailWord_1978161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978161).length < 2 ^ (prefixWord ++ tailWord_1978161).sum := by decide
  have hdescent : baseEnd_1978161 < baseStart_1978161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978201 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 6]
def baseStart_1978201 : Nat := 118140960795 + 1978201 * 2 ^ 59
def prefixEnd_1978201 : Nat := 4983230072969 + 3 ^ 40 * 1978201 * 2
def baseEnd_1978201 : Nat := 112863104911657779243325

theorem tailTrace_1978201 : CollatzResearch.WordTrace tailWord_1978201 prefixEnd_1978201 112863104911657779243325 := by
  unfold tailWord_1978201
  simp only [CollatzResearch.WordTrace]
  refine ⟨72150917906323101678310457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48100611937548734452206971 72150917906323101678310457)
  ·
    refine ⟨54113188429742326258732843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72150917906323101678310457 54113188429742326258732843)
    ·
      refine ⟨81169782644613489388099265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54113188429742326258732843 81169782644613489388099265)
      ·
        refine ⟨60877336983460117041074449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81169782644613489388099265 60877336983460117041074449)
        ·
          refine ⟨45658002737595087780805837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60877336983460117041074449 45658002737595087780805837)
          ·
            refine ⟨17121751026598157917802189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45658002737595087780805837 17121751026598157917802189)
            ·
              refine ⟨6420656634974309219175821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17121751026598157917802189 6420656634974309219175821)
              ·
                refine ⟨2407746238115365957190933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6420656634974309219175821 2407746238115365957190933)
                ·
                  refine ⟨112863104911657779243325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2407746238115365957190933 112863104911657779243325)
                  ·
                    rfl

theorem cell23_1978201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_1978201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978201 prefixEnd_1978201 := by exact prefixLift 1978201
  have htrace : WordTrace (prefixWord ++ tailWord_1978201) baseStart_1978201 baseEnd_1978201 := by
    simpa [prefixWord, tailWord_1978201, baseEnd_1978201] using wordTrace_append hprefix tailTrace_1978201
  have hstable : (prefixWord ++ tailWord_1978201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978201).length < 2 ^ (prefixWord ++ tailWord_1978201).sum := by decide
  have hdescent : baseEnd_1978201 < baseStart_1978201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978279 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_1978279 : Nat := 118140960795 + 1978279 * 2 ^ 59
def prefixEnd_1978279 : Nat := 4983230072969 + 3 ^ 40 * 1978279 * 2
def baseEnd_1978279 : Nat := 1015807995695970708014567

theorem tailTrace_1978279 : CollatzResearch.WordTrace tailWord_1978279 prefixEnd_1978279 1015807995695970708014567 := by
  unfold tailWord_1978279
  simp only [CollatzResearch.WordTrace]
  refine ⟨72153762800040520999649891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48102508533360347333099927 72153762800040520999649891)
  ·
    refine ⟨108230644200060781499474837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72153762800040520999649891 108230644200060781499474837)
    ·
      refine ⟨5073311446877849132787883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108230644200060781499474837 5073311446877849132787883)
      ·
        refine ⟨7609967170316773699181825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073311446877849132787883 7609967170316773699181825)
        ·
          refine ⟨5707475377737580274386369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7609967170316773699181825 5707475377737580274386369)
          ·
            refine ⟨4280606533303185205789777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5707475377737580274386369 4280606533303185205789777)
            ·
              refine ⟨3210454899977388904342333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4280606533303185205789777 3210454899977388904342333)
              ·
                refine ⟨1203920587491520839128375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3210454899977388904342333 1203920587491520839128375)
                ·
                  refine ⟨1805880881237281258692563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203920587491520839128375 1805880881237281258692563)
                  ·
                    refine ⟨2708821321855921888038845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1805880881237281258692563 2708821321855921888038845)
                    ·
                      refine ⟨1015807995695970708014567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2708821321855921888038845 1015807995695970708014567)
                      ·
                        rfl

theorem cell23_1978279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_1978279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978279 prefixEnd_1978279 := by exact prefixLift 1978279
  have htrace : WordTrace (prefixWord ++ tailWord_1978279) baseStart_1978279 baseEnd_1978279 := by
    simpa [prefixWord, tailWord_1978279, baseEnd_1978279] using wordTrace_append hprefix tailTrace_1978279
  have hstable : (prefixWord ++ tailWord_1978279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978279).length < 2 ^ (prefixWord ++ tailWord_1978279).sum := by decide
  have hdescent : baseEnd_1978279 < baseStart_1978279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978281 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_1978281 : Nat := 118140960795 + 1978281 * 2 ^ 59
def prefixEnd_1978281 : Nat := 4983230072969 + 3 ^ 40 * 1978281 * 2
def baseEnd_1978281 : Nat := 1015809022657279700189557

theorem tailTrace_1978281 : CollatzResearch.WordTrace tailWord_1978281 prefixEnd_1978281 1015809022657279700189557 := by
  unfold tailWord_1978281
  simp only [CollatzResearch.WordTrace]
  refine ⟨72153835746033275341222697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48102557164022183560815131 72153835746033275341222697)
  ·
    refine ⟨54115376809524956505917023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72153835746033275341222697 54115376809524956505917023)
    ·
      refine ⟨81173065214287434758875535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54115376809524956505917023 81173065214287434758875535)
      ·
        refine ⟨121759597821431152138313303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81173065214287434758875535 121759597821431152138313303)
        ·
          refine ⟨182639396732146728207469955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121759597821431152138313303 182639396732146728207469955)
          ·
            refine ⟨273959095098220092311204933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182639396732146728207469955 273959095098220092311204933)
            ·
              refine ⟨51367330330916267308350925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273959095098220092311204933 51367330330916267308350925)
              ·
                refine ⟨19262748874093600240631597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51367330330916267308350925 19262748874093600240631597)
                ·
                  refine ⟨7223530827785100090236849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19262748874093600240631597 7223530827785100090236849)
                  ·
                    refine ⟨5417648120838825067677637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7223530827785100090236849 5417648120838825067677637)
                    ·
                      refine ⟨1015809022657279700189557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5417648120838825067677637 1015809022657279700189557)
                      ·
                        rfl

theorem cell23_1978281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_1978281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978281 prefixEnd_1978281 := by exact prefixLift 1978281
  have htrace : WordTrace (prefixWord ++ tailWord_1978281) baseStart_1978281 baseEnd_1978281 := by
    simpa [prefixWord, tailWord_1978281, baseEnd_1978281] using wordTrace_append hprefix tailTrace_1978281
  have hstable : (prefixWord ++ tailWord_1978281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978281).length < 2 ^ (prefixWord ++ tailWord_1978281).sum := by decide
  have hdescent : baseEnd_1978281 < baseStart_1978281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978286 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_1978286 : Nat := 118140960795 + 1978286 * 2 ^ 59
def prefixEnd_1978286 : Nat := 4983230072969 + 3 ^ 40 * 1978286 * 2
def baseEnd_1978286 : Nat := 112867954451172464514115

theorem tailTrace_1978286 : CollatzResearch.WordTrace tailWord_1978286 prefixEnd_1978286 112867954451172464514115 := by
  unfold tailWord_1978286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019252263876895149394339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48102678740676774130103141 9019252263876895149394339)
  ·
    refine ⟨13528878395815342724091509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9019252263876895149394339 13528878395815342724091509)
    ·
      refine ⟨1268332349607688380383579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13528878395815342724091509 1268332349607688380383579)
      ·
        refine ⟨1902498524411532570575369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268332349607688380383579 1902498524411532570575369)
        ·
          refine ⟨1426873893308649427931527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1902498524411532570575369 1426873893308649427931527)
          ·
            refine ⟨2140310839962974141897291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426873893308649427931527 2140310839962974141897291)
            ·
              refine ⟨3210466259944461212845937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140310839962974141897291 3210466259944461212845937)
              ·
                refine ⟨2407849694958345909634453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210466259944461212845937 2407849694958345909634453)
                ·
                  refine ⟨112867954451172464514115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2407849694958345909634453 112867954451172464514115)
                  ·
                    rfl

theorem cell23_1978286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_1978286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978286 prefixEnd_1978286 := by exact prefixLift 1978286
  have htrace : WordTrace (prefixWord ++ tailWord_1978286) baseStart_1978286 baseEnd_1978286 := by
    simpa [prefixWord, tailWord_1978286, baseEnd_1978286] using wordTrace_append hprefix tailTrace_1978286
  have hstable : (prefixWord ++ tailWord_1978286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978286).length < 2 ^ (prefixWord ++ tailWord_1978286).sum := by decide
  have hdescent : baseEnd_1978286 < baseStart_1978286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978302 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_1978302 : Nat := 118140960795 + 1978302 * 2 ^ 59
def prefixEnd_1978302 : Nat := 4983230072969 + 3 ^ 40 * 1978302 * 2
def baseEnd_1978302 : Nat := 1015819805751024118026961

theorem tailTrace_1978302 : CollatzResearch.WordTrace tailWord_1978302 prefixEnd_1978302 1015819805751024118026961 := by
  unfold tailWord_1978302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019325209869649490967145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48103067785971463951824773 9019325209869649490967145)
  ·
    refine ⟨6764493907402237118225359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9019325209869649490967145 6764493907402237118225359)
    ·
      refine ⟨10146740861103355677338039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6764493907402237118225359 10146740861103355677338039)
      ·
        refine ⟨15220111291655033516007059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10146740861103355677338039 15220111291655033516007059)
        ·
          refine ⟨22830166937482550274010589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15220111291655033516007059 22830166937482550274010589)
          ·
            refine ⟨8561312601555956352753971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22830166937482550274010589 8561312601555956352753971)
            ·
              refine ⟨12841968902333934529130957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561312601555956352753971 12841968902333934529130957)
              ·
                refine ⟨4815738338375225448424109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12841968902333934529130957 4815738338375225448424109)
                ·
                  refine ⟨1805901876890709543159041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4815738338375225448424109 1805901876890709543159041)
                  ·
                    refine ⟨1354426407668032157369281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1805901876890709543159041 1354426407668032157369281)
                    ·
                      refine ⟨1015819805751024118026961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354426407668032157369281 1015819805751024118026961)
                      ·
                        rfl

theorem cell23_1978302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_1978302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978302 prefixEnd_1978302 := by exact prefixLift 1978302
  have htrace : WordTrace (prefixWord ++ tailWord_1978302) baseStart_1978302 baseEnd_1978302 := by
    simpa [prefixWord, tailWord_1978302, baseEnd_1978302] using wordTrace_append hprefix tailTrace_1978302
  have hstable : (prefixWord ++ tailWord_1978302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978302).length < 2 ^ (prefixWord ++ tailWord_1978302).sum := by decide
  have hdescent : baseEnd_1978302 < baseStart_1978302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978312 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1978312 : Nat := 118140960795 + 1978312 * 2 ^ 59
def prefixEnd_1978312 : Nat := 4983230072969 + 3 ^ 40 * 1978312 * 2
def baseEnd_1978312 : Nat := 338608313519189692967305

theorem tailTrace_1978312 : CollatzResearch.WordTrace tailWord_1978312 prefixEnd_1978312 338608313519189692967305 := by
  unfold tailWord_1978312
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077483204460483817800595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48103310939280645090400793 36077483204460483817800595)
  ·
    refine ⟨54116224806690725726700893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36077483204460483817800595 54116224806690725726700893)
    ·
      refine ⟨20293584302509022147512835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54116224806690725726700893 20293584302509022147512835)
      ·
        refine ⟨30440376453763533221269253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20293584302509022147512835 30440376453763533221269253)
        ·
          refine ⟨5707570585080662478987985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30440376453763533221269253 5707570585080662478987985)
          ·
            refine ⟨4280677938810496859240989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5707570585080662478987985 4280677938810496859240989)
            ·
              refine ⟨1605254227053936322215371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4280677938810496859240989 1605254227053936322215371)
              ·
                refine ⟨2407881340580904483323057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605254227053936322215371 2407881340580904483323057)
                ·
                  refine ⟨1805911005435678362492293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2407881340580904483323057 1805911005435678362492293)
                  ·
                    refine ⟨338608313519189692967305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1805911005435678362492293 338608313519189692967305)
                    ·
                      rfl

theorem cell23_1978312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1978312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978312 prefixEnd_1978312 := by exact prefixLift 1978312
  have htrace : WordTrace (prefixWord ++ tailWord_1978312) baseStart_1978312 baseEnd_1978312 := by
    simpa [prefixWord, tailWord_1978312, baseEnd_1978312] using wordTrace_append hprefix tailTrace_1978312
  have hstable : (prefixWord ++ tailWord_1978312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978312).length < 2 ^ (prefixWord ++ tailWord_1978312).sum := by decide
  have hdescent : baseEnd_1978312 < baseStart_1978312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978325 : List Nat := [1, 3, 2, 3, 2, 3, 2, 7]
def baseStart_1978325 : Nat := 118140960795 + 1978325 * 2 ^ 59
def prefixEnd_1978325 : Nat := 4983230072969 + 3 ^ 40 * 1978325 * 2
def baseEnd_1978325 : Nat := 37623393178002871408865

theorem tailTrace_1978325 : CollatzResearch.WordTrace tailWord_1978325 prefixEnd_1978325 37623393178002871408865 := by
  unfold tailWord_1978325
  simp only [CollatzResearch.WordTrace]
  refine ⟨72155440557873870855824429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48103627038582580570549619 72155440557873870855824429)
  ·
    refine ⟨27058290209202701570934161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72155440557873870855824429 27058290209202701570934161)
    ·
      refine ⟨20293717656902026178200621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27058290209202701570934161 20293717656902026178200621)
      ·
        refine ⟨7610144121338259816825233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20293717656902026178200621 7610144121338259816825233)
        ·
          refine ⟨5707608091003694862618925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7610144121338259816825233 5707608091003694862618925)
          ·
            refine ⟨2140353034126385573482097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5707608091003694862618925 2140353034126385573482097)
            ·
              refine ⟨1605264775594789180111573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140353034126385573482097 1605264775594789180111573)
              ·
                refine ⟨37623393178002871408865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1605264775594789180111573 37623393178002871408865)
                ·
                  rfl

theorem cell23_1978325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 7].length) (baseStart_1978325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978325 prefixEnd_1978325 := by exact prefixLift 1978325
  have htrace : WordTrace (prefixWord ++ tailWord_1978325) baseStart_1978325 baseEnd_1978325 := by
    simpa [prefixWord, tailWord_1978325, baseEnd_1978325] using wordTrace_append hprefix tailTrace_1978325
  have hstable : (prefixWord ++ tailWord_1978325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978325).length < 2 ^ (prefixWord ++ tailWord_1978325).sum := by decide
  have hdescent : baseEnd_1978325 < baseStart_1978325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978335 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 3]
def baseStart_1978335 : Nat := 118140960795 + 1978335 * 2 ^ 59
def prefixEnd_1978335 : Nat := 4983230072969 + 3 ^ 40 * 1978335 * 2
def baseEnd_1978335 : Nat := 1015836750612622488914309

theorem tailTrace_1978335 : CollatzResearch.WordTrace tailWord_1978335 prefixEnd_1978335 1015836750612622488914309 := by
  unfold tailWord_1978335
  simp only [CollatzResearch.WordTrace]
  refine ⟨72155805287837642563688459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48103870191891761709125639 72155805287837642563688459)
  ·
    refine ⟨108233707931756463845532689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72155805287837642563688459 108233707931756463845532689)
    ·
      refine ⟨81175280948817347884149517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108233707931756463845532689 81175280948817347884149517)
      ·
        refine ⟨30440730355806505456556069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81175280948817347884149517 30440730355806505456556069)
        ·
          refine ⟨5707636941713719773104263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30440730355806505456556069 5707636941713719773104263)
          ·
            refine ⟨8561455412570579659656395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707636941713719773104263 8561455412570579659656395)
            ·
              refine ⟨12842183118855869489484593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8561455412570579659656395 12842183118855869489484593)
              ·
                refine ⟨9631637339141902117113445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12842183118855869489484593 9631637339141902117113445)
                ·
                  refine ⟨1805932001089106646958771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9631637339141902117113445 1805932001089106646958771)
                  ·
                    refine ⟨2708898001633659970438157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1805932001089106646958771 2708898001633659970438157)
                    ·
                      refine ⟨1015836750612622488914309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2708898001633659970438157 1015836750612622488914309)
                      ·
                        rfl

theorem cell23_1978335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_1978335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978335 prefixEnd_1978335 := by exact prefixLift 1978335
  have htrace : WordTrace (prefixWord ++ tailWord_1978335) baseStart_1978335 baseEnd_1978335 := by
    simpa [prefixWord, tailWord_1978335, baseEnd_1978335] using wordTrace_append hprefix tailTrace_1978335
  have hstable : (prefixWord ++ tailWord_1978335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978335).length < 2 ^ (prefixWord ++ tailWord_1978335).sum := by decide
  have hdescent : baseEnd_1978335 < baseStart_1978335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978371 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_1978371 : Nat := 118140960795 + 1978371 * 2 ^ 59
def prefixEnd_1978371 : Nat := 4983230072969 + 3 ^ 40 * 1978371 * 2
def baseEnd_1978371 : Nat := 1015855235916184348064143

theorem tailTrace_1978371 : CollatzResearch.WordTrace tailWord_1978371 prefixEnd_1978371 1015855235916184348064143 := by
  unfold tailWord_1978371
  simp only [CollatzResearch.WordTrace]
  refine ⟨72157118315707220711998967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48104745543804813807999311 72157118315707220711998967)
  ·
    refine ⟨108235677473560831067998451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72157118315707220711998967 108235677473560831067998451)
    ·
      refine ⟨162353516210341246601997677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108235677473560831067998451 162353516210341246601997677)
      ·
        refine ⟨60882568578877967475749129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162353516210341246601997677 60882568578877967475749129)
        ·
          refine ⟨45661926434158475606811847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60882568578877967475749129 45661926434158475606811847)
          ·
            refine ⟨68492889651237713410217771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45661926434158475606811847 68492889651237713410217771)
            ·
              refine ⟨102739334476856570115326657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68492889651237713410217771 102739334476856570115326657)
              ·
                refine ⟨77054500857642427586494993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102739334476856570115326657 77054500857642427586494993)
                ·
                  refine ⟨57790875643231820689871245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77054500857642427586494993 57790875643231820689871245)
                  ·
                    refine ⟨21671578366211932758701717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57790875643231820689871245 21671578366211932758701717)
                    ·
                      refine ⟨1015855235916184348064143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21671578366211932758701717 1015855235916184348064143)
                      ·
                        rfl

theorem cell23_1978371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_1978371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978371 prefixEnd_1978371 := by exact prefixLift 1978371
  have htrace : WordTrace (prefixWord ++ tailWord_1978371) baseStart_1978371 baseEnd_1978371 := by
    simpa [prefixWord, tailWord_1978371, baseEnd_1978371] using wordTrace_append hprefix tailTrace_1978371
  have hstable : (prefixWord ++ tailWord_1978371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978371).length < 2 ^ (prefixWord ++ tailWord_1978371).sum := by decide
  have hdescent : baseEnd_1978371 < baseStart_1978371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978428 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1978428 : Nat := 118140960795 + 1978428 * 2 ^ 59
def prefixEnd_1978428 : Nat := 4983230072969 + 3 ^ 40 * 1978428 * 2
def baseEnd_1978428 : Nat := 338628168104496875017127

theorem tailTrace_1978428 : CollatzResearch.WordTrace tailWord_1978428 prefixEnd_1978428 338628168104496875017127 := by
  unfold tailWord_1978428
  simp only [CollatzResearch.WordTrace]
  refine ⟨36079598638250359723411969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48106131517667146297882625 36079598638250359723411969)
  ·
    refine ⟨27059698978687769792558977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36079598638250359723411969 27059698978687769792558977)
    ·
      refine ⟨20294774234015827344419233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27059698978687769792558977 20294774234015827344419233)
      ·
        refine ⟨15221080675511870508314425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20294774234015827344419233 15221080675511870508314425)
        ·
          refine ⟨11415810506633902881235819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15221080675511870508314425 11415810506633902881235819)
          ·
            refine ⟨17123715759950854321853729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415810506633902881235819 17123715759950854321853729)
            ·
              refine ⟨12842786819963140741390297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17123715759950854321853729 12842786819963140741390297)
              ·
                refine ⟨9632090114972355556042723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12842786819963140741390297 9632090114972355556042723)
                ·
                  refine ⟨14448135172458533334064085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632090114972355556042723 14448135172458533334064085)
                  ·
                    refine ⟨338628168104496875017127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14448135172458533334064085 338628168104496875017127)
                    ·
                      rfl

theorem cell23_1978428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1978428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978428 prefixEnd_1978428 := by exact prefixLift 1978428
  have htrace : WordTrace (prefixWord ++ tailWord_1978428) baseStart_1978428 baseEnd_1978428 := by
    simpa [prefixWord, tailWord_1978428, baseEnd_1978428] using wordTrace_append hprefix tailTrace_1978428
  have hstable : (prefixWord ++ tailWord_1978428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978428).length < 2 ^ (prefixWord ++ tailWord_1978428).sum := by decide
  have hdescent : baseEnd_1978428 < baseStart_1978428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978445 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1978445 : Nat := 118140960795 + 1978445 * 2 ^ 59
def prefixEnd_1978445 : Nat := 4983230072969 + 3 ^ 40 * 1978445 * 2
def baseEnd_1978445 : Nat := 338631077828205686179601

theorem tailTrace_1978445 : CollatzResearch.WordTrace tailWord_1978445 prefixEnd_1978445 338631077828205686179601 := by
  unfold tailWord_1978445
  simp only [CollatzResearch.WordTrace]
  refine ⟨72159817317439131350192789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48106544878292754233461859 72159817317439131350192789)
  ·
    refine ⟨3382491436754959282040287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72159817317439131350192789 3382491436754959282040287)
    ·
      refine ⟨5073737155132438923060431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382491436754959282040287 5073737155132438923060431)
      ·
        refine ⟨7610605732698658384590647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073737155132438923060431 7610605732698658384590647)
        ·
          refine ⟨11415908599047987576885971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610605732698658384590647 11415908599047987576885971)
          ·
            refine ⟨17123862898571981365328957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11415908599047987576885971 17123862898571981365328957)
            ·
              refine ⟨6421448586964493011998359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17123862898571981365328957 6421448586964493011998359)
              ·
                refine ⟨9632172880446739517997539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421448586964493011998359 9632172880446739517997539)
                ·
                  refine ⟨14448259320670109276996309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9632172880446739517997539 14448259320670109276996309)
                  ·
                    refine ⟨338631077828205686179601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14448259320670109276996309 338631077828205686179601)
                    ·
                      rfl

theorem cell23_1978445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1978445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978445 prefixEnd_1978445 := by exact prefixLift 1978445
  have htrace : WordTrace (prefixWord ++ tailWord_1978445) baseStart_1978445 baseEnd_1978445 := by
    simpa [prefixWord, tailWord_1978445, baseEnd_1978445] using wordTrace_append hprefix tailTrace_1978445
  have hstable : (prefixWord ++ tailWord_1978445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978445).length < 2 ^ (prefixWord ++ tailWord_1978445).sum := by decide
  have hdescent : baseEnd_1978445 < baseStart_1978445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978468 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1978468 : Nat := 118140960795 + 1978468 * 2 ^ 59
def prefixEnd_1978468 : Nat := 4983230072969 + 3 ^ 40 * 1978468 * 2
def baseEnd_1978468 : Nat := 1015905043539670468551197

theorem tailTrace_1978468 : CollatzResearch.WordTrace tailWord_1978468 prefixEnd_1978468 1015905043539670468551197 := by
  unfold tailWord_1978468
  simp only [CollatzResearch.WordTrace]
  refine ⟨36080328098177903139140029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48107104130903870852186705 36080328098177903139140029)
  ·
    refine ⟨13530123036816713677177511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36080328098177903139140029 13530123036816713677177511)
    ·
      refine ⟨20295184555225070515766267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13530123036816713677177511 20295184555225070515766267)
      ·
        refine ⟨30442776832837605773649401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20295184555225070515766267 30442776832837605773649401)
        ·
          refine ⟨22832082624628204330237051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30442776832837605773649401 22832082624628204330237051)
          ·
            refine ⟨34248123936942306495355577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832082624628204330237051 34248123936942306495355577)
            ·
              refine ⟨25686092952706729871516683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34248123936942306495355577 25686092952706729871516683)
              ·
                refine ⟨38529139429060094807275025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25686092952706729871516683 38529139429060094807275025)
                ·
                  refine ⟨28896854571795071105456269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38529139429060094807275025 28896854571795071105456269)
                  ·
                    refine ⟨10836320464423151664546101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28896854571795071105456269 10836320464423151664546101)
                    ·
                      refine ⟨1015905043539670468551197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10836320464423151664546101 1015905043539670468551197)
                      ·
                        rfl

theorem cell23_1978468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1978468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978468 prefixEnd_1978468 := by exact prefixLift 1978468
  have htrace : WordTrace (prefixWord ++ tailWord_1978468) baseStart_1978468 baseEnd_1978468 := by
    simpa [prefixWord, tailWord_1978468, baseEnd_1978468] using wordTrace_append hprefix tailTrace_1978468
  have hstable : (prefixWord ++ tailWord_1978468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978468).length < 2 ^ (prefixWord ++ tailWord_1978468).sum := by decide
  have hdescent : baseEnd_1978468 < baseStart_1978468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978482 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_1978482 : Nat := 118140960795 + 1978482 * 2 ^ 59
def prefixEnd_1978482 : Nat := 4983230072969 + 3 ^ 40 * 1978482 * 2
def baseEnd_1978482 : Nat := 1015912232268833413776133

theorem tailTrace_1978482 : CollatzResearch.WordTrace tailWord_1978482 prefixEnd_1978482 1015912232268833413776133 := by
  unfold tailWord_1978482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040291704576271667322425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48107444545536724446193133 18040291704576271667322425)
  ·
    refine ⟨13530218778432203750491819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18040291704576271667322425 13530218778432203750491819)
    ·
      refine ⟨20295328167648305625737729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13530218778432203750491819 20295328167648305625737729)
      ·
        refine ⟨15221496125736229219303297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20295328167648305625737729 15221496125736229219303297)
        ·
          refine ⟨11416122094302171914477473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15221496125736229219303297 11416122094302171914477473)
          ·
            refine ⟨8562091570726628935858105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11416122094302171914477473 8562091570726628935858105)
            ·
              refine ⟨6421568678044971701893579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8562091570726628935858105 6421568678044971701893579)
              ·
                refine ⟨9632353017067457552840369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421568678044971701893579 9632353017067457552840369)
                ·
                  refine ⟨7224264762800593164630277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9632353017067457552840369 7224264762800593164630277)
                  ·
                    refine ⟨1354549643025111218368177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7224264762800593164630277 1354549643025111218368177)
                    ·
                      refine ⟨1015912232268833413776133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354549643025111218368177 1015912232268833413776133)
                      ·
                        rfl

theorem cell23_1978482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_1978482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978482 prefixEnd_1978482 := by exact prefixLift 1978482
  have htrace : WordTrace (prefixWord ++ tailWord_1978482) baseStart_1978482 baseEnd_1978482 := by
    simpa [prefixWord, tailWord_1978482, baseEnd_1978482] using wordTrace_append hprefix tailTrace_1978482
  have hstable : (prefixWord ++ tailWord_1978482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978482).length < 2 ^ (prefixWord ++ tailWord_1978482).sum := by decide
  have hdescent : baseEnd_1978482 < baseStart_1978482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978526 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1978526 : Nat := 118140960795 + 1978526 * 2 ^ 59
def prefixEnd_1978526 : Nat := 4983230072969 + 3 ^ 40 * 1978526 * 2
def baseEnd_1978526 : Nat := 338644941805877080541977

theorem tailTrace_1978526 : CollatzResearch.WordTrace tailWord_1978526 prefixEnd_1978526 338644941805877080541977 := by
  unfold tailWord_1978526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020346453768210272986429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48108514420097121455927621 9020346453768210272986429)
  ·
    refine ⟨3382629920163078852369911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9020346453768210272986429 3382629920163078852369911)
    ·
      refine ⟨5073944880244618278554867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382629920163078852369911 5073944880244618278554867)
      ·
        refine ⟨7610917320366927417832301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073944880244618278554867 7610917320366927417832301)
        ·
          refine ⟨2854093995137597781687113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7610917320366927417832301 2854093995137597781687113)
          ·
            refine ⟨2140570496353198336265335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854093995137597781687113 2140570496353198336265335)
            ·
              refine ⟨3210855744529797504398003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140570496353198336265335 3210855744529797504398003)
              ·
                refine ⟨4816283616794696256597005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210855744529797504398003 4816283616794696256597005)
                ·
                  refine ⟨1806106356298011096223877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4816283616794696256597005 1806106356298011096223877)
                  ·
                    refine ⟨338644941805877080541977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1806106356298011096223877 338644941805877080541977)
                    ·
                      rfl

theorem cell23_1978526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1978526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978526 prefixEnd_1978526 := by exact prefixLift 1978526
  have htrace : WordTrace (prefixWord ++ tailWord_1978526) baseStart_1978526 baseEnd_1978526 := by
    simpa [prefixWord, tailWord_1978526, baseEnd_1978526] using wordTrace_append hprefix tailTrace_1978526
  have hstable : (prefixWord ++ tailWord_1978526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978526).length < 2 ^ (prefixWord ++ tailWord_1978526).sum := by decide
  have hdescent : baseEnd_1978526 < baseStart_1978526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978555 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 4]
def baseStart_1978555 : Nat := 118140960795 + 1978555 * 2 ^ 59
def prefixEnd_1978555 : Nat := 4983230072969 + 3 ^ 40 * 1978555 * 2
def baseEnd_1978555 : Nat := 1015949716356611628163297

theorem tailTrace_1978555 : CollatzResearch.WordTrace tailWord_1978555 prefixEnd_1978555 1015949716356611628163297 := by
  unfold tailWord_1978555
  simp only [CollatzResearch.WordTrace]
  refine ⟨72163829347040620136697119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48109219564693746757798079 72163829347040620136697119)
  ·
    refine ⟨108245744020560930205045679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72163829347040620136697119 108245744020560930205045679)
    ·
      refine ⟨162368616030841395307568519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108245744020560930205045679 162368616030841395307568519)
      ·
        refine ⟨243552924046262092961352779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162368616030841395307568519 243552924046262092961352779)
        ·
          refine ⟨365329386069393139442029169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243552924046262092961352779 365329386069393139442029169)
          ·
            refine ⟨273997039552044854581521877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365329386069393139442029169 273997039552044854581521877)
            ·
              refine ⟨6421805614501051279254419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 273997039552044854581521877 6421805614501051279254419)
              ·
                refine ⟨9632708421751576918881629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6421805614501051279254419 9632708421751576918881629)
                ·
                  refine ⟨3612265658156841344580611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9632708421751576918881629 3612265658156841344580611)
                  ·
                    refine ⟨5418398487235262016870917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612265658156841344580611 5418398487235262016870917)
                    ·
                      refine ⟨1015949716356611628163297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5418398487235262016870917 1015949716356611628163297)
                      ·
                        rfl

theorem cell23_1978555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 4].length) (baseStart_1978555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978555 prefixEnd_1978555 := by exact prefixLift 1978555
  have htrace : WordTrace (prefixWord ++ tailWord_1978555) baseStart_1978555 baseEnd_1978555 := by
    simpa [prefixWord, tailWord_1978555, baseEnd_1978555] using wordTrace_append hprefix tailTrace_1978555
  have hstable : (prefixWord ++ tailWord_1978555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978555).length < 2 ^ (prefixWord ++ tailWord_1978555).sum := by decide
  have hdescent : baseEnd_1978555 < baseStart_1978555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978565 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_1978565 : Nat := 118140960795 + 1978565 * 2 ^ 59
def prefixEnd_1978565 : Nat := 4983230072969 + 3 ^ 40 * 1978565 * 2
def baseEnd_1978565 : Nat := 338651617054385529679417

theorem tailTrace_1978565 : CollatzResearch.WordTrace tailWord_1978565 prefixEnd_1978565 338651617054385529679417 := by
  unfold tailWord_1978565
  simp only [CollatzResearch.WordTrace]
  refine ⟨72164194077004391844561149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48109462718002927896374099 72164194077004391844561149)
  ·
    refine ⟨27061572778876646941710431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72164194077004391844561149 27061572778876646941710431)
    ·
      refine ⟨40592359168314970412565647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27061572778876646941710431 40592359168314970412565647)
      ·
        refine ⟨60888538752472455618848471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40592359168314970412565647 60888538752472455618848471)
        ·
          refine ⟨91332808128708683428272707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60888538752472455618848471 91332808128708683428272707)
          ·
            refine ⟨136999212193063025142409061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91332808128708683428272707 136999212193063025142409061)
            ·
              refine ⟨25687352286199317214201699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136999212193063025142409061 25687352286199317214201699)
              ·
                refine ⟨38531028429298975821302549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25687352286199317214201699 38531028429298975821302549)
                ·
                  refine ⟨1806141957623389491623557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38531028429298975821302549 1806141957623389491623557)
                  ·
                    refine ⟨338651617054385529679417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1806141957623389491623557 338651617054385529679417)
                    ·
                      rfl

theorem cell23_1978565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_1978565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978565 prefixEnd_1978565 := by exact prefixLift 1978565
  have htrace : WordTrace (prefixWord ++ tailWord_1978565) baseStart_1978565 baseEnd_1978565 := by
    simpa [prefixWord, tailWord_1978565, baseEnd_1978565] using wordTrace_append hprefix tailTrace_1978565
  have hstable : (prefixWord ++ tailWord_1978565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978565).length < 2 ^ (prefixWord ++ tailWord_1978565).sum := by decide
  have hdescent : baseEnd_1978565 < baseStart_1978565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978599 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1978599 : Nat := 118140960795 + 1978599 * 2 ^ 59
def prefixEnd_1978599 : Nat := 4983230072969 + 3 ^ 40 * 1978599 * 2
def baseEnd_1978599 : Nat := 338657436501803152004365

theorem tailTrace_1978599 : CollatzResearch.WordTrace tailWord_1978599 prefixEnd_1978599 338657436501803152004365 := by
  unfold tailWord_1978599
  simp only [CollatzResearch.WordTrace]
  refine ⟨72165434158881215651298851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48110289439254143767532567 72165434158881215651298851)
  ·
    refine ⟨108248151238321823476948277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72165434158881215651298851 108248151238321823476948277)
    ·
      refine ⟨10148264178592670950963901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108248151238321823476948277 10148264178592670950963901)
      ·
        refine ⟨3805599066972251606611463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10148264178592670950963901 3805599066972251606611463)
        ·
          refine ⟨5708398600458377409917195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805599066972251606611463 5708398600458377409917195)
          ·
            refine ⟨8562597900687566114875793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5708398600458377409917195 8562597900687566114875793)
            ·
              refine ⟨6421948425515674586156845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8562597900687566114875793 6421948425515674586156845)
              ·
                refine ⟨2408230659568377969808817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6421948425515674586156845 2408230659568377969808817)
                ·
                  refine ⟨1806172994676283477356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2408230659568377969808817 1806172994676283477356613)
                  ·
                    refine ⟨338657436501803152004365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1806172994676283477356613 338657436501803152004365)
                    ·
                      rfl

theorem cell23_1978599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1978599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978599 prefixEnd_1978599 := by exact prefixLift 1978599
  have htrace : WordTrace (prefixWord ++ tailWord_1978599) baseStart_1978599 baseEnd_1978599 := by
    simpa [prefixWord, tailWord_1978599, baseEnd_1978599] using wordTrace_append hprefix tailTrace_1978599
  have hstable : (prefixWord ++ tailWord_1978599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978599).length < 2 ^ (prefixWord ++ tailWord_1978599).sum := by decide
  have hdescent : baseEnd_1978599 < baseStart_1978599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978602 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1978602 : Nat := 118140960795 + 1978602 * 2 ^ 59
def prefixEnd_1978602 : Nat := 4983230072969 + 3 ^ 40 * 1978602 * 2
def baseEnd_1978602 : Nat := 1015973849947372944275581

theorem tailTrace_1978602 : CollatzResearch.WordTrace tailWord_1978602 prefixEnd_1978602 1015973849947372944275581 := by
  unfold tailWord_1978602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18041385894467586790914515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48110362385246898109105373 18041385894467586790914515)
  ·
    refine ⟨27062078841701380186371773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18041385894467586790914515 27062078841701380186371773)
    ·
      refine ⟨10148279565638017569889415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27062078841701380186371773 10148279565638017569889415)
      ·
        refine ⟨15222419348457026354834123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10148279565638017569889415 15222419348457026354834123)
        ·
          refine ⟨22833629022685539532251185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15222419348457026354834123 22833629022685539532251185)
          ·
            refine ⟨17125221767014154649188389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22833629022685539532251185 17125221767014154649188389)
            ·
              refine ⟨3210979081315153996722823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17125221767014154649188389 3210979081315153996722823)
              ·
                refine ⟨4816468621972730995084235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3210979081315153996722823 4816468621972730995084235)
                ·
                  refine ⟨7224702932959096492626353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4816468621972730995084235 7224702932959096492626353)
                  ·
                    refine ⟨5418527199719322369469765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7224702932959096492626353 5418527199719322369469765)
                    ·
                      refine ⟨1015973849947372944275581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5418527199719322369469765 1015973849947372944275581)
                      ·
                        rfl

theorem cell23_1978602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1978602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978602 prefixEnd_1978602 := by exact prefixLift 1978602
  have htrace : WordTrace (prefixWord ++ tailWord_1978602) baseStart_1978602 baseEnd_1978602 := by
    simpa [prefixWord, tailWord_1978602, baseEnd_1978602] using wordTrace_append hprefix tailTrace_1978602
  have hstable : (prefixWord ++ tailWord_1978602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978602).length < 2 ^ (prefixWord ++ tailWord_1978602).sum := by decide
  have hdescent : baseEnd_1978602 < baseStart_1978602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978626 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1978626 : Nat := 118140960795 + 1978626 * 2 ^ 59
def prefixEnd_1978626 : Nat := 4983230072969 + 3 ^ 40 * 1978626 * 2
def baseEnd_1978626 : Nat := 1015986173483080850375471

theorem tailTrace_1978626 : CollatzResearch.WordTrace tailWord_1978626 prefixEnd_1978626 1015986173483080850375471 := by
  unfold tailWord_1978626
  simp only [CollatzResearch.WordTrace]
  refine ⟨18041604732445849815632933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48110945953188932841687821 18041604732445849815632933)
  ·
    refine ⟨3382800887333596840431175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18041604732445849815632933 3382800887333596840431175)
    ·
      refine ⟨5074201331000395260646763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382800887333596840431175 5074201331000395260646763)
      ·
        refine ⟨7611301996500592890970145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074201331000395260646763 7611301996500592890970145)
        ·
          refine ⟨5708476497375444668227609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7611301996500592890970145 5708476497375444668227609)
          ·
            refine ⟨4281357373031583501170707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5708476497375444668227609 4281357373031583501170707)
            ·
              refine ⟨6422036059547375251756061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281357373031583501170707 6422036059547375251756061)
              ·
                refine ⟨2408263522330265719408523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6422036059547375251756061 2408263522330265719408523)
                ·
                  refine ⟨3612395283495398579112785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408263522330265719408523 3612395283495398579112785)
                  ·
                    refine ⟨2709296462621548934334589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612395283495398579112785 2709296462621548934334589)
                    ·
                      refine ⟨1015986173483080850375471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2709296462621548934334589 1015986173483080850375471)
                      ·
                        rfl

theorem cell23_1978626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1978626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978626 prefixEnd_1978626 := by exact prefixLift 1978626
  have htrace : WordTrace (prefixWord ++ tailWord_1978626) baseStart_1978626 baseEnd_1978626 := by
    simpa [prefixWord, tailWord_1978626, baseEnd_1978626] using wordTrace_append hprefix tailTrace_1978626
  have hstable : (prefixWord ++ tailWord_1978626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978626).length < 2 ^ (prefixWord ++ tailWord_1978626).sum := by decide
  have hdescent : baseEnd_1978626 < baseStart_1978626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978645 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1978645 : Nat := 118140960795 + 1978645 * 2 ^ 59
def prefixEnd_1978645 : Nat := 4983230072969 + 3 ^ 40 * 1978645 * 2
def baseEnd_1978645 : Nat := 1015995929615516276037883

theorem tailTrace_1978645 : CollatzResearch.WordTrace tailWord_1978645 prefixEnd_1978645 1015995929615516276037883 := by
  unfold tailWord_1978645
  simp only [CollatzResearch.WordTrace]
  refine ⟨72167111916714565507473389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48111407944476377004982259 72167111916714565507473389)
  ·
    refine ⟨27062666968767962065302521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72167111916714565507473389 27062666968767962065302521)
    ·
      refine ⟨20297000226575971548976891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27062666968767962065302521 20297000226575971548976891)
      ·
        refine ⟨30445500339863957323465337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20297000226575971548976891 30445500339863957323465337)
        ·
          refine ⟨22834125254897967992599003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30445500339863957323465337 22834125254897967992599003)
          ·
            refine ⟨34251187882346951988898505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22834125254897967992599003 34251187882346951988898505)
            ·
              refine ⟨25688390911760213991673879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34251187882346951988898505 25688390911760213991673879)
              ·
                refine ⟨38532586367640320987510819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25688390911760213991673879 38532586367640320987510819)
                ·
                  refine ⟨57798879551460481481266229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38532586367640320987510819 57798879551460481481266229)
                  ·
                    refine ⟨5418644957949420138868709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57798879551460481481266229 5418644957949420138868709)
                    ·
                      refine ⟨1015995929615516276037883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5418644957949420138868709 1015995929615516276037883)
                      ·
                        rfl

theorem cell23_1978645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1978645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978645 prefixEnd_1978645 := by exact prefixLift 1978645
  have htrace : WordTrace (prefixWord ++ tailWord_1978645) baseStart_1978645 baseEnd_1978645 := by
    simpa [prefixWord, tailWord_1978645, baseEnd_1978645] using wordTrace_append hprefix tailTrace_1978645
  have hstable : (prefixWord ++ tailWord_1978645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978645).length < 2 ^ (prefixWord ++ tailWord_1978645).sum := by decide
  have hdescent : baseEnd_1978645 < baseStart_1978645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978663 : List Nat := [1, 1, 8, 1, 1, 2, 2, 7]
def baseStart_1978663 : Nat := 118140960795 + 1978663 * 2 ^ 59
def prefixEnd_1978663 : Nat := 4983230072969 + 3 ^ 40 * 1978663 * 2
def baseEnd_1978663 : Nat := 37629821195085081689363

theorem tailTrace_1978663 : CollatzResearch.WordTrace tailWord_1978663 prefixEnd_1978663 37629821195085081689363 := by
  unfold tailWord_1978663
  simp only [CollatzResearch.WordTrace]
  refine ⟨72167768430649354581628643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48111845620432903054419095 72167768430649354581628643)
  ·
    refine ⟨108251652645974031872442965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72167768430649354581628643 108251652645974031872442965)
    ·
      refine ⟨1268574054445008186005191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 108251652645974031872442965 1268574054445008186005191)
      ·
        refine ⟨1902861081667512279007787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268574054445008186005191 1902861081667512279007787)
        ·
          refine ⟨2854291622501268418511681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902861081667512279007787 2854291622501268418511681)
          ·
            refine ⟨2140718716875951313883761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854291622501268418511681 2140718716875951313883761)
            ·
              refine ⟨1605539037656963485412821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140718716875951313883761 1605539037656963485412821)
              ·
                refine ⟨37629821195085081689363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1605539037656963485412821 37629821195085081689363)
                ·
                  rfl

theorem cell23_1978663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 7].length) (baseStart_1978663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978663 prefixEnd_1978663 := by exact prefixLift 1978663
  have htrace : WordTrace (prefixWord ++ tailWord_1978663) baseStart_1978663 baseEnd_1978663 := by
    simpa [prefixWord, tailWord_1978663, baseEnd_1978663] using wordTrace_append hprefix tailTrace_1978663
  have hstable : (prefixWord ++ tailWord_1978663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978663).length < 2 ^ (prefixWord ++ tailWord_1978663).sum := by decide
  have hdescent : baseEnd_1978663 < baseStart_1978663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978682 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1978682 : Nat := 118140960795 + 1978682 * 2 ^ 59
def prefixEnd_1978682 : Nat := 4983230072969 + 3 ^ 40 * 1978682 * 2
def baseEnd_1978682 : Nat := 1016014928399732631275213

theorem tailTrace_1978682 : CollatzResearch.WordTrace tailWord_1978682 prefixEnd_1978682 1016014928399732631275213 := by
  unfold tailWord_1978682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042115354395130206642575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48112307611720347217713533 18042115354395130206642575)
  ·
    refine ⟨27063173031592695309963863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18042115354395130206642575 27063173031592695309963863)
    ·
      refine ⟨40594759547389042964945795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27063173031592695309963863 40594759547389042964945795)
      ·
        refine ⟨60892139321083564447418693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40594759547389042964945795 60892139321083564447418693)
        ·
          refine ⟨11417276122703168333891005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60892139321083564447418693 11417276122703168333891005)
          ·
            refine ⟨4281478546013688125209127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11417276122703168333891005 4281478546013688125209127)
            ·
              refine ⟨6422217819020532187813691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281478546013688125209127 6422217819020532187813691)
              ·
                refine ⟨9633326728530798281720537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6422217819020532187813691 9633326728530798281720537)
                ·
                  refine ⟨7224995046398098711290403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9633326728530798281720537 7224995046398098711290403)
                  ·
                    refine ⟨10837492569597148066935605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7224995046398098711290403 10837492569597148066935605)
                    ·
                      refine ⟨1016014928399732631275213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10837492569597148066935605 1016014928399732631275213)
                      ·
                        rfl

theorem cell23_1978682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1978682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978682 prefixEnd_1978682 := by exact prefixLift 1978682
  have htrace : WordTrace (prefixWord ++ tailWord_1978682) baseStart_1978682 baseEnd_1978682 := by
    simpa [prefixWord, tailWord_1978682, baseEnd_1978682] using wordTrace_append hprefix tailTrace_1978682
  have hstable : (prefixWord ++ tailWord_1978682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978682).length < 2 ^ (prefixWord ++ tailWord_1978682).sum := by decide
  have hdescent : baseEnd_1978682 < baseStart_1978682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978695 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1978695 : Nat := 118140960795 + 1978695 * 2 ^ 59
def prefixEnd_1978695 : Nat := 4983230072969 + 3 ^ 40 * 1978695 * 2
def baseEnd_1978695 : Nat := 1016021603648241080412653

theorem tailTrace_1978695 : CollatzResearch.WordTrace tailWord_1978695 prefixEnd_1978695 1016021603648241080412653 := by
  unfold tailWord_1978695
  simp only [CollatzResearch.WordTrace]
  refine ⟨72168935566533424046793539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48112623711022282697862359 72168935566533424046793539)
  ·
    refine ⟨108253403349800136070190309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72168935566533424046793539 108253403349800136070190309)
    ·
      refine ⟨20297513128087525513160683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108253403349800136070190309 20297513128087525513160683)
      ·
        refine ⟨30446269692131288269741025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20297513128087525513160683 30446269692131288269741025)
        ·
          refine ⟨22834702269098466202305769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30446269692131288269741025 22834702269098466202305769)
          ·
            refine ⟨17126026701823849651729327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22834702269098466202305769 17126026701823849651729327)
            ·
              refine ⟨25689040052735774477593991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17126026701823849651729327 25689040052735774477593991)
              ·
                refine ⟨38533560079103661716390987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25689040052735774477593991 38533560079103661716390987)
                ·
                  refine ⟨57800340118655492574586481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38533560079103661716390987 57800340118655492574586481)
                  ·
                    refine ⟨43350255088991619430939861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57800340118655492574586481 43350255088991619430939861)
                    ·
                      refine ⟨1016021603648241080412653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43350255088991619430939861 1016021603648241080412653)
                      ·
                        rfl

theorem cell23_1978695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1978695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978695 prefixEnd_1978695 := by exact prefixLift 1978695
  have htrace : WordTrace (prefixWord ++ tailWord_1978695) baseStart_1978695 baseEnd_1978695 := by
    simpa [prefixWord, tailWord_1978695, baseEnd_1978695] using wordTrace_append hprefix tailTrace_1978695
  have hstable : (prefixWord ++ tailWord_1978695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978695).length < 2 ^ (prefixWord ++ tailWord_1978695).sum := by decide
  have hdescent : baseEnd_1978695 < baseStart_1978695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978753 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 5]
def baseStart_1978753 : Nat := 118140960795 + 1978753 * 2 ^ 59
def prefixEnd_1978753 : Nat := 4983230072969 + 3 ^ 40 * 1978753 * 2
def baseEnd_1978753 : Nat := 112894598391800205943043

theorem tailTrace_1978753 : CollatzResearch.WordTrace tailWord_1978753 prefixEnd_1978753 112894598391800205943043 := by
  unfold tailWord_1978753
  simp only [CollatzResearch.WordTrace]
  refine ⟨72171051000323299952404913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48114034000215533301603275 72171051000323299952404913)
  ·
    refine ⟨54128288250242474964303685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72171051000323299952404913 54128288250242474964303685)
    ·
      refine ⟨10149054046920464055806941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54128288250242474964303685 10149054046920464055806941)
      ·
        refine ⟨3805895267595174020927603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10149054046920464055806941 3805895267595174020927603)
        ·
          refine ⟨5708842901392761031391405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805895267595174020927603 5708842901392761031391405)
          ·
            refine ⟨2140816088022285386771777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5708842901392761031391405 2140816088022285386771777)
            ·
              refine ⟨1605612066016714040078833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140816088022285386771777 1605612066016714040078833)
              ·
                refine ⟨1204209049512535530059125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605612066016714040078833 1204209049512535530059125)
                ·
                  refine ⟨112894598391800205943043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1204209049512535530059125 112894598391800205943043)
                  ·
                    rfl

theorem cell23_1978753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 5].length) (baseStart_1978753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978753 prefixEnd_1978753 := by exact prefixLift 1978753
  have htrace : WordTrace (prefixWord ++ tailWord_1978753) baseStart_1978753 baseEnd_1978753 := by
    simpa [prefixWord, tailWord_1978753, baseEnd_1978753] using wordTrace_append hprefix tailTrace_1978753
  have hstable : (prefixWord ++ tailWord_1978753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978753).length < 2 ^ (prefixWord ++ tailWord_1978753).sum := by decide
  have hdescent : baseEnd_1978753 < baseStart_1978753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978809 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 6]
def baseStart_1978809 : Nat := 118140960795 + 1978809 * 2 ^ 59
def prefixEnd_1978809 : Nat := 4983230072969 + 3 ^ 40 * 1978809 * 2
def baseEnd_1978809 : Nat := 112897793382539292709681

theorem tailTrace_1978809 : CollatzResearch.WordTrace tailWord_1978809 prefixEnd_1978809 112897793382539292709681 := by
  unfold tailWord_1978809
  simp only [CollatzResearch.WordTrace]
  refine ⟨72173093488120421516443481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48115395658746947677628987 72173093488120421516443481)
  ·
    refine ⟨54129820116090316137332611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72173093488120421516443481 54129820116090316137332611)
    ·
      refine ⟨81194730174135474205998917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54129820116090316137332611 81194730174135474205998917)
      ·
        refine ⟨15224011907650401413624797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81194730174135474205998917 15224011907650401413624797)
        ·
          refine ⟨5709004465368900530109299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15224011907650401413624797 5709004465368900530109299)
          ·
            refine ⟨8563506698053350795163949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709004465368900530109299 8563506698053350795163949)
            ·
              refine ⟨3211315011770006548186481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8563506698053350795163949 3211315011770006548186481)
              ·
                refine ⟨2408486258827504911139861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3211315011770006548186481 2408486258827504911139861)
                ·
                  refine ⟨112897793382539292709681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2408486258827504911139861 112897793382539292709681)
                  ·
                    rfl

theorem cell23_1978809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_1978809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978809 prefixEnd_1978809 := by exact prefixLift 1978809
  have htrace : WordTrace (prefixWord ++ tailWord_1978809) baseStart_1978809 baseEnd_1978809 := by
    simpa [prefixWord, tailWord_1978809, baseEnd_1978809] using wordTrace_append hprefix tailTrace_1978809
  have hstable : (prefixWord ++ tailWord_1978809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978809).length < 2 ^ (prefixWord ++ tailWord_1978809).sum := by decide
  have hdescent : baseEnd_1978809 < baseStart_1978809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978859 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 4]
def baseStart_1978859 : Nat := 118140960795 + 1978859 * 2 ^ 59
def prefixEnd_1978859 : Nat := 4983230072969 + 3 ^ 40 * 1978859 * 2
def baseEnd_1978859 : Nat := 1016105814475578438761899

theorem tailTrace_1978859 : CollatzResearch.WordTrace tailWord_1978859 prefixEnd_1978859 1016105814475578438761899 := by
  unfold tailWord_1978859
  simp only [CollatzResearch.WordTrace]
  refine ⟨72174917137939280055763631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48116611425292853370509087 72174917137939280055763631)
  ·
    refine ⟨108262375706908920083645447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72174917137939280055763631 108262375706908920083645447)
    ·
      refine ⟨162393563560363380125468171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108262375706908920083645447 162393563560363380125468171)
      ·
        refine ⟨243590345340545070188202257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162393563560363380125468171 243590345340545070188202257)
        ·
          refine ⟨182692759005408802641151693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243590345340545070188202257 182692759005408802641151693)
          ·
            refine ⟨68509784627028300990431885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182692759005408802641151693 68509784627028300990431885)
            ·
              refine ⟨25691169235135612871411957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68509784627028300990431885 25691169235135612871411957)
              ·
                refine ⟨2408547115793963706694871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25691169235135612871411957 2408547115793963706694871)
                ·
                  refine ⟨3612820673690945560042307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408547115793963706694871 3612820673690945560042307)
                  ·
                    refine ⟨5419231010536418340063461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3612820673690945560042307 5419231010536418340063461)
                    ·
                      refine ⟨1016105814475578438761899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5419231010536418340063461 1016105814475578438761899)
                      ·
                        rfl

theorem cell23_1978859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 4].length) (baseStart_1978859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978859 prefixEnd_1978859 := by exact prefixLift 1978859
  have htrace : WordTrace (prefixWord ++ tailWord_1978859) baseStart_1978859 baseEnd_1978859 := by
    simpa [prefixWord, tailWord_1978859, baseEnd_1978859] using wordTrace_append hprefix tailTrace_1978859
  have hstable : (prefixWord ++ tailWord_1978859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978859).length < 2 ^ (prefixWord ++ tailWord_1978859).sum := by decide
  have hdescent : baseEnd_1978859 < baseStart_1978859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978872 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1978872 : Nat := 118140960795 + 1978872 * 2 ^ 59
def prefixEnd_1978872 : Nat := 4983230072969 + 3 ^ 40 * 1978872 * 2
def baseEnd_1978872 : Nat := 1016112489724086887899339

theorem tailTrace_1978872 : CollatzResearch.WordTrace tailWord_1978872 prefixEnd_1978872 1016112489724086887899339 := by
  unfold tailWord_1978872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36087695643446091637993435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48116927524594788850657913 36087695643446091637993435)
  ·
    refine ⟨54131543465169137456990153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36087695643446091637993435 54131543465169137456990153)
    ·
      refine ⟨40598657598876853092742615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54131543465169137456990153 40598657598876853092742615)
      ·
        refine ⟨60897986398315279639113923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40598657598876853092742615 60897986398315279639113923)
        ·
          refine ⟨91346979597472919458670885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60897986398315279639113923 91346979597472919458670885)
          ·
            refine ⟨17127558674526172398500791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91346979597472919458670885 17127558674526172398500791)
            ·
              refine ⟨25691338011789258597751187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17127558674526172398500791 25691338011789258597751187)
              ·
                refine ⟨38537007017683887896626781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25691338011789258597751187 38537007017683887896626781)
                ·
                  refine ⟨14451377631631457961235043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38537007017683887896626781 14451377631631457961235043)
                  ·
                    refine ⟨21677066447447186941852565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14451377631631457961235043 21677066447447186941852565)
                    ·
                      refine ⟨1016112489724086887899339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21677066447447186941852565 1016112489724086887899339)
                      ·
                        rfl

theorem cell23_1978872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1978872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978872 prefixEnd_1978872 := by exact prefixLift 1978872
  have htrace : WordTrace (prefixWord ++ tailWord_1978872) baseStart_1978872 baseEnd_1978872 := by
    simpa [prefixWord, tailWord_1978872, baseEnd_1978872] using wordTrace_append hprefix tailTrace_1978872
  have hstable : (prefixWord ++ tailWord_1978872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978872).length < 2 ^ (prefixWord ++ tailWord_1978872).sum := by decide
  have hdescent : baseEnd_1978872 < baseStart_1978872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978879 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_1978879 : Nat := 118140960795 + 1978879 * 2 ^ 59
def prefixEnd_1978879 : Nat := 4983230072969 + 3 ^ 40 * 1978879 * 2
def baseEnd_1978879 : Nat := 1016116084088668360511807

theorem tailTrace_1978879 : CollatzResearch.WordTrace tailWord_1978879 prefixEnd_1978879 1016116084088668360511807 := by
  unfold tailWord_1978879
  simp only [CollatzResearch.WordTrace]
  refine ⟨72175646597866823471491691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48117097731911215647661127 72175646597866823471491691)
  ·
    refine ⟨108263469896800235207237537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72175646597866823471491691 108263469896800235207237537)
    ·
      refine ⟨81197602422600176405428153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108263469896800235207237537 81197602422600176405428153)
      ·
        refine ⟨60898201816950132304071115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81197602422600176405428153 60898201816950132304071115)
        ·
          refine ⟨91347302725425198456106673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60898201816950132304071115 91347302725425198456106673)
          ·
            refine ⟨68510477044068898842080005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91347302725425198456106673 68510477044068898842080005)
            ·
              refine ⟨12845714445762918532890001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68510477044068898842080005 12845714445762918532890001)
              ·
                refine ⟨9634285834322188899667501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12845714445762918532890001 9634285834322188899667501)
                ·
                  refine ⟨3612857187870820837375313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9634285834322188899667501 3612857187870820837375313)
                  ·
                    refine ⟨2709642890903115628031485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612857187870820837375313 2709642890903115628031485)
                    ·
                      refine ⟨1016116084088668360511807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2709642890903115628031485 1016116084088668360511807)
                      ·
                        rfl

theorem cell23_1978879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_1978879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978879 prefixEnd_1978879 := by exact prefixLift 1978879
  have htrace : WordTrace (prefixWord ++ tailWord_1978879) baseStart_1978879 baseEnd_1978879 := by
    simpa [prefixWord, tailWord_1978879, baseEnd_1978879] using wordTrace_append hprefix tailTrace_1978879
  have hstable : (prefixWord ++ tailWord_1978879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978879).length < 2 ^ (prefixWord ++ tailWord_1978879).sum := by decide
  have hdescent : baseEnd_1978879 < baseStart_1978879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978913 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1978913 : Nat := 118140960795 + 1978913 * 2 ^ 59
def prefixEnd_1978913 : Nat := 4983230072969 + 3 ^ 40 * 1978913 * 2
def baseEnd_1978913 : Nat := 1016133542430921227486651

theorem tailTrace_1978913 : CollatzResearch.WordTrace tailWord_1978913 prefixEnd_1978913 1016133542430921227486651 := by
  unfold tailWord_1978913
  simp only [CollatzResearch.WordTrace]
  refine ⟨72176886679743647278229393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48117924453162431518819595 72176886679743647278229393)
  ·
    refine ⟨54132665009807735458672045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72176886679743647278229393 54132665009807735458672045)
    ·
      refine ⟨20299749378677900797002017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54132665009807735458672045 20299749378677900797002017)
      ·
        refine ⟨15224812034008425597751513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20299749378677900797002017 15224812034008425597751513)
        ·
          refine ⟨11418609025506319198313635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15224812034008425597751513 11418609025506319198313635)
          ·
            refine ⟨17127913538259478797470453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418609025506319198313635 17127913538259478797470453)
            ·
              refine ⟨1605741894211826137262855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17127913538259478797470453 1605741894211826137262855)
              ·
                refine ⟨2408612841317739205894283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605741894211826137262855 2408612841317739205894283)
                ·
                  refine ⟨3612919261976608808841425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2408612841317739205894283 3612919261976608808841425)
                  ·
                    refine ⟨2709689446482456606631069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3612919261976608808841425 2709689446482456606631069)
                    ·
                      refine ⟨1016133542430921227486651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2709689446482456606631069 1016133542430921227486651)
                      ·
                        rfl

theorem cell23_1978913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1978913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978913 prefixEnd_1978913 := by exact prefixLift 1978913
  have htrace : WordTrace (prefixWord ++ tailWord_1978913) baseStart_1978913 baseEnd_1978913 := by
    simpa [prefixWord, tailWord_1978913, baseEnd_1978913] using wordTrace_append hprefix tailTrace_1978913
  have hstable : (prefixWord ++ tailWord_1978913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978913).length < 2 ^ (prefixWord ++ tailWord_1978913).sum := by decide
  have hdescent : baseEnd_1978913 < baseStart_1978913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978916 : List Nat := [2, 3, 1, 5, 2, 10]
def baseStart_1978916 : Nat := 118140960795 + 1978916 * 2 ^ 59
def prefixEnd_1978916 : Nat := 4983230072969 + 3 ^ 40 * 1978916 * 2
def baseEnd_1978916 : Nat := 4181625855443970023659

theorem tailTrace_1978916 : CollatzResearch.WordTrace tailWord_1978916 prefixEnd_1978916 4181625855443970023659 := by
  unfold tailWord_1978916
  simp only [CollatzResearch.WordTrace]
  refine ⟨36088498049366389395294301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48117997399155185860392401 36088498049366389395294301)
  ·
    refine ⟨13533186768512396023235363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36088498049366389395294301 13533186768512396023235363)
    ·
      refine ⟨20299780152768594034853045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533186768512396023235363 20299780152768594034853045)
      ·
        refine ⟨1903104389322055690767473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20299780152768594034853045 1903104389322055690767473)
        ·
          refine ⟨1427328291991541768075605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903104389322055690767473 1427328291991541768075605)
          ·
            refine ⟨4181625855443970023659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1427328291991541768075605 4181625855443970023659)
            ·
              rfl

theorem cell23_1978916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 10].length) (baseStart_1978916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978916 prefixEnd_1978916 := by exact prefixLift 1978916
  have htrace : WordTrace (prefixWord ++ tailWord_1978916) baseStart_1978916 baseEnd_1978916 := by
    simpa [prefixWord, tailWord_1978916, baseEnd_1978916] using wordTrace_append hprefix tailTrace_1978916
  have hstable : (prefixWord ++ tailWord_1978916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978916).length < 2 ^ (prefixWord ++ tailWord_1978916).sum := by decide
  have hdescent : baseEnd_1978916 < baseStart_1978916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978936 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 5, 3, 2]
def baseStart_1978936 : Nat := 118140960795 + 1978936 * 2 ^ 59
def prefixEnd_1978936 : Nat := 4983230072969 + 3 ^ 40 * 1978936 * 2
def baseEnd_1978936 : Nat := 1016145352485974637499045

theorem tailTrace_1978936 : CollatzResearch.WordTrace tailWord_1978936 prefixEnd_1978936 1016145352485974637499045 := by
  unfold tailWord_1978936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36088862779330161103158331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48118483705773548137544441 36088862779330161103158331)
  ·
    refine ⟨54133294168995241654737497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36088862779330161103158331 54133294168995241654737497)
    ·
      refine ⟨40599970626746431241053123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54133294168995241654737497 40599970626746431241053123)
      ·
        refine ⟨60899955940119646861579685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40599970626746431241053123 60899955940119646861579685)
        ·
          refine ⟨11418741738772433786546191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60899955940119646861579685 11418741738772433786546191)
          ·
            refine ⟨17128112608158650679819287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11418741738772433786546191 17128112608158650679819287)
            ·
              refine ⟨25692168912237976019728931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17128112608158650679819287 25692168912237976019728931)
              ·
                refine ⟨38538253368356964029593397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25692168912237976019728931 38538253368356964029593397)
                ·
                  refine ⟨3612961253283465377774381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38538253368356964029593397 3612961253283465377774381)
                  ·
                    refine ⟨1354860469981299516665393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3612961253283465377774381 1354860469981299516665393)
                    ·
                      refine ⟨1016145352485974637499045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354860469981299516665393 1016145352485974637499045)
                      ·
                        rfl

theorem cell23_1978936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_1978936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978936 prefixEnd_1978936 := by exact prefixLift 1978936
  have htrace : WordTrace (prefixWord ++ tailWord_1978936) baseStart_1978936 baseEnd_1978936 := by
    simpa [prefixWord, tailWord_1978936, baseEnd_1978936] using wordTrace_append hprefix tailTrace_1978936
  have hstable : (prefixWord ++ tailWord_1978936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978936).length < 2 ^ (prefixWord ++ tailWord_1978936).sum := by decide
  have hdescent : baseEnd_1978936 < baseStart_1978936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1978979 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1978979 : Nat := 118140960795 + 1978979 * 2 ^ 59
def prefixEnd_1978979 : Nat := 4983230072969 + 3 ^ 40 * 1978979 * 2
def baseEnd_1978979 : Nat := 1016167432154117969261347

theorem tailTrace_1978979 : CollatzResearch.WordTrace tailWord_1978979 prefixEnd_1978979 1016167432154117969261347 := by
  unfold tailWord_1978979
  simp only [CollatzResearch.WordTrace]
  refine ⟨72179293897504540550131991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48119529265003027033421327 72179293897504540550131991)
  ·
    refine ⟨108268940846256810825197987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72179293897504540550131991 108268940846256810825197987)
    ·
      refine ⟨162403411269385216237796981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108268940846256810825197987 162403411269385216237796981)
      ·
        refine ⟨15225319806504864022293467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162403411269385216237796981 15225319806504864022293467)
        ·
          refine ⟨22837979709757296033440201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15225319806504864022293467 22837979709757296033440201)
          ·
            refine ⟨17128484782317972025080151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22837979709757296033440201 17128484782317972025080151)
            ·
              refine ⟨25692727173476958037620227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17128484782317972025080151 25692727173476958037620227)
              ·
                refine ⟨38539090760215437056430341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25692727173476958037620227 38539090760215437056430341)
                ·
                  refine ⟨7226079517540394448080689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38539090760215437056430341 7226079517540394448080689)
                  ·
                    refine ⟨5419559638155295836060517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7226079517540394448080689 5419559638155295836060517)
                    ·
                      refine ⟨1016167432154117969261347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5419559638155295836060517 1016167432154117969261347)
                      ·
                        rfl

theorem cell23_1978979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1978979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1978979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1978979 prefixEnd_1978979 := by exact prefixLift 1978979
  have htrace : WordTrace (prefixWord ++ tailWord_1978979) baseStart_1978979 baseEnd_1978979 := by
    simpa [prefixWord, tailWord_1978979, baseEnd_1978979] using wordTrace_append hprefix tailTrace_1978979
  have hstable : (prefixWord ++ tailWord_1978979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1978979).length < 2 ^ (prefixWord ++ tailWord_1978979).sum := by decide
  have hdescent : baseEnd_1978979 < baseStart_1978979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1978979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979036 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1979036 : Nat := 118140960795 + 1979036 * 2 ^ 59
def prefixEnd_1979036 : Nat := 4983230072969 + 3 ^ 40 * 1979036 * 2
def baseEnd_1979036 : Nat := 338732233517141415416195

theorem tailTrace_1979036 : CollatzResearch.WordTrace tailWord_1979036 prefixEnd_1979036 338732233517141415416195 := by
  unfold tailWord_1979036
  simp only [CollatzResearch.WordTrace]
  refine ⟨36090686429149019642478481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48120915238865359523304641 36090686429149019642478481)
  ·
    refine ⟨27068014821861764731858861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36090686429149019642478481 27068014821861764731858861)
    ·
      refine ⟨10150505558198161774447073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27068014821861764731858861 10150505558198161774447073)
      ·
        refine ⟨7612879168648621330835305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10150505558198161774447073 7612879168648621330835305)
        ·
          refine ⟨5709659376486465998126479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7612879168648621330835305 5709659376486465998126479)
          ·
            refine ⟨8564489064729698997189719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5709659376486465998126479 8564489064729698997189719)
            ·
              refine ⟨12846733597094548495784579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564489064729698997189719 12846733597094548495784579)
              ·
                refine ⟨19270100395641822743676869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12846733597094548495784579 19270100395641822743676869)
                ·
                  refine ⟨3613143824182841764439413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19270100395641822743676869 3613143824182841764439413)
                  ·
                    refine ⟨338732233517141415416195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3613143824182841764439413 338732233517141415416195)
                    ·
                      rfl

theorem cell23_1979036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1979036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979036 prefixEnd_1979036 := by exact prefixLift 1979036
  have htrace : WordTrace (prefixWord ++ tailWord_1979036) baseStart_1979036 baseEnd_1979036 := by
    simpa [prefixWord, tailWord_1979036, baseEnd_1979036] using wordTrace_append hprefix tailTrace_1979036
  have hstable : (prefixWord ++ tailWord_1979036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979036).length < 2 ^ (prefixWord ++ tailWord_1979036).sum := by decide
  have hdescent : baseEnd_1979036 < baseStart_1979036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979040 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 5]
def baseStart_1979040 : Nat := 118140960795 + 1979040 * 2 ^ 59
def prefixEnd_1979040 : Nat := 4983230072969 + 3 ^ 40 * 1979040 * 2
def baseEnd_1979040 : Nat := 112910972719338025622063

theorem tailTrace_1979040 : CollatzResearch.WordTrace tailWord_1979040 prefixEnd_1979040 112910972719338025622063 := by
  unfold tailWord_1979040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36090759375141773984051287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48121012500189031978735049 36090759375141773984051287)
  ·
    refine ⟨54136139062712660976076931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36090759375141773984051287 54136139062712660976076931)
    ·
      refine ⟨81204208594068991464115397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54136139062712660976076931 81204208594068991464115397)
      ·
        refine ⟨15225789111387935899521637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81204208594068991464115397 15225789111387935899521637)
        ·
          refine ⟨2854835458385237981160307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15225789111387935899521637 2854835458385237981160307)
          ·
            refine ⟨4282253187577856971740461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854835458385237981160307 4282253187577856971740461)
            ·
              refine ⟨1605844945341696364402673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4282253187577856971740461 1605844945341696364402673)
              ·
                refine ⟨1204383709006272273302005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605844945341696364402673 1204383709006272273302005)
                ·
                  refine ⟨112910972719338025622063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1204383709006272273302005 112910972719338025622063)
                  ·
                    rfl

theorem cell23_1979040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 5].length) (baseStart_1979040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979040 prefixEnd_1979040 := by exact prefixLift 1979040
  have htrace : WordTrace (prefixWord ++ tailWord_1979040) baseStart_1979040 baseEnd_1979040 := by
    simpa [prefixWord, tailWord_1979040, baseEnd_1979040] using wordTrace_append hprefix tailTrace_1979040
  have hstable : (prefixWord ++ tailWord_1979040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979040).length < 2 ^ (prefixWord ++ tailWord_1979040).sum := by decide
  have hdescent : baseEnd_1979040 < baseStart_1979040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979056 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 6, 2]
def baseStart_1979056 : Nat := 118140960795 + 1979056 * 2 ^ 59
def prefixEnd_1979056 : Nat := 4983230072969 + 3 ^ 40 * 1979056 * 2
def baseEnd_1979056 : Nat := 1016206970164514167998493

theorem tailTrace_1979056 : CollatzResearch.WordTrace tailWord_1979056 prefixEnd_1979056 1016206970164514167998493 := by
  unfold tailWord_1979056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091051159112791350342511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48121401545483721800456681 36091051159112791350342511)
  ·
    refine ⟨54136576738669187025513767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36091051159112791350342511 54136576738669187025513767)
    ·
      refine ⟨81204865108003780538270651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54136576738669187025513767 81204865108003780538270651)
      ·
        refine ⟨121807297662005670807405977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81204865108003780538270651 121807297662005670807405977)
        ·
          refine ⟨91355473246504253105554483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121807297662005670807405977 91355473246504253105554483)
          ·
            refine ⟨137033209869756379658331725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91355473246504253105554483 137033209869756379658331725)
            ·
              refine ⟨51387453701158642371874397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137033209869756379658331725 51387453701158642371874397)
              ·
                refine ⟨19270295137934490889452899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51387453701158642371874397 19270295137934490889452899)
                ·
                  refine ⟨28905442706901736334179349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19270295137934490889452899 28905442706901736334179349)
                  ·
                    refine ⟨1354942626886018890664657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28905442706901736334179349 1354942626886018890664657)
                    ·
                      refine ⟨1016206970164514167998493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354942626886018890664657 1016206970164514167998493)
                      ·
                        rfl

theorem cell23_1979056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 6, 2].length) (baseStart_1979056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979056 prefixEnd_1979056 := by exact prefixLift 1979056
  have htrace : WordTrace (prefixWord ++ tailWord_1979056) baseStart_1979056 baseEnd_1979056 := by
    simpa [prefixWord, tailWord_1979056, baseEnd_1979056] using wordTrace_append hprefix tailTrace_1979056
  have hstable : (prefixWord ++ tailWord_1979056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979056).length < 2 ^ (prefixWord ++ tailWord_1979056).sum := by decide
  have hdescent : baseEnd_1979056 < baseStart_1979056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979066 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_1979066 : Nat := 118140960795 + 1979066 * 2 ^ 59
def prefixEnd_1979066 : Nat := 4983230072969 + 3 ^ 40 * 1979066 * 2
def baseEnd_1979066 : Nat := 338737368323686376291149

theorem tailTrace_1979066 : CollatzResearch.WordTrace tailWord_1979066 prefixEnd_1979066 338737368323686376291149 := by
  unfold tailWord_1979066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045616762047338602137263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48121644698792902939032701 18045616762047338602137263)
  ·
    refine ⟨27068425143071007903205895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18045616762047338602137263 27068425143071007903205895)
    ·
      refine ⟨40602637714606511854808843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27068425143071007903205895 40602637714606511854808843)
      ·
        refine ⟨60903956571909767782213265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40602637714606511854808843 60903956571909767782213265)
        ·
          refine ⟨45677967428932325836659949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60903956571909767782213265 45677967428932325836659949)
          ·
            refine ⟨17129237785849622188747481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45677967428932325836659949 17129237785849622188747481)
            ·
              refine ⟨12846928339387216641560611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17129237785849622188747481 12846928339387216641560611)
              ·
                refine ⟨19270392509080824962340917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12846928339387216641560611 19270392509080824962340917)
                ·
                  refine ⟨1806599297726327340219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19270392509080824962340917 1806599297726327340219461)
                  ·
                    refine ⟨338737368323686376291149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1806599297726327340219461 338737368323686376291149)
                    ·
                      rfl

theorem cell23_1979066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_1979066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979066 prefixEnd_1979066 := by exact prefixLift 1979066
  have htrace : WordTrace (prefixWord ++ tailWord_1979066) baseStart_1979066 baseEnd_1979066 := by
    simpa [prefixWord, tailWord_1979066, baseEnd_1979066] using wordTrace_append hprefix tailTrace_1979066
  have hstable : (prefixWord ++ tailWord_1979066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979066).length < 2 ^ (prefixWord ++ tailWord_1979066).sum := by decide
  have hdescent : baseEnd_1979066 < baseStart_1979066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979079 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 8]
def baseStart_1979079 : Nat := 118140960795 + 1979079 * 2 ^ 59
def prefixEnd_1979079 : Nat := 4983230072969 + 3 ^ 40 * 1979079 * 2
def baseEnd_1979079 : Nat := 112913197802174175334543

theorem tailTrace_1979079 : CollatzResearch.WordTrace tailWord_1979079 prefixEnd_1979079 112913197802174175334543 := by
  unfold tailWord_1979079
  simp only [CollatzResearch.WordTrace]
  refine ⟨72182941197142257628772291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48121960798094838419181527 72182941197142257628772291)
  ·
    refine ⟨108274411795713386443158437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72182941197142257628772291 108274411795713386443158437)
    ·
      refine ⟨20301452211696259958092207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108274411795713386443158437 20301452211696259958092207)
      ·
        refine ⟨30452178317544389937138311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20301452211696259958092207 30452178317544389937138311)
        ·
          refine ⟨45678267476316584905707467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30452178317544389937138311 45678267476316584905707467)
          ·
            refine ⟨68517401214474877358561201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45678267476316584905707467 68517401214474877358561201)
            ·
              refine ⟨51388050910856158018920901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68517401214474877358561201 51388050910856158018920901)
              ·
                refine ⟨9635259545785529628547669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51388050910856158018920901 9635259545785529628547669)
                ·
                  refine ⟨112913197802174175334543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9635259545785529628547669 112913197802174175334543)
                  ·
                    rfl

theorem cell23_1979079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 8].length) (baseStart_1979079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979079 prefixEnd_1979079 := by exact prefixLift 1979079
  have htrace : WordTrace (prefixWord ++ tailWord_1979079) baseStart_1979079 baseEnd_1979079 := by
    simpa [prefixWord, tailWord_1979079, baseEnd_1979079] using wordTrace_append hprefix tailTrace_1979079
  have hstable : (prefixWord ++ tailWord_1979079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979079).length < 2 ^ (prefixWord ++ tailWord_1979079).sum := by decide
  have hdescent : baseEnd_1979079 < baseStart_1979079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979096 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 6]
def baseStart_1979096 : Nat := 118140960795 + 1979096 * 2 ^ 59
def prefixEnd_1979096 : Nat := 4983230072969 + 3 ^ 40 * 1979096 * 2
def baseEnd_1979096 : Nat := 112914167710077112388701

theorem tailTrace_1979096 : CollatzResearch.WordTrace tailWord_1979096 prefixEnd_1979096 112914167710077112388701 := by
  unfold tailWord_1979096
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091780619040334766070571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48122374158720446354760761 36091780619040334766070571)
  ·
    refine ⟨54137670928560502149105857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36091780619040334766070571 54137670928560502149105857)
    ·
      refine ⟨40603253196420376611829393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54137670928560502149105857 40603253196420376611829393)
      ·
        refine ⟨30452439897315282458872045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40603253196420376611829393 30452439897315282458872045)
        ·
          refine ⟨11419664961493230922077017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30452439897315282458872045 11419664961493230922077017)
          ·
            refine ⟨8564748721119923191557763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11419664961493230922077017 8564748721119923191557763)
            ·
              refine ⟨12847123081679884787336645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564748721119923191557763 12847123081679884787336645)
              ·
                refine ⟨2408835577814978397625621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12847123081679884787336645 2408835577814978397625621)
                ·
                  refine ⟨112914167710077112388701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2408835577814978397625621 112914167710077112388701)
                  ·
                    rfl

theorem cell23_1979096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 6].length) (baseStart_1979096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979096 prefixEnd_1979096 := by exact prefixLift 1979096
  have htrace : WordTrace (prefixWord ++ tailWord_1979096) baseStart_1979096 baseEnd_1979096 := by
    simpa [prefixWord, tailWord_1979096, baseEnd_1979096] using wordTrace_append hprefix tailTrace_1979096
  have hstable : (prefixWord ++ tailWord_1979096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979096).length < 2 ^ (prefixWord ++ tailWord_1979096).sum := by decide
  have hdescent : baseEnd_1979096 < baseStart_1979096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979124 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1979124 : Nat := 118140960795 + 1979124 * 2 ^ 59
def prefixEnd_1979124 : Nat := 4983230072969 + 3 ^ 40 * 1979124 * 2
def baseEnd_1979124 : Nat := 1016241886849019901948181

theorem tailTrace_1979124 : CollatzResearch.WordTrace tailWord_1979124 prefixEnd_1979124 1016241886849019901948181 := by
  unfold tailWord_1979124
  simp only [CollatzResearch.WordTrace]
  refine ⟨36092291240989615157080213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48123054987986153542773617 36092291240989615157080213)
  ·
    refine ⟨1691826151921388210488135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36092291240989615157080213 1691826151921388210488135)
    ·
      refine ⟨2537739227882082315732203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691826151921388210488135 2537739227882082315732203)
      ·
        refine ⟨3806608841823123473598305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537739227882082315732203 3806608841823123473598305)
        ·
          refine ⟨2854956631367342605198729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3806608841823123473598305 2854956631367342605198729)
          ·
            refine ⟨2141217473525506953899047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854956631367342605198729 2141217473525506953899047)
            ·
              refine ⟨3211826210288260430848571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141217473525506953899047 3211826210288260430848571)
              ·
                refine ⟨4817739315432390646272857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3211826210288260430848571 4817739315432390646272857)
                ·
                  refine ⟨3613304486574292984704643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4817739315432390646272857 3613304486574292984704643)
                  ·
                    refine ⟨5419956729861439477056965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3613304486574292984704643 5419956729861439477056965)
                    ·
                      refine ⟨1016241886849019901948181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5419956729861439477056965 1016241886849019901948181)
                      ·
                        rfl

theorem cell23_1979124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1979124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979124 prefixEnd_1979124 := by exact prefixLift 1979124
  have htrace : WordTrace (prefixWord ++ tailWord_1979124) baseStart_1979124 baseEnd_1979124 := by
    simpa [prefixWord, tailWord_1979124, baseEnd_1979124] using wordTrace_append hprefix tailTrace_1979124
  have hstable : (prefixWord ++ tailWord_1979124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979124).length < 2 ^ (prefixWord ++ tailWord_1979124).sum := by decide
  have hdescent : baseEnd_1979124 < baseStart_1979124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979133 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_1979133 : Nat := 118140960795 + 1979133 * 2 ^ 59
def prefixEnd_1979133 : Nat := 4983230072969 + 3 ^ 40 * 1979133 * 2
def baseEnd_1979133 : Nat := 1016246508174910366735639

theorem tailTrace_1979133 : CollatzResearch.WordTrace tailWord_1979133 prefixEnd_1979133 1016246508174910366735639 := by
  unfold tailWord_1979133
  simp only [CollatzResearch.WordTrace]
  refine ⟨72184910738946624851238053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48123273825964416567492035 72184910738946624851238053)
  ·
    refine ⟨13534670763552492159607135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72184910738946624851238053 13534670763552492159607135)
    ·
      refine ⟨20302006145328738239410703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13534670763552492159607135 20302006145328738239410703)
      ·
        refine ⟨30453009217993107359116055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20302006145328738239410703 30453009217993107359116055)
        ·
          refine ⟨45679513826989661038674083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30453009217993107359116055 45679513826989661038674083)
          ·
            refine ⟨68519270740484491558011125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45679513826989661038674083 68519270740484491558011125)
            ·
              refine ⟨6423681631920421083563543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68519270740484491558011125 6423681631920421083563543)
              ·
                refine ⟨9635522447880631625345315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423681631920421083563543 9635522447880631625345315)
                ·
                  refine ⟨14453283671820947438017973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9635522447880631625345315 14453283671820947438017973)
                  ·
                    refine ⟨1354995344233213822314185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14453283671820947438017973 1354995344233213822314185)
                    ·
                      refine ⟨1016246508174910366735639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1354995344233213822314185 1016246508174910366735639)
                      ·
                        rfl

theorem cell23_1979133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_1979133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979133 prefixEnd_1979133 := by exact prefixLift 1979133
  have htrace : WordTrace (prefixWord ++ tailWord_1979133) baseStart_1979133 baseEnd_1979133 := by
    simpa [prefixWord, tailWord_1979133, baseEnd_1979133] using wordTrace_append hprefix tailTrace_1979133
  have hstable : (prefixWord ++ tailWord_1979133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979133).length < 2 ^ (prefixWord ++ tailWord_1979133).sum := by decide
  have hdescent : baseEnd_1979133 < baseStart_1979133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979180 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 3, 2, 2]
def baseStart_1979180 : Nat := 118140960795 + 1979180 * 2 ^ 59
def prefixEnd_1979180 : Nat := 4983230072969 + 3 ^ 40 * 1979180 * 2
def baseEnd_1979180 : Nat := 1016270641765671682847923

theorem tailTrace_1979180 : CollatzResearch.WordTrace tailWord_1979180 prefixEnd_1979180 1016270641765671682847923 := by
  unfold tailWord_1979180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36093312484888175939099497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48124416646517567918799329 36093312484888175939099497)
  ·
    refine ⟨27069984363666131954324623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36093312484888175939099497 27069984363666131954324623)
    ·
      refine ⟨40604976545499197931486935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27069984363666131954324623 40604976545499197931486935)
      ·
        refine ⟨60907464818248796897230403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40604976545499197931486935 60907464818248796897230403)
        ·
          refine ⟨91361197227373195345845605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60907464818248796897230403 91361197227373195345845605)
          ·
            refine ⟨17130224480132474127346051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91361197227373195345845605 17130224480132474127346051)
            ·
              refine ⟨25695336720198711191019077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17130224480132474127346051 25695336720198711191019077)
              ·
                refine ⟨4817875635037258348316077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25695336720198711191019077 4817875635037258348316077)
                ·
                  refine ⟨1806703363138971880618529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4817875635037258348316077 1806703363138971880618529)
                  ·
                    refine ⟨1355027522354228910463897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1806703363138971880618529 1355027522354228910463897)
                    ·
                      refine ⟨1016270641765671682847923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1355027522354228910463897 1016270641765671682847923)
                      ·
                        rfl

theorem cell23_1979180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_1979180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979180 prefixEnd_1979180 := by exact prefixLift 1979180
  have htrace : WordTrace (prefixWord ++ tailWord_1979180) baseStart_1979180 baseEnd_1979180 := by
    simpa [prefixWord, tailWord_1979180, baseEnd_1979180] using wordTrace_append hprefix tailTrace_1979180
  have hstable : (prefixWord ++ tailWord_1979180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979180).length < 2 ^ (prefixWord ++ tailWord_1979180).sum := by decide
  have hdescent : baseEnd_1979180 < baseStart_1979180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979186 : List Nat := [3, 2, 1, 1, 3, 1, 3, 9]
def baseStart_1979186 : Nat := 118140960795 + 1979186 * 2 ^ 59
def prefixEnd_1979186 : Nat := 4983230072969 + 3 ^ 40 * 1979186 * 2
def baseEnd_1979186 : Nat := 37639767505540691087885

theorem tailTrace_1979186 : CollatzResearch.WordTrace tailWord_1979186 prefixEnd_1979186 37639767505540691087885 := by
  unfold tailWord_1979186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18046710951938653725729353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48124562538503076601944941 18046710951938653725729353)
  ·
    refine ⟨13535033213953990294297015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18046710951938653725729353 13535033213953990294297015)
    ·
      refine ⟨20302549820930985441445523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13535033213953990294297015 20302549820930985441445523)
      ·
        refine ⟨30453824731396478162168285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20302549820930985441445523 30453824731396478162168285)
        ·
          refine ⟨11420184274273679310813107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30453824731396478162168285 11420184274273679310813107)
          ·
            refine ⟨17130276411410518966219661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420184274273679310813107 17130276411410518966219661)
            ·
              refine ⟨6423853654278944612332373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17130276411410518966219661 6423853654278944612332373)
              ·
                refine ⟨37639767505540691087885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6423853654278944612332373 37639767505540691087885)
                ·
                  rfl

theorem cell23_1979186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_1979186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979186 prefixEnd_1979186 := by exact prefixLift 1979186
  have htrace : WordTrace (prefixWord ++ tailWord_1979186) baseStart_1979186 baseEnd_1979186 := by
    simpa [prefixWord, tailWord_1979186, baseEnd_1979186] using wordTrace_append hprefix tailTrace_1979186
  have hstable : (prefixWord ++ tailWord_1979186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979186).length < 2 ^ (prefixWord ++ tailWord_1979186).sum := by decide
  have hdescent : baseEnd_1979186 < baseStart_1979186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979234 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1979234 : Nat := 118140960795 + 1979234 * 2 ^ 59
def prefixEnd_1979234 : Nat := 4983230072969 + 3 ^ 40 * 1979234 * 2
def baseEnd_1979234 : Nat := 1016298369721014471572675

theorem tailTrace_1979234 : CollatzResearch.WordTrace tailWord_1979234 prefixEnd_1979234 1016298369721014471572675 := by
  unfold tailWord_1979234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047148627895179775166189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48125729674387146067109837 18047148627895179775166189)
  ·
    refine ⟨6767680735460692415687321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18047148627895179775166189 6767680735460692415687321)
    ·
      refine ⟨5075760551595519311765491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6767680735460692415687321 5075760551595519311765491)
      ·
        refine ⟨7613640827393278967648237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075760551595519311765491 7613640827393278967648237)
        ·
          refine ⟨2855115310272479612868089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7613640827393278967648237 2855115310272479612868089)
          ·
            refine ⟨2141336482704359709651067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855115310272479612868089 2141336482704359709651067)
            ·
              refine ⟨3212004724056539564476601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141336482704359709651067 3212004724056539564476601)
              ·
                refine ⟨2409003543042404673357451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212004724056539564476601 2409003543042404673357451)
                ·
                  refine ⟨3613505314563607010036177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409003543042404673357451 3613505314563607010036177)
                  ·
                    refine ⟨2710128985922705257527133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613505314563607010036177 2710128985922705257527133)
                    ·
                      refine ⟨1016298369721014471572675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2710128985922705257527133 1016298369721014471572675)
                      ·
                        rfl

theorem cell23_1979234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1979234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979234 prefixEnd_1979234 := by exact prefixLift 1979234
  have htrace : WordTrace (prefixWord ++ tailWord_1979234) baseStart_1979234 baseEnd_1979234 := by
    simpa [prefixWord, tailWord_1979234, baseEnd_1979234] using wordTrace_append hprefix tailTrace_1979234
  have hstable : (prefixWord ++ tailWord_1979234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979234).length < 2 ^ (prefixWord ++ tailWord_1979234).sum := by decide
  have hdescent : baseEnd_1979234 < baseStart_1979234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979256 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1979256 : Nat := 118140960795 + 1979256 * 2 ^ 59
def prefixEnd_1979256 : Nat := 4983230072969 + 3 ^ 40 * 1979256 * 2
def baseEnd_1979256 : Nat := 1016309666295413385497573

theorem tailTrace_1979256 : CollatzResearch.WordTrace tailWord_1979256 prefixEnd_1979256 1016309666295413385497573 := by
  unfold tailWord_1979256
  simp only [CollatzResearch.WordTrace]
  refine ⟨36094698458750508428982811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48126264611667344571977081 36094698458750508428982811)
  ·
    refine ⟨54142047688125762643474217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36094698458750508428982811 54142047688125762643474217)
    ·
      refine ⟨40606535766094321982605663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54142047688125762643474217 40606535766094321982605663)
      ·
        refine ⟨60909803649141482973908495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40606535766094321982605663 60909803649141482973908495)
        ·
          refine ⟨91364705473712224460862743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60909803649141482973908495 91364705473712224460862743)
          ·
            refine ⟨137047058210568336691294115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91364705473712224460862743 137047058210568336691294115)
            ·
              refine ⟨205570587315852505036941173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137047058210568336691294115 205570587315852505036941173)
              ·
                refine ⟨19272242560861172347213235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205570587315852505036941173 19272242560861172347213235)
                ·
                  refine ⟨28908363841291758520819853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19272242560861172347213235 28908363841291758520819853)
                  ·
                    refine ⟨10840636440484409445307445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28908363841291758520819853 10840636440484409445307445)
                    ·
                      refine ⟨1016309666295413385497573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10840636440484409445307445 1016309666295413385497573)
                      ·
                        rfl

theorem cell23_1979256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1979256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979256 prefixEnd_1979256 := by exact prefixLift 1979256
  have htrace : WordTrace (prefixWord ++ tailWord_1979256) baseStart_1979256 baseEnd_1979256 := by
    simpa [prefixWord, tailWord_1979256, baseEnd_1979256] using wordTrace_append hprefix tailTrace_1979256
  have hstable : (prefixWord ++ tailWord_1979256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979256).length < 2 ^ (prefixWord ++ tailWord_1979256).sum := by decide
  have hdescent : baseEnd_1979256 < baseStart_1979256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979273 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_1979273 : Nat := 118140960795 + 1979273 * 2 ^ 59
def prefixEnd_1979273 : Nat := 4983230072969 + 3 ^ 40 * 1979273 * 2
def baseEnd_1979273 : Nat := 1016318395466539818984995

theorem tailTrace_1979273 : CollatzResearch.WordTrace tailWord_1979273 prefixEnd_1979273 1016318395466539818984995 := by
  unfold tailWord_1979273
  simp only [CollatzResearch.WordTrace]
  refine ⟨72190016958439428761334473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48126677972292952507556315 72190016958439428761334473)
  ·
    refine ⟨54142512718829571571000855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72190016958439428761334473 54142512718829571571000855)
    ·
      refine ⟨81213769078244357356501283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54142512718829571571000855 81213769078244357356501283)
      ·
        refine ⟨121820653617366536034751925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81213769078244357356501283 121820653617366536034751925)
        ·
          refine ⟨11420686276628112753257993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121820653617366536034751925 11420686276628112753257993)
          ·
            refine ⟨8565514707471084564943495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11420686276628112753257993 8565514707471084564943495)
            ·
              refine ⟨12848272061206626847415243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8565514707471084564943495 12848272061206626847415243)
              ·
                refine ⟨19272408091809940271122865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12848272061206626847415243 19272408091809940271122865)
                ·
                  refine ⟨14454306068857455203342149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19272408091809940271122865 14454306068857455203342149)
                  ·
                    refine ⟨2710182387910772850626653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14454306068857455203342149 2710182387910772850626653)
                    ·
                      refine ⟨1016318395466539818984995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2710182387910772850626653 1016318395466539818984995)
                      ·
                        rfl

theorem cell23_1979273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_1979273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979273 prefixEnd_1979273 := by exact prefixLift 1979273
  have htrace : WordTrace (prefixWord ++ tailWord_1979273) baseStart_1979273 baseEnd_1979273 := by
    simpa [prefixWord, tailWord_1979273, baseEnd_1979273] using wordTrace_append hprefix tailTrace_1979273
  have hstable : (prefixWord ++ tailWord_1979273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979273).length < 2 ^ (prefixWord ++ tailWord_1979273).sum := by decide
  have hdescent : baseEnd_1979273 < baseStart_1979273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979287 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1979287 : Nat := 118140960795 + 1979287 * 2 ^ 59
def prefixEnd_1979287 : Nat := 4983230072969 + 3 ^ 40 * 1979287 * 2
def baseEnd_1979287 : Nat := 1016325584195702764209931

theorem tailTrace_1979287 : CollatzResearch.WordTrace tailWord_1979287 prefixEnd_1979287 1016325584195702764209931 := by
  unfold tailWord_1979287
  simp only [CollatzResearch.WordTrace]
  refine ⟨72190527580388709152344115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48127018386925806101562743 72190527580388709152344115)
  ·
    refine ⟨108285791370583063728516173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72190527580388709152344115 108285791370583063728516173)
    ·
      refine ⟨40607171763968648898193565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108285791370583063728516173 40607171763968648898193565)
      ·
        refine ⟨15227689411488243336822587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40607171763968648898193565 15227689411488243336822587)
        ·
          refine ⟨22841534117232365005233881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15227689411488243336822587 22841534117232365005233881)
          ·
            refine ⟨17131150587924273753925411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22841534117232365005233881 17131150587924273753925411)
            ·
              refine ⟨25696725881886410630888117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17131150587924273753925411 25696725881886410630888117)
              ·
                refine ⟨2409068051426850996645761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25696725881886410630888117 2409068051426850996645761)
                ·
                  refine ⟨1806801038570138247484321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409068051426850996645761 1806801038570138247484321)
                  ·
                    refine ⟨1355100778927603685613241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1806801038570138247484321 1355100778927603685613241)
                    ·
                      refine ⟨1016325584195702764209931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1355100778927603685613241 1016325584195702764209931)
                      ·
                        rfl

theorem cell23_1979287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1979287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979287 prefixEnd_1979287 := by exact prefixLift 1979287
  have htrace : WordTrace (prefixWord ++ tailWord_1979287) baseStart_1979287 baseEnd_1979287 := by
    simpa [prefixWord, tailWord_1979287, baseEnd_1979287] using wordTrace_append hprefix tailTrace_1979287
  have hstable : (prefixWord ++ tailWord_1979287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979287).length < 2 ^ (prefixWord ++ tailWord_1979287).sum := by decide
  have hdescent : baseEnd_1979287 < baseStart_1979287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979293 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 7]
def baseStart_1979293 : Nat := 118140960795 + 1979293 * 2 ^ 59
def prefixEnd_1979293 : Nat := 4983230072969 + 3 ^ 40 * 1979293 * 2
def baseEnd_1979293 : Nat := 112925407231069971192767

theorem tailTrace_1979293 : CollatzResearch.WordTrace tailWord_1979293 prefixEnd_1979293 112925407231069971192767 := by
  unfold tailWord_1979293
  simp only [CollatzResearch.WordTrace]
  refine ⟨72190746418366972177062533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48127164278911314784708355 72190746418366972177062533)
  ·
    refine ⟨13535764953443807283199225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72190746418366972177062533 13535764953443807283199225)
    ·
      refine ⟨10151823715082855462399419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13535764953443807283199225 10151823715082855462399419)
      ·
        refine ⟨15227735572624283193599129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151823715082855462399419 15227735572624283193599129)
        ·
          refine ⟨11420801679468212395199347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15227735572624283193599129 11420801679468212395199347)
          ·
            refine ⟨17131202519202318592799021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420801679468212395199347 17131202519202318592799021)
            ·
              refine ⟨6424200944700869472299633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17131202519202318592799021 6424200944700869472299633)
              ·
                refine ⟨4818150708525652104224725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6424200944700869472299633 4818150708525652104224725)
                ·
                  refine ⟨112925407231069971192767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4818150708525652104224725 112925407231069971192767)
                  ·
                    rfl

theorem cell23_1979293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_1979293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979293 prefixEnd_1979293 := by exact prefixLift 1979293
  have htrace : WordTrace (prefixWord ++ tailWord_1979293) baseStart_1979293 baseEnd_1979293 := by
    simpa [prefixWord, tailWord_1979293, baseEnd_1979293] using wordTrace_append hprefix tailTrace_1979293
  have hstable : (prefixWord ++ tailWord_1979293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979293).length < 2 ^ (prefixWord ++ tailWord_1979293).sum := by decide
  have hdescent : baseEnd_1979293 < baseStart_1979293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979343 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_1979343 : Nat := 118140960795 + 1979343 * 2 ^ 59
def prefixEnd_1979343 : Nat := 4983230072969 + 3 ^ 40 * 1979343 * 2
def baseEnd_1979343 : Nat := 1016354339112354545109673

theorem tailTrace_1979343 : CollatzResearch.WordTrace tailWord_1979343 prefixEnd_1979343 1016354339112354545109673 := by
  unfold tailWord_1979343
  simp only [CollatzResearch.WordTrace]
  refine ⟨72192570068185830716382683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48128380045457220477588455 72192570068185830716382683)
  ·
    refine ⟨108288855102278746074574025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72192570068185830716382683 108288855102278746074574025)
    ·
      refine ⟨81216641326709059555930519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108288855102278746074574025 81216641326709059555930519)
      ·
        refine ⟨121824961990063589333895779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81216641326709059555930519 121824961990063589333895779)
        ·
          refine ⟨182737442985095384000843669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121824961990063589333895779 182737442985095384000843669)
          ·
            refine ⟨8565817639926346125039547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 182737442985095384000843669 8565817639926346125039547)
            ·
              refine ⟨12848726459889519187559321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8565817639926346125039547 12848726459889519187559321)
              ·
                refine ⟨9636544844917139390669491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12848726459889519187559321 9636544844917139390669491)
                ·
                  refine ⟨14454817267375709086004237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9636544844917139390669491 14454817267375709086004237)
                  ·
                    refine ⟨5420556475265890907251589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14454817267375709086004237 5420556475265890907251589)
                    ·
                      refine ⟨1016354339112354545109673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5420556475265890907251589 1016354339112354545109673)
                      ·
                        rfl

theorem cell23_1979343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_1979343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979343 prefixEnd_1979343 := by exact prefixLift 1979343
  have htrace : WordTrace (prefixWord ++ tailWord_1979343) baseStart_1979343 baseEnd_1979343 := by
    simpa [prefixWord, tailWord_1979343, baseEnd_1979343] using wordTrace_append hprefix tailTrace_1979343
  have hstable : (prefixWord ++ tailWord_1979343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979343).length < 2 ^ (prefixWord ++ tailWord_1979343).sum := by decide
  have hdescent : baseEnd_1979343 < baseStart_1979343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979400 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 6]
def baseStart_1979400 : Nat := 118140960795 + 1979400 * 2 ^ 59
def prefixEnd_1979400 : Nat := 4983230072969 + 3 ^ 40 * 1979400 * 2
def baseEnd_1979400 : Nat := 112931511945517869121879

theorem tailTrace_1979400 : CollatzResearch.WordTrace tailWord_1979400 prefixEnd_1979400 112931511945517869121879 := by
  unfold tailWord_1979400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36097324514489664725603827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48129766019319552967471769 36097324514489664725603827)
  ·
    refine ⟨54145986771734497088405741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36097324514489664725603827 54145986771734497088405741)
    ·
      refine ⟨20304745039400436408152153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54145986771734497088405741 20304745039400436408152153)
      ·
        refine ⟨15228558779550327306114115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20304745039400436408152153 15228558779550327306114115)
        ·
          refine ⟨22842838169325490959171173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15228558779550327306114115 22842838169325490959171173)
          ·
            refine ⟨4283032156748529554844595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22842838169325490959171173 4283032156748529554844595)
            ·
              refine ⟨6424548235122794332266893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283032156748529554844595 6424548235122794332266893)
              ·
                refine ⟨2409205588171047874600085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6424548235122794332266893 2409205588171047874600085)
                ·
                  refine ⟨112931511945517869121879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2409205588171047874600085 112931511945517869121879)
                  ·
                    rfl

theorem cell23_1979400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 6].length) (baseStart_1979400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979400 prefixEnd_1979400 := by exact prefixLift 1979400
  have htrace : WordTrace (prefixWord ++ tailWord_1979400) baseStart_1979400 baseEnd_1979400 := by
    simpa [prefixWord, tailWord_1979400, baseEnd_1979400] using wordTrace_append hprefix tailTrace_1979400
  have hstable : (prefixWord ++ tailWord_1979400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979400).length < 2 ^ (prefixWord ++ tailWord_1979400).sum := by decide
  have hdescent : baseEnd_1979400 < baseStart_1979400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979443 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 5, 6]
def baseStart_1979443 : Nat := 118140960795 + 1979443 * 2 ^ 59
def prefixEnd_1979443 : Nat := 4983230072969 + 3 ^ 40 * 1979443 * 2
def baseEnd_1979443 : Nat := 338801895725934717953071

theorem tailTrace_1979443 : CollatzResearch.WordTrace tailWord_1979443 prefixEnd_1979443 338801895725934717953071 := by
  unfold tailWord_1979443
  simp only [CollatzResearch.WordTrace]
  refine ⟨72196217367823547795022983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48130811578549031863348655 72196217367823547795022983)
  ·
    refine ⟨108294326051735321692534475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72196217367823547795022983 108294326051735321692534475)
    ·
      refine ⟨162441489077602982538801713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108294326051735321692534475 162441489077602982538801713)
      ·
        refine ⟨121831116808202236904101285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162441489077602982538801713 121831116808202236904101285)
        ·
          refine ⟨22843334401537919419518991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121831116808202236904101285 22843334401537919419518991)
          ·
            refine ⟨34265001602306879129278487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22843334401537919419518991 34265001602306879129278487)
            ·
              refine ⟨51397502403460318693917731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34265001602306879129278487 51397502403460318693917731)
              ·
                refine ⟨77096253605190478040876597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51397502403460318693917731 77096253605190478040876597)
                ·
                  refine ⟨7227773775486607316332181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77096253605190478040876597 7227773775486607316332181)
                  ·
                    refine ⟨338801895725934717953071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7227773775486607316332181 338801895725934717953071)
                    ·
                      rfl

theorem cell23_1979443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 6].length) (baseStart_1979443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979443 prefixEnd_1979443 := by exact prefixLift 1979443
  have htrace : WordTrace (prefixWord ++ tailWord_1979443) baseStart_1979443 baseEnd_1979443 := by
    simpa [prefixWord, tailWord_1979443, baseEnd_1979443] using wordTrace_append hprefix tailTrace_1979443
  have hstable : (prefixWord ++ tailWord_1979443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979443).length < 2 ^ (prefixWord ++ tailWord_1979443).sum := by decide
  have hdescent : baseEnd_1979443 < baseStart_1979443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979450 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1979450 : Nat := 118140960795 + 1979450 * 2 ^ 59
def prefixEnd_1979450 : Nat := 4983230072969 + 3 ^ 40 * 1979450 * 2
def baseEnd_1979450 : Nat := 1016409281542385626471681

theorem tailTrace_1979450 : CollatzResearch.WordTrace tailWord_1979450 prefixEnd_1979450 1016409281542385626471681 := by
  unfold tailWord_1979450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049118169699546997631951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48130981785865458660351869 18049118169699546997631951)
  ·
    refine ⟨27073677254549320496447927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18049118169699546997631951 27073677254549320496447927)
    ·
      refine ⟨40610515881823980744671891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27073677254549320496447927 40610515881823980744671891)
      ·
        refine ⟨60915773822735971117007837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40610515881823980744671891 60915773822735971117007837)
        ·
          refine ⟨22843415183525989168877939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60915773822735971117007837 22843415183525989168877939)
          ·
            refine ⟨34265122775288983753316909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22843415183525989168877939 34265122775288983753316909)
            ·
              refine ⟨12849421040733368907493841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34265122775288983753316909 12849421040733368907493841)
              ·
                refine ⟨9637065780550026680620381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12849421040733368907493841 9637065780550026680620381)
                ·
                  refine ⟨3613899667706260005232643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9637065780550026680620381 3613899667706260005232643)
                  ·
                    refine ⟨5420849501559390007848965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3613899667706260005232643 5420849501559390007848965)
                    ·
                      refine ⟨1016409281542385626471681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5420849501559390007848965 1016409281542385626471681)
                      ·
                        rfl

theorem cell23_1979450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1979450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979450 prefixEnd_1979450 := by exact prefixLift 1979450
  have htrace : WordTrace (prefixWord ++ tailWord_1979450) baseStart_1979450 baseEnd_1979450 := by
    simpa [prefixWord, tailWord_1979450, baseEnd_1979450] using wordTrace_append hprefix tailTrace_1979450
  have hstable : (prefixWord ++ tailWord_1979450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979450).length < 2 ^ (prefixWord ++ tailWord_1979450).sum := by decide
  have hdescent : baseEnd_1979450 < baseStart_1979450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979473 : List Nat := [1, 2, 2, 1, 3, 1, 2, 11]
def baseStart_1979473 : Nat := 118140960795 + 1979473 * 2 ^ 59
def prefixEnd_1979473 : Nat := 4983230072969 + 3 ^ 40 * 1979473 * 2
def baseEnd_1979473 : Nat := 37645225614719964314225

theorem tailTrace_1979473 : CollatzResearch.WordTrace tailWord_1979473 prefixEnd_1979473 37645225614719964314225 := by
  unfold tailWord_1979473
  simp only [CollatzResearch.WordTrace]
  refine ⟨72197311557714862918615073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48131541038476575279076715 72197311557714862918615073)
  ·
    refine ⟨54147983668286147188961305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72197311557714862918615073 54147983668286147188961305)
    ·
      refine ⟨40610987751214610391720979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54147983668286147188961305 40610987751214610391720979)
      ·
        refine ⟨60916481626821915587581469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40610987751214610391720979 60916481626821915587581469)
        ·
          refine ⟨22843680610058218345343051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60916481626821915587581469 22843680610058218345343051)
          ·
            refine ⟨34265520915087327518014577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22843680610058218345343051 34265520915087327518014577)
            ·
              refine ⟨25699140686315495638510933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34265520915087327518014577 25699140686315495638510933)
              ·
                refine ⟨37645225614719964314225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25699140686315495638510933 37645225614719964314225)
                ·
                  rfl

theorem cell23_1979473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 11].length) (baseStart_1979473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979473 prefixEnd_1979473 := by exact prefixLift 1979473
  have htrace : WordTrace (prefixWord ++ tailWord_1979473) baseStart_1979473 baseEnd_1979473 := by
    simpa [prefixWord, tailWord_1979473, baseEnd_1979473] using wordTrace_append hprefix tailTrace_1979473
  have hstable : (prefixWord ++ tailWord_1979473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979473).length < 2 ^ (prefixWord ++ tailWord_1979473).sum := by decide
  have hdescent : baseEnd_1979473 < baseStart_1979473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979480 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1979480 : Nat := 118140960795 + 1979480 * 2 ^ 59
def prefixEnd_1979480 : Nat := 4983230072969 + 3 ^ 40 * 1979480 * 2
def baseEnd_1979480 : Nat := 1016424685962020509096543

theorem tailTrace_1979480 : CollatzResearch.WordTrace tailWord_1979480 prefixEnd_1979480 1016424685962020509096543 := by
  unfold tailWord_1979480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36098783434344751557059947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48131711245793002076079929 36098783434344751557059947)
  ·
    refine ⟨54148175151517127335589921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36098783434344751557059947 54148175151517127335589921)
    ·
      refine ⟨40611131363637845501692441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54148175151517127335589921 40611131363637845501692441)
      ·
        refine ⟨30458348522728384126269331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40611131363637845501692441 30458348522728384126269331)
        ·
          refine ⟨45687522784092576189403997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30458348522728384126269331 45687522784092576189403997)
          ·
            refine ⟨17132821044034716071026499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45687522784092576189403997 17132821044034716071026499)
            ·
              refine ⟨25699231566052074106539749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17132821044034716071026499 25699231566052074106539749)
              ·
                refine ⟨4818605918634763894976203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25699231566052074106539749 4818605918634763894976203)
                ·
                  refine ⟨7227908877952145842464305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818605918634763894976203 7227908877952145842464305)
                  ·
                    refine ⟨5420931658464109381848229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7227908877952145842464305 5420931658464109381848229)
                    ·
                      refine ⟨1016424685962020509096543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5420931658464109381848229 1016424685962020509096543)
                      ·
                        rfl

theorem cell23_1979480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1979480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979480 prefixEnd_1979480 := by exact prefixLift 1979480
  have htrace : WordTrace (prefixWord ++ tailWord_1979480) baseStart_1979480 baseEnd_1979480 := by
    simpa [prefixWord, tailWord_1979480, baseEnd_1979480] using wordTrace_append hprefix tailTrace_1979480
  have hstable : (prefixWord ++ tailWord_1979480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979480).length < 2 ^ (prefixWord ++ tailWord_1979480).sum := by decide
  have hdescent : baseEnd_1979480 < baseStart_1979480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979484 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_1979484 : Nat := 118140960795 + 1979484 * 2 ^ 59
def prefixEnd_1979484 : Nat := 4983230072969 + 3 ^ 40 * 1979484 * 2
def baseEnd_1979484 : Nat := 1016426739884638493446525

theorem tailTrace_1979484 : CollatzResearch.WordTrace tailWord_1979484 prefixEnd_1979484 1016426739884638493446525 := by
  unfold tailWord_1979484
  simp only [CollatzResearch.WordTrace]
  refine ⟨36098856380337505898632753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48131808507116674531510337 36098856380337505898632753)
  ·
    refine ⟨27074142285253129423974565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36098856380337505898632753 27074142285253129423974565)
    ·
      refine ⟨5076401678484961766995231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27074142285253129423974565 5076401678484961766995231)
      ·
        refine ⟨7614602517727442650492847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5076401678484961766995231 7614602517727442650492847)
        ·
          refine ⟨11421903776591163975739271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614602517727442650492847 11421903776591163975739271)
          ·
            refine ⟨17132855664886745963608907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421903776591163975739271 17132855664886745963608907)
            ·
              refine ⟨25699283497330118945413361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17132855664886745963608907 25699283497330118945413361)
              ·
                refine ⟨19274462622997589209060021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25699283497330118945413361 19274462622997589209060021)
                ·
                  refine ⟨1806980870906023988349377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19274462622997589209060021 1806980870906023988349377)
                  ·
                    refine ⟨1355235653179517991262033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1806980870906023988349377 1355235653179517991262033)
                    ·
                      refine ⟨1016426739884638493446525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1355235653179517991262033 1016426739884638493446525)
                      ·
                        rfl

theorem cell23_1979484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_1979484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979484 prefixEnd_1979484 := by exact prefixLift 1979484
  have htrace : WordTrace (prefixWord ++ tailWord_1979484) baseStart_1979484 baseEnd_1979484 := by
    simpa [prefixWord, tailWord_1979484, baseEnd_1979484] using wordTrace_append hprefix tailTrace_1979484
  have hstable : (prefixWord ++ tailWord_1979484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979484).length < 2 ^ (prefixWord ++ tailWord_1979484).sum := by decide
  have hdescent : baseEnd_1979484 < baseStart_1979484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979487 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 3]
def baseStart_1979487 : Nat := 118140960795 + 1979487 * 2 ^ 59
def prefixEnd_1979487 : Nat := 4983230072969 + 3 ^ 40 * 1979487 * 2
def baseEnd_1979487 : Nat := 1016428280326601981709011

theorem tailTrace_1979487 : CollatzResearch.WordTrace tailWord_1979487 prefixEnd_1979487 1016428280326601981709011 := by
  unfold tailWord_1979487
  simp only [CollatzResearch.WordTrace]
  refine ⟨72197822179664143309624715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48131881453109428873083143 72197822179664143309624715)
  ·
    refine ⟨108296733269496214964437073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72197822179664143309624715 108296733269496214964437073)
    ·
      refine ⟨81222549952122161223327805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108296733269496214964437073 81222549952122161223327805)
      ·
        refine ⟨30458456232045810458747927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81222549952122161223327805 30458456232045810458747927)
        ·
          refine ⟨45687684348068715688121891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30458456232045810458747927 45687684348068715688121891)
          ·
            refine ⟨68531526522103073532182837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45687684348068715688121891 68531526522103073532182837)
            ·
              refine ⟨6424830611447163143642141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68531526522103073532182837 6424830611447163143642141)
              ·
                refine ⟨2409311479292686178865803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6424830611447163143642141 2409311479292686178865803)
                ·
                  refine ⟨3613967218939029268298705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409311479292686178865803 3613967218939029268298705)
                  ·
                    refine ⟨2710475414204271951224029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3613967218939029268298705 2710475414204271951224029)
                    ·
                      refine ⟨1016428280326601981709011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2710475414204271951224029 1016428280326601981709011)
                      ·
                        rfl

theorem cell23_1979487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_1979487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979487 prefixEnd_1979487 := by exact prefixLift 1979487
  have htrace : WordTrace (prefixWord ++ tailWord_1979487) baseStart_1979487 baseEnd_1979487 := by
    simpa [prefixWord, tailWord_1979487, baseEnd_1979487] using wordTrace_append hprefix tailTrace_1979487
  have hstable : (prefixWord ++ tailWord_1979487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979487).length < 2 ^ (prefixWord ++ tailWord_1979487).sum := by decide
  have hdescent : baseEnd_1979487 < baseStart_1979487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979501 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_1979501 : Nat := 118140960795 + 1979501 * 2 ^ 59
def prefixEnd_1979501 : Nat := 4983230072969 + 3 ^ 40 * 1979501 * 2
def baseEnd_1979501 : Nat := 1016435469055764926933947

theorem tailTrace_1979501 : CollatzResearch.WordTrace tailWord_1979501 prefixEnd_1979501 1016435469055764926933947 := by
  unfold tailWord_1979501
  simp only [CollatzResearch.WordTrace]
  refine ⟨72198332801613423700634357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48132221867742282467089571 72198332801613423700634357)
  ·
    refine ⟨6768593700151258471934471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72198332801613423700634357 6768593700151258471934471)
    ·
      refine ⟨10152890550226887707901707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768593700151258471934471 10152890550226887707901707)
      ·
        refine ⟨15229335825340331561852561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10152890550226887707901707 15229335825340331561852561)
        ·
          refine ⟨11422001869005248671389421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15229335825340331561852561 11422001869005248671389421)
          ·
            refine ⟨4283250700876968251771033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11422001869005248671389421 4283250700876968251771033)
            ·
              refine ⟨3212438025657726188828275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283250700876968251771033 3212438025657726188828275)
              ·
                refine ⟨4818657038486589283242413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212438025657726188828275 4818657038486589283242413)
                ·
                  refine ⟨1806996389432470981215905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4818657038486589283242413 1806996389432470981215905)
                  ·
                    refine ⟨1355247292074353235911929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1806996389432470981215905 1355247292074353235911929)
                    ·
                      refine ⟨1016435469055764926933947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1355247292074353235911929 1016435469055764926933947)
                      ·
                        rfl

theorem cell23_1979501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_1979501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979501 prefixEnd_1979501 := by exact prefixLift 1979501
  have htrace : WordTrace (prefixWord ++ tailWord_1979501) baseStart_1979501 baseEnd_1979501 := by
    simpa [prefixWord, tailWord_1979501, baseEnd_1979501] using wordTrace_append hprefix tailTrace_1979501
  have hstable : (prefixWord ++ tailWord_1979501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979501).length < 2 ^ (prefixWord ++ tailWord_1979501).sum := by decide
  have hdescent : baseEnd_1979501 < baseStart_1979501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979530 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1979530 : Nat := 118140960795 + 1979530 * 2 ^ 59
def prefixEnd_1979530 : Nat := 4983230072969 + 3 ^ 40 * 1979530 * 2
def baseEnd_1979530 : Nat := 1016450359994745313471313

theorem tailTrace_1979530 : CollatzResearch.WordTrace tailWord_1979530 prefixEnd_1979530 1016450359994745313471313 := by
  unfold tailWord_1979530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049847629627090413360011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48132927012338907768960029 18049847629627090413360011)
  ·
    refine ⟨27074771444440635620040017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18049847629627090413360011 27074771444440635620040017)
    ·
      refine ⟨20306078583330476715030013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27074771444440635620040017 20306078583330476715030013)
      ·
        refine ⟨7614779468748928768136255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20306078583330476715030013 7614779468748928768136255)
        ·
          refine ⟨11422169203123393152204383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614779468748928768136255 11422169203123393152204383)
          ·
            refine ⟨17133253804685089728306575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422169203123393152204383 17133253804685089728306575)
            ·
              refine ⟨25699880707027634592459863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17133253804685089728306575 25699880707027634592459863)
              ·
                refine ⟨38549821060541451888689795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25699880707027634592459863 38549821060541451888689795)
                ·
                  refine ⟨57824731590812177833034693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38549821060541451888689795 57824731590812177833034693)
                  ·
                    refine ⟨10842137173277283343694005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57824731590812177833034693 10842137173277283343694005)
                    ·
                      refine ⟨1016450359994745313471313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10842137173277283343694005 1016450359994745313471313)
                      ·
                        rfl

theorem cell23_1979530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1979530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979530 prefixEnd_1979530 := by exact prefixLift 1979530
  have htrace : WordTrace (prefixWord ++ tailWord_1979530) baseStart_1979530 baseEnd_1979530 := by
    simpa [prefixWord, tailWord_1979530, baseEnd_1979530] using wordTrace_append hprefix tailTrace_1979530
  have hstable : (prefixWord ++ tailWord_1979530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979530).length < 2 ^ (prefixWord ++ tailWord_1979530).sum := by decide
  have hdescent : baseEnd_1979530 < baseStart_1979530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979534 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1979534 : Nat := 118140960795 + 1979534 * 2 ^ 59
def prefixEnd_1979534 : Nat := 4983230072969 + 3 ^ 40 * 1979534 * 2
def baseEnd_1979534 : Nat := 1016452413917363297821295

theorem tailTrace_1979534 : CollatzResearch.WordTrace tailWord_1979534 prefixEnd_1979534 1016452413917363297821295 := by
  unfold tailWord_1979534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9024942051311733792073207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48133024273662580224390437 9024942051311733792073207)
  ·
    refine ⟨13537413076967600688109811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9024942051311733792073207 13537413076967600688109811)
    ·
      refine ⟨20306119615451401032164717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13537413076967600688109811 20306119615451401032164717)
      ·
        refine ⟨7614794855794275387061769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20306119615451401032164717 7614794855794275387061769)
        ·
          refine ⟨5711096141845706540296327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614794855794275387061769 5711096141845706540296327)
          ·
            refine ⟨8566644212768559810444491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711096141845706540296327 8566644212768559810444491)
            ·
              refine ⟨12849966319152839715666737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8566644212768559810444491 12849966319152839715666737)
              ·
                refine ⟨9637474739364629786750053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12849966319152839715666737 9637474739364629786750053)
                ·
                  refine ⟨1807026513630868085015635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9637474739364629786750053 1807026513630868085015635)
                  ·
                    refine ⟨2710539770446302127523453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1807026513630868085015635 2710539770446302127523453)
                    ·
                      refine ⟨1016452413917363297821295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2710539770446302127523453 1016452413917363297821295)
                      ·
                        rfl

theorem cell23_1979534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1979534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979534 prefixEnd_1979534 := by exact prefixLift 1979534
  have htrace : WordTrace (prefixWord ++ tailWord_1979534) baseStart_1979534 baseEnd_1979534 := by
    simpa [prefixWord, tailWord_1979534, baseEnd_1979534] using wordTrace_append hprefix tailTrace_1979534
  have hstable : (prefixWord ++ tailWord_1979534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979534).length < 2 ^ (prefixWord ++ tailWord_1979534).sum := by decide
  have hdescent : baseEnd_1979534 < baseStart_1979534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979608 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 2, 2, 2]
def baseStart_1979608 : Nat := 118140960795 + 1979608 * 2 ^ 59
def prefixEnd_1979608 : Nat := 4983230072969 + 3 ^ 40 * 1979608 * 2
def baseEnd_1979608 : Nat := 1016490411485796008295955

theorem tailTrace_1979608 : CollatzResearch.WordTrace tailWord_1979608 prefixEnd_1979608 1016490411485796008295955 := by
  unfold tailWord_1979608
  simp only [CollatzResearch.WordTrace]
  refine ⟨36101117706112890487389739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48134823608150520649852985 36101117706112890487389739)
  ·
    refine ⟨54151676559169335731084609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36101117706112890487389739 54151676559169335731084609)
    ·
      refine ⟨40613757419377001798313457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54151676559169335731084609 40613757419377001798313457)
      ·
        refine ⟨30460318064532751348735093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40613757419377001798313457 30460318064532751348735093)
        ·
          refine ⟨2855654818549945438943915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30460318064532751348735093 2855654818549945438943915)
          ·
            refine ⟨4283482227824918158415873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855654818549945438943915 4283482227824918158415873)
            ·
              refine ⟨3212611670868688618811905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283482227824918158415873 3212611670868688618811905)
              ·
                refine ⟨2409458753151516464108929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212611670868688618811905 2409458753151516464108929)
                ·
                  refine ⟨1807094064863637348081697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409458753151516464108929 1807094064863637348081697)
                  ·
                    refine ⟨1355320548647728011061273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1807094064863637348081697 1355320548647728011061273)
                    ·
                      refine ⟨1016490411485796008295955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1355320548647728011061273 1016490411485796008295955)
                      ·
                        rfl

theorem cell23_1979608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_1979608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979608 prefixEnd_1979608 := by exact prefixLift 1979608
  have htrace : WordTrace (prefixWord ++ tailWord_1979608) baseStart_1979608 baseEnd_1979608 := by
    simpa [prefixWord, tailWord_1979608, baseEnd_1979608] using wordTrace_append hprefix tailTrace_1979608
  have hstable : (prefixWord ++ tailWord_1979608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979608).length < 2 ^ (prefixWord ++ tailWord_1979608).sum := by decide
  have hdescent : baseEnd_1979608 < baseStart_1979608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979610 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_1979610 : Nat := 118140960795 + 1979610 * 2 ^ 59
def prefixEnd_1979610 : Nat := 4983230072969 + 3 ^ 40 * 1979610 * 2
def baseEnd_1979610 : Nat := 338830479482368333490315

theorem tailTrace_1979610 : CollatzResearch.WordTrace tailWord_1979610 prefixEnd_1979610 338830479482368333490315 := by
  unfold tailWord_1979610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050577089554633829088071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48134872238812356877568189 18050577089554633829088071)
  ·
    refine ⟨27075865634331950743632107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18050577089554633829088071 27075865634331950743632107)
    ·
      refine ⟨40613798451497926115448161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27075865634331950743632107 40613798451497926115448161)
      ·
        refine ⟨30460348838623444586586121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40613798451497926115448161 30460348838623444586586121)
        ·
          refine ⟨22845261628967583439939591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30460348838623444586586121 22845261628967583439939591)
          ·
            refine ⟨34267892443451375159909387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22845261628967583439939591 34267892443451375159909387)
            ·
              refine ⟨51401838665177062739864081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34267892443451375159909387 51401838665177062739864081)
              ·
                refine ⟨38551378998882797054898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51401838665177062739864081 38551378998882797054898061)
                ·
                  refine ⟨14456767124581048895586773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38551378998882797054898061 14456767124581048895586773)
                  ·
                    refine ⟨338830479482368333490315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14456767124581048895586773 338830479482368333490315)
                    ·
                      rfl

theorem cell23_1979610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_1979610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979610 prefixEnd_1979610 := by exact prefixLift 1979610
  have htrace : WordTrace (prefixWord ++ tailWord_1979610) baseStart_1979610 baseEnd_1979610 := by
    simpa [prefixWord, tailWord_1979610, baseEnd_1979610] using wordTrace_append hprefix tailTrace_1979610
  have hstable : (prefixWord ++ tailWord_1979610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979610).length < 2 ^ (prefixWord ++ tailWord_1979610).sum := by decide
  have hdescent : baseEnd_1979610 < baseStart_1979610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979647 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_1979647 : Nat := 118140960795 + 1979647 * 2 ^ 59
def prefixEnd_1979647 : Nat := 4983230072969 + 3 ^ 40 * 1979647 * 2
def baseEnd_1979647 : Nat := 1016510437231321355708275

theorem tailTrace_1979647 : CollatzResearch.WordTrace tailWord_1979647 prefixEnd_1979647 1016510437231321355708275 := by
  unfold tailWord_1979647
  simp only [CollatzResearch.WordTrace]
  refine ⟨72203657859084490635449195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48135771906056327090299463 72203657859084490635449195)
  ·
    refine ⟨108305486788626735953173793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72203657859084490635449195 108305486788626735953173793)
    ·
      refine ⟨81229115091470051964880345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108305486788626735953173793 81229115091470051964880345)
      ·
        refine ⟨60921836318602538973660259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81229115091470051964880345 60921836318602538973660259)
        ·
          refine ⟨91382754477903808460490389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60921836318602538973660259 91382754477903808460490389)
          ·
            refine ⟨4283566616151741021585487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91382754477903808460490389 4283566616151741021585487)
            ·
              refine ⟨6425349924227611532378231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283566616151741021585487 6425349924227611532378231)
              ·
                refine ⟨9638024886341417298567347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425349924227611532378231 9638024886341417298567347)
                ·
                  refine ⟨14457037329512125947851021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9638024886341417298567347 14457037329512125947851021)
                  ·
                    refine ⟨5421388998567047230444133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14457037329512125947851021 5421388998567047230444133)
                    ·
                      refine ⟨1016510437231321355708275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5421388998567047230444133 1016510437231321355708275)
                      ·
                        rfl

theorem cell23_1979647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_1979647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979647 prefixEnd_1979647 := by exact prefixLift 1979647
  have htrace : WordTrace (prefixWord ++ tailWord_1979647) baseStart_1979647 baseEnd_1979647 := by
    simpa [prefixWord, tailWord_1979647, baseEnd_1979647] using wordTrace_append hprefix tailTrace_1979647
  have hstable : (prefixWord ++ tailWord_1979647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979647).length < 2 ^ (prefixWord ++ tailWord_1979647).sum := by decide
  have hdescent : baseEnd_1979647 < baseStart_1979647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979657 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 5, 4]
def baseStart_1979657 : Nat := 118140960795 + 1979657 * 2 ^ 59
def prefixEnd_1979657 : Nat := 4983230072969 + 3 ^ 40 * 1979657 * 2
def baseEnd_1979657 : Nat := 338838524012622105527743

theorem tailTrace_1979657 : CollatzResearch.WordTrace tailWord_1979657 prefixEnd_1979657 338838524012622105527743 := by
  unfold tailWord_1979657
  simp only [CollatzResearch.WordTrace]
  refine ⟨72204022589048262343313225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48136015059365508228875483 72204022589048262343313225)
  ·
    refine ⟨54153016941786196757484919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72204022589048262343313225 54153016941786196757484919)
    ·
      refine ⟨81229525412679295136227379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54153016941786196757484919 81229525412679295136227379)
      ·
        refine ⟨121844288119018942704341069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81229525412679295136227379 121844288119018942704341069)
        ·
          refine ⟨45691608044632103514127901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121844288119018942704341069 45691608044632103514127901)
          ·
            refine ⟨17134353016737038817797963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45691608044632103514127901 17134353016737038817797963)
            ·
              refine ⟨25701529525105558226696945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17134353016737038817797963 25701529525105558226696945)
              ·
                refine ⟨19276147143829168670022709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25701529525105558226696945 19276147143829168670022709)
                ·
                  refine ⟨1807138794733984562814629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19276147143829168670022709 1807138794733984562814629)
                  ·
                    refine ⟨338838524012622105527743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807138794733984562814629 338838524012622105527743)
                    ·
                      rfl

theorem cell23_1979657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_1979657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979657 prefixEnd_1979657 := by exact prefixLift 1979657
  have htrace : WordTrace (prefixWord ++ tailWord_1979657) baseStart_1979657 baseEnd_1979657 := by
    simpa [prefixWord, tailWord_1979657, baseEnd_1979657] using wordTrace_append hprefix tailTrace_1979657
  have hstable : (prefixWord ++ tailWord_1979657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979657).length < 2 ^ (prefixWord ++ tailWord_1979657).sum := by decide
  have hdescent : baseEnd_1979657 < baseStart_1979657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979674 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_1979674 : Nat := 118140960795 + 1979674 * 2 ^ 59
def prefixEnd_1979674 : Nat := 4983230072969 + 3 ^ 40 * 1979674 * 2
def baseEnd_1979674 : Nat := 338841433736330916690217

theorem tailTrace_1979674 : CollatzResearch.WordTrace tailWord_1979674 prefixEnd_1979674 338841433736330916690217 := by
  unfold tailWord_1979674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051160657496668561670519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48136428419991116164454717 18051160657496668561670519)
  ·
    refine ⟨27076740986245002842505779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18051160657496668561670519 27076740986245002842505779)
    ·
      refine ⟨40615111479367504263758669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27076740986245002842505779 40615111479367504263758669)
      ·
        refine ⟨15230666804762814098909501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40615111479367504263758669 15230666804762814098909501)
        ·
          refine ⟨5711500051786055287091063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15230666804762814098909501 5711500051786055287091063)
          ·
            refine ⟨8567250077679082930636595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711500051786055287091063 8567250077679082930636595)
            ·
              refine ⟨12850875116518624395954893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567250077679082930636595 12850875116518624395954893)
              ·
                refine ⟨4819078168694484148483085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12850875116518624395954893 4819078168694484148483085)
                ·
                  refine ⟨1807154313260431555681157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4819078168694484148483085 1807154313260431555681157)
                  ·
                    refine ⟨338841433736330916690217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807154313260431555681157 338841433736330916690217)
                    ·
                      rfl

theorem cell23_1979674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_1979674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979674 prefixEnd_1979674 := by exact prefixLift 1979674
  have htrace : WordTrace (prefixWord ++ tailWord_1979674) baseStart_1979674 baseEnd_1979674 := by
    simpa [prefixWord, tailWord_1979674, baseEnd_1979674] using wordTrace_append hprefix tailTrace_1979674
  have hstable : (prefixWord ++ tailWord_1979674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979674).length < 2 ^ (prefixWord ++ tailWord_1979674).sum := by decide
  have hdescent : baseEnd_1979674 < baseStart_1979674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979708 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1979708 : Nat := 118140960795 + 1979708 * 2 ^ 59
def prefixEnd_1979708 : Nat := 4983230072969 + 3 ^ 40 * 1979708 * 2
def baseEnd_1979708 : Nat := 338847253183748539015165

theorem tailTrace_1979708 : CollatzResearch.WordTrace tailWord_1979708 prefixEnd_1979708 338847253183748539015165 := by
  unfold tailWord_1979708
  simp only [CollatzResearch.WordTrace]
  refine ⟨36102941355931749026709889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48137255141242332035613185 36102941355931749026709889)
  ·
    refine ⟨27077206016948811770032417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36102941355931749026709889 27077206016948811770032417)
    ·
      refine ⟨20307904512711608827524313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27077206016948811770032417 20307904512711608827524313)
      ·
        refine ⟨15230928384533706620643235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20307904512711608827524313 15230928384533706620643235)
        ·
          refine ⟨22846392576800559930964853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15230928384533706620643235 22846392576800559930964853)
          ·
            refine ⟨2141849304075052493527955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22846392576800559930964853 2141849304075052493527955)
            ·
              refine ⟨3212773956112578740291933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141849304075052493527955 3212773956112578740291933)
              ·
                refine ⟨1204790233542217027609475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212773956112578740291933 1204790233542217027609475)
                ·
                  refine ⟨1807185350313325541414213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204790233542217027609475 1807185350313325541414213)
                  ·
                    refine ⟨338847253183748539015165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807185350313325541414213 338847253183748539015165)
                    ·
                      rfl

theorem cell23_1979708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1979708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979708 prefixEnd_1979708 := by exact prefixLift 1979708
  have htrace : WordTrace (prefixWord ++ tailWord_1979708) baseStart_1979708 baseEnd_1979708 := by
    simpa [prefixWord, tailWord_1979708, baseEnd_1979708] using wordTrace_append hprefix tailTrace_1979708
  have hstable : (prefixWord ++ tailWord_1979708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979708).length < 2 ^ (prefixWord ++ tailWord_1979708).sum := by decide
  have hdescent : baseEnd_1979708 < baseStart_1979708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979725 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1979725 : Nat := 118140960795 + 1979725 * 2 ^ 59
def prefixEnd_1979725 : Nat := 4983230072969 + 3 ^ 40 * 1979725 * 2
def baseEnd_1979725 : Nat := 338850162907457350177639

theorem tailTrace_1979725 : CollatzResearch.WordTrace tailWord_1979725 prefixEnd_1979725 338850162907457350177639 := by
  unfold tailWord_1979725
  simp only [CollatzResearch.WordTrace]
  refine ⟨72206502752801909956788629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48137668501867939971192419 72206502752801909956788629)
  ·
    refine ⟨3384679816537589529224467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72206502752801909956788629 3384679816537589529224467)
    ·
      refine ⟨5077019724806384293836701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3384679816537589529224467 5077019724806384293836701)
      ·
        refine ⟨1903882396802394110188763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5077019724806384293836701 1903882396802394110188763)
        ·
          refine ⟨2855823595203591165283145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903882396802394110188763 2855823595203591165283145)
          ·
            refine ⟨2141867696402693373962359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855823595203591165283145 2141867696402693373962359)
            ·
              refine ⟨3212801544604040060943539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141867696402693373962359 3212801544604040060943539)
              ·
                refine ⟨4819202316906060091415309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212801544604040060943539 4819202316906060091415309)
                ·
                  refine ⟨1807200868839772534280741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4819202316906060091415309 1807200868839772534280741)
                  ·
                    refine ⟨338850162907457350177639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807200868839772534280741 338850162907457350177639)
                    ·
                      rfl

theorem cell23_1979725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1979725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979725 prefixEnd_1979725 := by exact prefixLift 1979725
  have htrace : WordTrace (prefixWord ++ tailWord_1979725) baseStart_1979725 baseEnd_1979725 := by
    simpa [prefixWord, tailWord_1979725, baseEnd_1979725] using wordTrace_append hprefix tailTrace_1979725
  have hstable : (prefixWord ++ tailWord_1979725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979725).length < 2 ^ (prefixWord ++ tailWord_1979725).sum := by decide
  have hdescent : baseEnd_1979725 < baseStart_1979725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979771 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 1, 1, 4]
def baseStart_1979771 : Nat := 118140960795 + 1979771 * 2 ^ 59
def prefixEnd_1979771 : Nat := 4983230072969 + 3 ^ 40 * 1979771 * 2
def baseEnd_1979771 : Nat := 1016574108832478870557705

theorem tailTrace_1979771 : CollatzResearch.WordTrace tailWord_1979771 prefixEnd_1979771 1016574108832478870557705 := by
  unfold tailWord_1979771
  simp only [CollatzResearch.WordTrace]
  refine ⟨72208180510635259812963167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48138787007090173208642111 72208180510635259812963167)
  ·
    refine ⟨108312270765952889719444751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72208180510635259812963167 108312270765952889719444751)
    ·
      refine ⟨162468406148929334579167127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108312270765952889719444751 162468406148929334579167127)
      ·
        refine ⟨243702609223394001868750691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162468406148929334579167127 243702609223394001868750691)
        ·
          refine ⟨365553913835091002803126037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243702609223394001868750691 365553913835091002803126037)
          ·
            refine ⟨17135339711019890756396533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 365553913835091002803126037 17135339711019890756396533)
            ·
              refine ⟨1606438097908114758412175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17135339711019890756396533 1606438097908114758412175)
              ·
                refine ⟨2409657146862172137618263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606438097908114758412175 2409657146862172137618263)
                ·
                  refine ⟨3614485720293258206427395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409657146862172137618263 3614485720293258206427395)
                  ·
                    refine ⟨5421728580439887309641093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3614485720293258206427395 5421728580439887309641093)
                    ·
                      refine ⟨1016574108832478870557705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5421728580439887309641093 1016574108832478870557705)
                      ·
                        rfl

theorem cell23_1979771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 1, 4].length) (baseStart_1979771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979771 prefixEnd_1979771 := by exact prefixLift 1979771
  have htrace : WordTrace (prefixWord ++ tailWord_1979771) baseStart_1979771 baseEnd_1979771 := by
    simpa [prefixWord, tailWord_1979771, baseEnd_1979771] using wordTrace_append hprefix tailTrace_1979771
  have hstable : (prefixWord ++ tailWord_1979771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979771).length < 2 ^ (prefixWord ++ tailWord_1979771).sum := by decide
  have hdescent : baseEnd_1979771 < baseStart_1979771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979777 : List Nat := [1, 2, 4, 3, 13]
def baseStart_1979777 : Nat := 118140960795 + 1979777 * 2 ^ 59
def prefixEnd_1979777 : Nat := 4983230072969 + 3 ^ 40 * 1979777 * 2
def baseEnd_1979777 : Nat := 1394481741723464810813

theorem tailTrace_1979777 : CollatzResearch.WordTrace tailWord_1979777 prefixEnd_1979777 1394481741723464810813 := by
  unfold tailWord_1979777
  simp only [CollatzResearch.WordTrace]
  refine ⟨72208399348613522837681585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48138932899075681891787723 72208399348613522837681585)
  ·
    refine ⟨54156299511460142128261189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72208399348613522837681585 54156299511460142128261189)
    ·
      refine ⟨10154306158398776649048973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54156299511460142128261189 10154306158398776649048973)
      ·
        refine ⟨3807864809399541243393365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10154306158398776649048973 3807864809399541243393365)
        ·
          refine ⟨1394481741723464810813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3807864809399541243393365 1394481741723464810813)
          ·
            rfl

theorem cell23_1979777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 13].length) (baseStart_1979777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979777 prefixEnd_1979777 := by exact prefixLift 1979777
  have htrace : WordTrace (prefixWord ++ tailWord_1979777) baseStart_1979777 baseEnd_1979777 := by
    simpa [prefixWord, tailWord_1979777, baseEnd_1979777] using wordTrace_append hprefix tailTrace_1979777
  have hstable : (prefixWord ++ tailWord_1979777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979777).length < 2 ^ (prefixWord ++ tailWord_1979777).sum := by decide
  have hdescent : baseEnd_1979777 < baseStart_1979777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979797 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1979797 : Nat := 118140960795 + 1979797 * 2 ^ 59
def prefixEnd_1979797 : Nat := 4983230072969 + 3 ^ 40 * 1979797 * 2
def baseEnd_1979797 : Nat := 1016587459329495768832585

theorem tailTrace_1979797 : CollatzResearch.WordTrace tailWord_1979797 prefixEnd_1979797 1016587459329495768832585 := by
  unfold tailWord_1979797
  simp only [CollatzResearch.WordTrace]
  refine ⟨72209128808541066253409645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48139419205694044168939763 72209128808541066253409645)
  ·
    refine ⟨27078423303202899845028617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72209128808541066253409645 27078423303202899845028617)
    ·
      refine ⟨20308817477402174883771463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27078423303202899845028617 20308817477402174883771463)
      ·
        refine ⟨30463226216103262325657195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20308817477402174883771463 30463226216103262325657195)
        ·
          refine ⟨45694839324154893488485793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30463226216103262325657195 45694839324154893488485793)
          ·
            refine ⟨34271129493116170116364345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45694839324154893488485793 34271129493116170116364345)
            ·
              refine ⟨25703347119837127587273259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34271129493116170116364345 25703347119837127587273259)
              ·
                refine ⟨38555020679755691380909889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25703347119837127587273259 38555020679755691380909889)
                ·
                  refine ⟨28916265509816768535682417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38555020679755691380909889 28916265509816768535682417)
                  ·
                    refine ⟨21687199132362576401761813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28916265509816768535682417 21687199132362576401761813)
                    ·
                      refine ⟨1016587459329495768832585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21687199132362576401761813 1016587459329495768832585)
                      ·
                        rfl

theorem cell23_1979797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1979797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979797 prefixEnd_1979797 := by exact prefixLift 1979797
  have htrace : WordTrace (prefixWord ++ tailWord_1979797) baseStart_1979797 baseEnd_1979797 := by
    simpa [prefixWord, tailWord_1979797, baseEnd_1979797] using wordTrace_append hprefix tailTrace_1979797
  have hstable : (prefixWord ++ tailWord_1979797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979797).length < 2 ^ (prefixWord ++ tailWord_1979797).sum := by decide
  have hdescent : baseEnd_1979797 < baseStart_1979797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979842 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1979842 : Nat := 118140960795 + 1979842 * 2 ^ 59
def prefixEnd_1979842 : Nat := 4983230072969 + 3 ^ 40 * 1979842 * 2
def baseEnd_1979842 : Nat := 1016610565958948092769879

theorem tailTrace_1979842 : CollatzResearch.WordTrace tailWord_1979842 prefixEnd_1979842 1016610565958948092769879 := by
  unfold tailWord_1979842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052692523344509734699445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48140513395585359292531853 18052692523344509734699445)
  ·
    refine ⟨1692439924063547787628073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18052692523344509734699445 1692439924063547787628073)
    ·
      refine ⟨1269329943047660840721055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1692439924063547787628073 1269329943047660840721055)
      ·
        refine ⟨1903994914571491261081583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269329943047660840721055 1903994914571491261081583)
        ·
          refine ⟨2855992371857236891622375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903994914571491261081583 2855992371857236891622375)
          ·
            refine ⟨4283988557785855337433563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855992371857236891622375 4283988557785855337433563)
            ·
              refine ⟨6425982836678783006150345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4283988557785855337433563 6425982836678783006150345)
              ·
                refine ⟨4819487127509087254612759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6425982836678783006150345 4819487127509087254612759)
                ·
                  refine ⟨7229230691263630881919139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4819487127509087254612759 7229230691263630881919139)
                  ·
                    refine ⟨10843846036895446322878709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7229230691263630881919139 10843846036895446322878709)
                    ·
                      refine ⟨1016610565958948092769879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10843846036895446322878709 1016610565958948092769879)
                      ·
                        rfl

theorem cell23_1979842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1979842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979842 prefixEnd_1979842 := by exact prefixLift 1979842
  have htrace : WordTrace (prefixWord ++ tailWord_1979842) baseStart_1979842 baseEnd_1979842 := by
    simpa [prefixWord, tailWord_1979842, baseEnd_1979842] using wordTrace_append hprefix tailTrace_1979842
  have hstable : (prefixWord ++ tailWord_1979842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979842).length < 2 ^ (prefixWord ++ tailWord_1979842).sum := by decide
  have hdescent : baseEnd_1979842 < baseStart_1979842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979854 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1979854 : Nat := 118140960795 + 1979854 * 2 ^ 59
def prefixEnd_1979854 : Nat := 4983230072969 + 3 ^ 40 * 1979854 * 2
def baseEnd_1979854 : Nat := 338872242575600681939941

theorem tailTrace_1979854 : CollatzResearch.WordTrace tailWord_1979854 prefixEnd_1979854 338872242575600681939941 := by
  unfold tailWord_1979854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026400971166820623529327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48140805179556376658823077 9026400971166820623529327)
  ·
    refine ⟨13539601456750230935293991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9026400971166820623529327 13539601456750230935293991)
    ·
      refine ⟨20309402185125346402940987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13539601456750230935293991 20309402185125346402940987)
      ·
        refine ⟨30464103277688019604411481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20309402185125346402940987 30464103277688019604411481)
        ·
          refine ⟨22848077458266014703308611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30464103277688019604411481 22848077458266014703308611)
          ·
            refine ⟨34272116187399022054962917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22848077458266014703308611 34272116187399022054962917)
            ·
              refine ⟨6426021785137316635305547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34272116187399022054962917 6426021785137316635305547)
              ·
                refine ⟨9639032677705974952958321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426021785137316635305547 9639032677705974952958321)
                ·
                  refine ⟨7229274508279481214718741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9639032677705974952958321 7229274508279481214718741)
                  ·
                    refine ⟨338872242575600681939941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7229274508279481214718741 338872242575600681939941)
                    ·
                      rfl

theorem cell23_1979854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1979854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979854 prefixEnd_1979854 := by exact prefixLift 1979854
  have htrace : WordTrace (prefixWord ++ tailWord_1979854) baseStart_1979854 baseEnd_1979854 := by
    simpa [prefixWord, tailWord_1979854, baseEnd_1979854] using wordTrace_append hprefix tailTrace_1979854
  have hstable : (prefixWord ++ tailWord_1979854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979854).length < 2 ^ (prefixWord ++ tailWord_1979854).sum := by decide
  have hdescent : baseEnd_1979854 < baseStart_1979854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979864 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1979864 : Nat := 118140960795 + 1979864 * 2 ^ 59
def prefixEnd_1979864 : Nat := 4983230072969 + 3 ^ 40 * 1979864 * 2
def baseEnd_1979864 : Nat := 1016621862533347006694777

theorem tailTrace_1979864 : CollatzResearch.WordTrace tailWord_1979864 prefixEnd_1979864 1016621862533347006694777 := by
  unfold tailWord_1979864
  simp only [CollatzResearch.WordTrace]
  refine ⟨36105786249649168348049323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48141048332865557797399097 36105786249649168348049323)
  ·
    refine ⟨54158679374473752522073985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36105786249649168348049323 54158679374473752522073985)
    ·
      refine ⟨40619009530855314391555489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54158679374473752522073985 40619009530855314391555489)
      ·
        refine ⟨30464257148141485793666617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40619009530855314391555489 30464257148141485793666617)
        ·
          refine ⟨22848192861106114345249963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30464257148141485793666617 22848192861106114345249963)
          ·
            refine ⟨34272289291659171517874945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22848192861106114345249963 34272289291659171517874945)
            ·
              refine ⟨25704216968744378638406209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34272289291659171517874945 25704216968744378638406209)
              ·
                refine ⟨19278162726558283978804657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25704216968744378638406209 19278162726558283978804657)
                ·
                  refine ⟨14458622044918712984103493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19278162726558283978804657 14458622044918712984103493)
                  ·
                    refine ⟨2710991633422258684519405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14458622044918712984103493 2710991633422258684519405)
                    ·
                      refine ⟨1016621862533347006694777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2710991633422258684519405 1016621862533347006694777)
                      ·
                        rfl

theorem cell23_1979864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1979864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979864 prefixEnd_1979864 := by exact prefixLift 1979864
  have htrace : WordTrace (prefixWord ++ tailWord_1979864) baseStart_1979864 baseEnd_1979864 := by
    simpa [prefixWord, tailWord_1979864, baseEnd_1979864] using wordTrace_append hprefix tailTrace_1979864
  have hstable : (prefixWord ++ tailWord_1979864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979864).length < 2 ^ (prefixWord ++ tailWord_1979864).sum := by decide
  have hdescent : baseEnd_1979864 < baseStart_1979864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979901 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 7]
def baseStart_1979901 : Nat := 118140960795 + 1979901 * 2 ^ 59
def prefixEnd_1979901 : Nat := 4983230072969 + 3 ^ 40 * 1979901 * 2
def baseEnd_1979901 : Nat := 112960095701951484659123

theorem tailTrace_1979901 : CollatzResearch.WordTrace tailWord_1979901 prefixEnd_1979901 112960095701951484659123 := by
  unfold tailWord_1979901
  simp only [CollatzResearch.WordTrace]
  refine ⟨72212922000164292015195557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48141948000109528010130371 72212922000164292015195557)
  ·
    refine ⟨13539922875030804752849167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72212922000164292015195557 13539922875030804752849167)
    ·
      refine ⟨20309884312546207129273751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13539922875030804752849167 20309884312546207129273751)
      ·
        refine ⟨30464826468819310693910627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20309884312546207129273751 30464826468819310693910627)
        ·
          refine ⟨45697239703228966040865941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30464826468819310693910627 45697239703228966040865941)
          ·
            refine ⟨2142058111088857783165591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45697239703228966040865941 2142058111088857783165591)
            ·
              refine ⟨3213087166633286674748387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142058111088857783165591 3213087166633286674748387)
              ·
                refine ⟨4819630749949930012122581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213087166633286674748387 4819630749949930012122581)
                ·
                  refine ⟨112960095701951484659123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4819630749949930012122581 112960095701951484659123)
                  ·
                    rfl

theorem cell23_1979901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_1979901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979901 prefixEnd_1979901 := by exact prefixLift 1979901
  have htrace : WordTrace (prefixWord ++ tailWord_1979901) baseStart_1979901 baseEnd_1979901 := by
    simpa [prefixWord, tailWord_1979901, baseEnd_1979901] using wordTrace_append hprefix tailTrace_1979901
  have hstable : (prefixWord ++ tailWord_1979901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979901).length < 2 ^ (prefixWord ++ tailWord_1979901).sum := by decide
  have hdescent : baseEnd_1979901 < baseStart_1979901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979954 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1979954 : Nat := 118140960795 + 1979954 * 2 ^ 59
def prefixEnd_1979954 : Nat := 4983230072969 + 3 ^ 40 * 1979954 * 2
def baseEnd_1979954 : Nat := 1016668075792251654569363

theorem tailTrace_1979954 : CollatzResearch.WordTrace tailWord_1979954 prefixEnd_1979954 1016668075792251654569363 := by
  unfold tailWord_1979954
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053713767243070516718729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48143236712648188044583277 18053713767243070516718729)
  ·
    refine ⟨13540285325432302887539047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18053713767243070516718729 13540285325432302887539047)
    ·
      refine ⟨20310427988148454331308571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13540285325432302887539047 20310427988148454331308571)
      ·
        refine ⟨30465641982222681496962857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20310427988148454331308571 30465641982222681496962857)
        ·
          refine ⟨22849231486667011122722143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30465641982222681496962857 22849231486667011122722143)
          ·
            refine ⟨34273847230000516684083215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22849231486667011122722143 34273847230000516684083215)
            ·
              refine ⟨51410770845000775026124823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34273847230000516684083215 51410770845000775026124823)
              ·
                refine ⟨77116156267501162539187235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51410770845000775026124823 77116156267501162539187235)
                ·
                  refine ⟨115674234401251743808780853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77116156267501162539187235 115674234401251743808780853)
                  ·
                    refine ⟨10844459475117350982073205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 115674234401251743808780853 10844459475117350982073205)
                    ·
                      refine ⟨1016668075792251654569363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10844459475117350982073205 1016668075792251654569363)
                      ·
                        rfl

theorem cell23_1979954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1979954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979954 prefixEnd_1979954 := by exact prefixLift 1979954
  have htrace : WordTrace (prefixWord ++ tailWord_1979954) baseStart_1979954 baseEnd_1979954 := by
    simpa [prefixWord, tailWord_1979954, baseEnd_1979954] using wordTrace_append hprefix tailTrace_1979954
  have hstable : (prefixWord ++ tailWord_1979954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979954).length < 2 ^ (prefixWord ++ tailWord_1979954).sum := by decide
  have hdescent : baseEnd_1979954 < baseStart_1979954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979994 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1979994 : Nat := 118140960795 + 1979994 * 2 ^ 59
def prefixEnd_1979994 : Nat := 4983230072969 + 3 ^ 40 * 1979994 * 2
def baseEnd_1979994 : Nat := 1016688615018431498069179

theorem tailTrace_1979994 : CollatzResearch.WordTrace tailWord_1979994 prefixEnd_1979994 1016688615018431498069179 := by
  unfold tailWord_1979994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18054078497206842224582759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48144209325884912598887357 18054078497206842224582759)
  ·
    refine ⟨27081117745810263336874139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18054078497206842224582759 27081117745810263336874139)
    ·
      refine ⟨40621676618715395005311209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27081117745810263336874139 40621676618715395005311209)
      ·
        refine ⟨30466257464036546253983407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40621676618715395005311209 30466257464036546253983407)
        ·
          refine ⟨45699386196054819380975111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30466257464036546253983407 45699386196054819380975111)
          ·
            refine ⟨68549079294082229071462667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45699386196054819380975111 68549079294082229071462667)
            ·
              refine ⟨102823618941123343607194001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68549079294082229071462667 102823618941123343607194001)
              ·
                refine ⟨77117714205842507705395501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102823618941123343607194001 77117714205842507705395501)
                ·
                  refine ⟨28919142827190940389523313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77117714205842507705395501 28919142827190940389523313)
                  ·
                    refine ⟨21689357120393205292142485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28919142827190940389523313 21689357120393205292142485)
                    ·
                      refine ⟨1016688615018431498069179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21689357120393205292142485 1016688615018431498069179)
                      ·
                        rfl

theorem cell23_1979994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1979994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1979994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1979994 prefixEnd_1979994 := by exact prefixLift 1979994
  have htrace : WordTrace (prefixWord ++ tailWord_1979994) baseStart_1979994 baseEnd_1979994 := by
    simpa [prefixWord, tailWord_1979994, baseEnd_1979994] using wordTrace_append hprefix tailTrace_1979994
  have hstable : (prefixWord ++ tailWord_1979994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979994).length < 2 ^ (prefixWord ++ tailWord_1979994).sum := by decide
  have hdescent : baseEnd_1979994 < baseStart_1979994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980008 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 6]
def baseStart_1980008 : Nat := 118140960795 + 1980008 * 2 ^ 59
def prefixEnd_1980008 : Nat := 4983230072969 + 3 ^ 40 * 1980008 * 2
def baseEnd_1980008 : Nat := 112966200416399382588235

theorem tailTrace_1980008 : CollatzResearch.WordTrace tailWord_1980008 prefixEnd_1980008 112966200416399382588235 := by
  unfold tailWord_1980008
  simp only [CollatzResearch.WordTrace]
  refine ⟨36108412305388324644670339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48144549740517766192893785 36108412305388324644670339)
  ·
    refine ⟨54162618458082486967005509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36108412305388324644670339 54162618458082486967005509)
    ·
      refine ⟨10155490960890466306313533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54162618458082486967005509 10155490960890466306313533)
      ·
        refine ⟨3808309110333924864867575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10155490960890466306313533 3808309110333924864867575)
        ·
          refine ⟨5712463665500887297301363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808309110333924864867575 5712463665500887297301363)
          ·
            refine ⟨8568695498251330945952045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712463665500887297301363 8568695498251330945952045)
            ·
              refine ⟨3213260811844249104732017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8568695498251330945952045 3213260811844249104732017)
              ·
                refine ⟨2409945608883186828549013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213260811844249104732017 2409945608883186828549013)
                ·
                  refine ⟨112966200416399382588235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2409945608883186828549013 112966200416399382588235)
                  ·
                    rfl

theorem cell23_1980008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 6].length) (baseStart_1980008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980008 prefixEnd_1980008 := by exact prefixLift 1980008
  have htrace : WordTrace (prefixWord ++ tailWord_1980008) baseStart_1980008 baseEnd_1980008 := by
    simpa [prefixWord, tailWord_1980008, baseEnd_1980008] using wordTrace_append hprefix tailTrace_1980008
  have hstable : (prefixWord ++ tailWord_1980008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980008).length < 2 ^ (prefixWord ++ tailWord_1980008).sum := by decide
  have hdescent : baseEnd_1980008 < baseStart_1980008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980041 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_1980041 : Nat := 118140960795 + 1980041 * 2 ^ 59
def prefixEnd_1980041 : Nat := 4983230072969 + 3 ^ 40 * 1980041 * 2
def baseEnd_1980041 : Nat := 1016712748609192814181463

theorem tailTrace_1980041 : CollatzResearch.WordTrace tailWord_1980041 prefixEnd_1980041 1016712748609192814181463 := by
  unfold tailWord_1980041
  simp only [CollatzResearch.WordTrace]
  refine ⟨72218028219657095925291977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48145352146438063950194651 72218028219657095925291977)
  ·
    refine ⟨54163521164742821943968983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72218028219657095925291977 54163521164742821943968983)
    ·
      refine ⟨81245281747114232915953475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54163521164742821943968983 81245281747114232915953475)
      ·
        refine ⟨121867922620671349373930213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81245281747114232915953475 121867922620671349373930213)
        ·
          refine ⟨22850235491375878007611915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121867922620671349373930213 22850235491375878007611915)
          ·
            refine ⟨34275353237063817011417873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22850235491375878007611915 34275353237063817011417873)
            ·
              refine ⟨25706514927797862758563405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34275353237063817011417873 25706514927797862758563405)
              ·
                refine ⟨9639943097924198534461277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25706514927797862758563405 9639943097924198534461277)
                ·
                  refine ⟨3614978661721574450422979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9639943097924198534461277 3614978661721574450422979)
                  ·
                    refine ⟨5422467992582361675634469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3614978661721574450422979 5422467992582361675634469)
                    ·
                      refine ⟨1016712748609192814181463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5422467992582361675634469 1016712748609192814181463)
                      ·
                        rfl

theorem cell23_1980041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_1980041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980041 prefixEnd_1980041 := by exact prefixLift 1980041
  have htrace : WordTrace (prefixWord ++ tailWord_1980041) baseStart_1980041 baseEnd_1980041 := by
    simpa [prefixWord, tailWord_1980041, baseEnd_1980041] using wordTrace_append hprefix tailTrace_1980041
  have hstable : (prefixWord ++ tailWord_1980041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980041).length < 2 ^ (prefixWord ++ tailWord_1980041).sum := by decide
  have hdescent : baseEnd_1980041 < baseStart_1980041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980062 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_1980062 : Nat := 118140960795 + 1980062 * 2 ^ 59
def prefixEnd_1980062 : Nat := 4983230072969 + 3 ^ 40 * 1980062 * 2
def baseEnd_1980062 : Nat := 1016723531702937232018867

theorem tailTrace_1980062 : CollatzResearch.WordTrace tailWord_1980062 prefixEnd_1980062 1016723531702937232018867 := by
  unfold tailWord_1980062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027349269072627063975805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48145862768387344341204293 9027349269072627063975805)
  ·
    refine ⟨3385255975902235148990927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9027349269072627063975805 3385255975902235148990927)
    ·
      refine ⟨5077883963853352723486391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385255975902235148990927 5077883963853352723486391)
      ·
        refine ⟨7616825945780029085229587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077883963853352723486391 7616825945780029085229587)
        ·
          refine ⟨11425238918670043627844381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616825945780029085229587 11425238918670043627844381)
          ·
            refine ⟨4284464594501266360441643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11425238918670043627844381 4284464594501266360441643)
            ·
              refine ⟨6426696891751899540662465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284464594501266360441643 6426696891751899540662465)
              ·
                refine ⟨4820022668813924655496849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426696891751899540662465 4820022668813924655496849)
                ·
                  refine ⟨3615017001610443491622637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4820022668813924655496849 3615017001610443491622637)
                  ·
                    refine ⟨1355631375603916309358489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3615017001610443491622637 1355631375603916309358489)
                    ·
                      refine ⟨1016723531702937232018867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1355631375603916309358489 1016723531702937232018867)
                      ·
                        rfl

theorem cell23_1980062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_1980062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980062 prefixEnd_1980062 := by exact prefixLift 1980062
  have htrace : WordTrace (prefixWord ++ tailWord_1980062) baseStart_1980062 baseEnd_1980062 := by
    simpa [prefixWord, tailWord_1980062, baseEnd_1980062] using wordTrace_append hprefix tailTrace_1980062
  have hstable : (prefixWord ++ tailWord_1980062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980062).length < 2 ^ (prefixWord ++ tailWord_1980062).sum := by decide
  have hdescent : baseEnd_1980062 < baseStart_1980062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980068 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_1980068 : Nat := 118140960795 + 1980068 * 2 ^ 59
def prefixEnd_1980068 : Nat := 4983230072969 + 3 ^ 40 * 1980068 * 2
def baseEnd_1980068 : Nat := 338908870862288069514613

theorem tailTrace_1980068 : CollatzResearch.WordTrace tailWord_1980068 prefixEnd_1980068 338908870862288069514613 := by
  unfold tailWord_1980068
  simp only [CollatzResearch.WordTrace]
  refine ⟨36109506495279639768262429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48146008660372853024349905 36109506495279639768262429)
  ·
    refine ⟨13541064935729864913098411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36109506495279639768262429 13541064935729864913098411)
    ·
      refine ⟨20311597403594797369647617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13541064935729864913098411 20311597403594797369647617)
      ·
        refine ⟨15233698052696098027235713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20311597403594797369647617 15233698052696098027235713)
        ·
          refine ⟨11425273539522073520426785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15233698052696098027235713 11425273539522073520426785)
          ·
            refine ⟨8568955154641555140320089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11425273539522073520426785 8568955154641555140320089)
            ·
              refine ⟨6426716365981166355240067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8568955154641555140320089 6426716365981166355240067)
              ·
                refine ⟨9640074548971749532860101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6426716365981166355240067 9640074548971749532860101)
                ·
                  refine ⟨1807513977932203037411269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9640074548971749532860101 1807513977932203037411269)
                  ·
                    refine ⟨338908870862288069514613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807513977932203037411269 338908870862288069514613)
                    ·
                      rfl

theorem cell23_1980068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_1980068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980068 prefixEnd_1980068 := by exact prefixLift 1980068
  have htrace : WordTrace (prefixWord ++ tailWord_1980068) baseStart_1980068 baseEnd_1980068 := by
    simpa [prefixWord, tailWord_1980068, baseEnd_1980068] using wordTrace_append hprefix tailTrace_1980068
  have hstable : (prefixWord ++ tailWord_1980068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980068).length < 2 ^ (prefixWord ++ tailWord_1980068).sum := by decide
  have hdescent : baseEnd_1980068 < baseStart_1980068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
