import V185TrunkScan23Chunk1098

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6507272 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_6507272 : Nat := 118140960795 + 6507272 * 2 ^ 59
def prefixEnd_6507272 : Nat := 4983230072969 + 3 ^ 40 * 6507272 * 2
def baseEnd_6507272 : Nat := 3341358285544169502073607

theorem tailTrace_6507272 : CollatzResearch.WordTrace tailWord_6507272 prefixEnd_6507272 3341358285544169502073607 := by
  unfold tailWord_6507272
  simp only [CollatzResearch.WordTrace]
  refine ⟨118669854040636186211666035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158226472054181581615554713 118669854040636186211666035)
  ·
    refine ⟨178004781060954279317499053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118669854040636186211666035 178004781060954279317499053)
    ·
      refine ⟨66751792897857854744062145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178004781060954279317499053 66751792897857854744062145)
      ·
        refine ⟨50063844673393391058046609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66751792897857854744062145 50063844673393391058046609)
        ·
          refine ⟨37547883505045043293534957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50063844673393391058046609 37547883505045043293534957)
          ·
            refine ⟨14080456314391891235075609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37547883505045043293534957 14080456314391891235075609)
            ·
              refine ⟨10560342235793918426306707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14080456314391891235075609 10560342235793918426306707)
              ·
                refine ⟨15840513353690877639460061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10560342235793918426306707 15840513353690877639460061)
                ·
                  refine ⟨5940192507634079114797523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15840513353690877639460061 5940192507634079114797523)
                  ·
                    refine ⟨8910288761451118672196285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5940192507634079114797523 8910288761451118672196285)
                    ·
                      refine ⟨3341358285544169502073607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8910288761451118672196285 3341358285544169502073607)
                      ·
                        rfl

theorem cell23_6507272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_6507272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507272 prefixEnd_6507272 := by exact prefixLift 6507272
  have htrace : WordTrace (prefixWord ++ tailWord_6507272) baseStart_6507272 baseEnd_6507272 := by
    simpa [prefixWord, tailWord_6507272, baseEnd_6507272] using wordTrace_append hprefix tailTrace_6507272
  have hstable : (prefixWord ++ tailWord_6507272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507272).length < 2 ^ (prefixWord ++ tailWord_6507272).sum := by decide
  have hdescent : baseEnd_6507272 < baseStart_6507272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507295 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 4]
def baseStart_6507295 : Nat := 118140960795 + 6507295 * 2 ^ 59
def prefixEnd_6507295 : Nat := 4983230072969 + 3 ^ 40 * 6507295 * 2
def baseEnd_6507295 : Nat := 3341370095599222912086001

theorem tailTrace_6507295 : CollatzResearch.WordTrace tailWord_6507295 prefixEnd_6507295 3341370095599222912086001 := by
  unfold tailWord_6507295
  simp only [CollatzResearch.WordTrace]
  refine ⟨237340546960189047351419339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158227031306792698234279559 237340546960189047351419339)
  ·
    refine ⟨356010820440283571027129009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237340546960189047351419339 356010820440283571027129009)
    ·
      refine ⟨267008115330212678270346757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356010820440283571027129009 267008115330212678270346757)
      ·
        refine ⟨50064021624414877175690017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267008115330212678270346757 50064021624414877175690017)
        ·
          refine ⟨37548016218311157881767513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50064021624414877175690017 37548016218311157881767513)
          ·
            refine ⟨28161012163733368411325635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37548016218311157881767513 28161012163733368411325635)
            ·
              refine ⟨42241518245600052616988453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28161012163733368411325635 42241518245600052616988453)
              ·
                refine ⟨7920284671050009865685335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42241518245600052616988453 7920284671050009865685335)
                ·
                  refine ⟨11880427006575014798528003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7920284671050009865685335 11880427006575014798528003)
                  ·
                    refine ⟨17820640509862522197792005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11880427006575014798528003 17820640509862522197792005)
                    ·
                      refine ⟨3341370095599222912086001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17820640509862522197792005 3341370095599222912086001)
                      ·
                        rfl

theorem cell23_6507295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_6507295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507295 prefixEnd_6507295 := by exact prefixLift 6507295
  have htrace : WordTrace (prefixWord ++ tailWord_6507295) baseStart_6507295 baseEnd_6507295 := by
    simpa [prefixWord, tailWord_6507295, baseEnd_6507295] using wordTrace_append hprefix tailTrace_6507295
  have hstable : (prefixWord ++ tailWord_6507295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507295).length < 2 ^ (prefixWord ++ tailWord_6507295).sum := by decide
  have hdescent : baseEnd_6507295 < baseStart_6507295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507308 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_6507308 : Nat := 118140960795 + 6507308 * 2 ^ 59
def prefixEnd_6507308 : Nat := 4983230072969 + 3 ^ 40 * 6507308 * 2
def baseEnd_6507308 : Nat := 3341376770847731361223441

theorem tailTrace_6507308 : CollatzResearch.WordTrace tailWord_6507308 prefixEnd_6507308 3341376770847731361223441 := by
  unfold tailWord_6507308
  simp only [CollatzResearch.WordTrace]
  refine ⟨118670510554570975285821289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158227347406094633714428385 118670510554570975285821289)
  ·
    refine ⟨89002882915928231464365967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118670510554570975285821289 89002882915928231464365967)
    ·
      refine ⟨133504324373892347196548951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89002882915928231464365967 133504324373892347196548951)
      ·
        refine ⟨200256486560838520794823427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133504324373892347196548951 200256486560838520794823427)
        ·
          refine ⟨300384729841257781192235141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200256486560838520794823427 300384729841257781192235141)
          ·
            refine ⟨56322136845235833973544089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300384729841257781192235141 56322136845235833973544089)
            ·
              refine ⟨42241602633926875480158067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56322136845235833973544089 42241602633926875480158067)
              ·
                refine ⟨63362403950890313220237101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42241602633926875480158067 63362403950890313220237101)
                ·
                  refine ⟨23760901481583867457588913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63362403950890313220237101 23760901481583867457588913)
                  ·
                    refine ⟨17820676111187900593191685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23760901481583867457588913 17820676111187900593191685)
                    ·
                      refine ⟨3341376770847731361223441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17820676111187900593191685 3341376770847731361223441)
                      ·
                        rfl

theorem cell23_6507308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_6507308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507308 prefixEnd_6507308 := by exact prefixLift 6507308
  have htrace : WordTrace (prefixWord ++ tailWord_6507308) baseStart_6507308 baseEnd_6507308 := by
    simpa [prefixWord, tailWord_6507308, baseEnd_6507308] using wordTrace_append hprefix tailTrace_6507308
  have hstable : (prefixWord ++ tailWord_6507308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507308).length < 2 ^ (prefixWord ++ tailWord_6507308).sum := by decide
  have hdescent : baseEnd_6507308 < baseStart_6507308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507315 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 5]
def baseStart_6507315 : Nat := 118140960795 + 6507315 * 2 ^ 59
def prefixEnd_6507315 : Nat := 4983230072969 + 3 ^ 40 * 6507315 * 2
def baseEnd_6507315 : Nat := 3341380365212312833835909

theorem tailTrace_6507315 : CollatzResearch.WordTrace tailWord_6507315 prefixEnd_6507315 3341380365212312833835909 := by
  unfold tailWord_6507315
  simp only [CollatzResearch.WordTrace]
  refine ⟨237341276420116590767147399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158227517613411060511431599 237341276420116590767147399)
  ·
    refine ⟨356011914630174886150721099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237341276420116590767147399 356011914630174886150721099)
    ·
      refine ⟨534017871945262329226081649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356011914630174886150721099 534017871945262329226081649)
      ·
        refine ⟨400513403958946746919561237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534017871945262329226081649 400513403958946746919561237)
        ·
          refine ⟨18774065810575628761854433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 400513403958946746919561237 18774065810575628761854433)
          ·
            refine ⟨14080549357931721571390825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18774065810575628761854433 14080549357931721571390825)
            ·
              refine ⟨10560412018448791178543119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14080549357931721571390825 10560412018448791178543119)
              ·
                refine ⟨15840618027673186767814679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10560412018448791178543119 15840618027673186767814679)
                ·
                  refine ⟨23760927041509780151722019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15840618027673186767814679 23760927041509780151722019)
                  ·
                    refine ⟨35641390562264670227583029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23760927041509780151722019 35641390562264670227583029)
                    ·
                      refine ⟨3341380365212312833835909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35641390562264670227583029 3341380365212312833835909)
                      ·
                        rfl

theorem cell23_6507315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_6507315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507315 prefixEnd_6507315 := by exact prefixLift 6507315
  have htrace : WordTrace (prefixWord ++ tailWord_6507315) baseStart_6507315 baseEnd_6507315 := by
    simpa [prefixWord, tailWord_6507315, baseEnd_6507315] using wordTrace_append hprefix tailTrace_6507315
  have hstable : (prefixWord ++ tailWord_6507315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507315).length < 2 ^ (prefixWord ++ tailWord_6507315).sum := by decide
  have hdescent : baseEnd_6507315 < baseStart_6507315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507388 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_6507388 : Nat := 118140960795 + 6507388 * 2 ^ 59
def prefixEnd_6507388 : Nat := 4983230072969 + 3 ^ 40 * 6507388 * 2
def baseEnd_6507388 : Nat := 3341417849300091048223073

theorem tailTrace_6507388 : CollatzResearch.WordTrace tailWord_6507388 prefixEnd_6507388 3341417849300091048223073 := by
  unfold tailWord_6507388
  simp only [CollatzResearch.WordTrace]
  refine ⟨118671969474426062117277409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158229292632568082823036545 118671969474426062117277409)
  ·
    refine ⟨89003977105819546587958057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118671969474426062117277409 89003977105819546587958057)
    ·
      refine ⟨66752982829364659940968543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89003977105819546587958057 66752982829364659940968543)
      ·
        refine ⟨100129474244046989911452815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66752982829364659940968543 100129474244046989911452815)
        ·
          refine ⟨150194211366070484867179223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100129474244046989911452815 150194211366070484867179223)
          ·
            refine ⟨225291317049105727300768835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150194211366070484867179223 225291317049105727300768835)
            ·
              refine ⟨337936975573658590951153253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225291317049105727300768835 337936975573658590951153253)
              ·
                refine ⟨63363182920060985803341235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337936975573658590951153253 63363182920060985803341235)
                ·
                  refine ⟨95044774380091478705011853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63363182920060985803341235 95044774380091478705011853)
                  ·
                    refine ⟨35641790392534304514379445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95044774380091478705011853 35641790392534304514379445)
                    ·
                      refine ⟨3341417849300091048223073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35641790392534304514379445 3341417849300091048223073)
                      ·
                        rfl

theorem cell23_6507388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_6507388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507388 prefixEnd_6507388 := by exact prefixLift 6507388
  have htrace : WordTrace (prefixWord ++ tailWord_6507388) baseStart_6507388 baseEnd_6507388 := by
    simpa [prefixWord, tailWord_6507388, baseEnd_6507388] using wordTrace_append hprefix tailTrace_6507388
  have hstable : (prefixWord ++ tailWord_6507388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507388).length < 2 ^ (prefixWord ++ tailWord_6507388).sum := by decide
  have hdescent : baseEnd_6507388 < baseStart_6507388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507453 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_6507453 : Nat := 118140960795 + 6507453 * 2 ^ 59
def prefixEnd_6507453 : Nat := 4983230072969 + 3 ^ 40 * 6507453 * 2
def baseEnd_6507453 : Nat := 3341451225542633293910275

theorem tailTrace_6507453 : CollatzResearch.WordTrace tailWord_6507453 prefixEnd_6507453 3341451225542633293910275 := by
  unfold tailWord_6507453
  simp only [CollatzResearch.WordTrace]
  refine ⟨237346309693616640335671013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158230873129077760223780675 237346309693616640335671013)
  ·
    refine ⟨44502433067553120062938315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237346309693616640335671013 44502433067553120062938315)
    ·
      refine ⟨66753649601329680094407473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44502433067553120062938315 66753649601329680094407473)
      ·
        refine ⟨50065237200997260070805605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66753649601329680094407473 50065237200997260070805605)
        ·
          refine ⟨9387231975186986263276051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50065237200997260070805605 9387231975186986263276051)
          ·
            refine ⟨14080847962780479394914077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387231975186986263276051 14080847962780479394914077)
            ·
              refine ⟨5280317986042679773092779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14080847962780479394914077 5280317986042679773092779)
              ·
                refine ⟨7920476979064019659639169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280317986042679773092779 7920476979064019659639169)
                ·
                  refine ⟨5940357734298014744729377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7920476979064019659639169 5940357734298014744729377)
                  ·
                    refine ⟨4455268300723511058547033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5940357734298014744729377 4455268300723511058547033)
                    ·
                      refine ⟨3341451225542633293910275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455268300723511058547033 3341451225542633293910275)
                      ·
                        rfl

theorem cell23_6507453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_6507453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507453 prefixEnd_6507453 := by exact prefixLift 6507453
  have htrace : WordTrace (prefixWord ++ tailWord_6507453) baseStart_6507453 baseEnd_6507453 := by
    simpa [prefixWord, tailWord_6507453, baseEnd_6507453] using wordTrace_append hprefix tailTrace_6507453
  have hstable : (prefixWord ++ tailWord_6507453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507453).length < 2 ^ (prefixWord ++ tailWord_6507453).sum := by decide
  have hdescent : baseEnd_6507453 < baseStart_6507453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507492 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_6507492 : Nat := 118140960795 + 6507492 * 2 ^ 59
def prefixEnd_6507492 : Nat := 4983230072969 + 3 ^ 40 * 6507492 * 2
def baseEnd_6507492 : Nat := 3341471251288158641322595

theorem tailTrace_6507492 : CollatzResearch.WordTrace tailWord_6507492 prefixEnd_6507492 3341471251288158641322595 := by
  unfold tailWord_6507492
  simp only [CollatzResearch.WordTrace]
  refine ⟨118673866070237674998170365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158231821426983566664227153 118673866070237674998170365)
  ·
    refine ⟨44502699776339128124313887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118673866070237674998170365 44502699776339128124313887)
    ·
      refine ⟨66754049664508692186470831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44502699776339128124313887 66754049664508692186470831)
      ·
        refine ⟨100131074496763038279706247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66754049664508692186470831 100131074496763038279706247)
        ·
          refine ⟨150196611745144557419559371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100131074496763038279706247 150196611745144557419559371)
          ·
            refine ⟨225294917617716836129339057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150196611745144557419559371 225294917617716836129339057)
            ·
              refine ⟨168971188213287627097004293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225294917617716836129339057 168971188213287627097004293)
              ·
                refine ⟨31682097789991430080688305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168971188213287627097004293 31682097789991430080688305)
                ·
                  refine ⟨23761573342493572560516229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31682097789991430080688305 23761573342493572560516229)
                  ·
                    refine ⟨4455295001717544855096793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23761573342493572560516229 4455295001717544855096793)
                    ·
                      refine ⟨3341471251288158641322595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455295001717544855096793 3341471251288158641322595)
                      ·
                        rfl

theorem cell23_6507492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_6507492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507492 prefixEnd_6507492 := by exact prefixLift 6507492
  have htrace : WordTrace (prefixWord ++ tailWord_6507492) baseStart_6507492 baseEnd_6507492 := by
    simpa [prefixWord, tailWord_6507492, baseEnd_6507492] using wordTrace_append hprefix tailTrace_6507492
  have hstable : (prefixWord ++ tailWord_6507492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507492).length < 2 ^ (prefixWord ++ tailWord_6507492).sum := by decide
  have hdescent : baseEnd_6507492 < baseStart_6507492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507549 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 6]
def baseStart_6507549 : Nat := 118140960795 + 6507549 * 2 ^ 59
def prefixEnd_6507549 : Nat := 4983230072969 + 3 ^ 40 * 6507549 * 2
def baseEnd_6507549 : Nat := 371277835520607213145537

theorem tailTrace_6507549 : CollatzResearch.WordTrace tailWord_6507549 prefixEnd_6507549 371277835520607213145537 := by
  unfold tailWord_6507549
  simp only [CollatzResearch.WordTrace]
  refine ⟨237349811101268848731165701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158233207400845899154110467 237349811101268848731165701)
  ·
    refine ⟨44503089581487909137093569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237349811101268848731165701 44503089581487909137093569)
    ·
      refine ⟨33377317186115931852820177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44503089581487909137093569 33377317186115931852820177)
      ·
        refine ⟨25032987889586948889615133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33377317186115931852820177 25032987889586948889615133)
        ·
          refine ⟨9387370458595105833605675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25032987889586948889615133 9387370458595105833605675)
          ·
            refine ⟨14081055687892658750408513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387370458595105833605675 14081055687892658750408513)
            ·
              refine ⟨10560791765919494062806385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14081055687892658750408513 10560791765919494062806385)
              ·
                refine ⟨7920593824439620547104789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560791765919494062806385 7920593824439620547104789)
                ·
                  refine ⟨371277835520607213145537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7920593824439620547104789 371277835520607213145537)
                  ·
                    rfl

theorem cell23_6507549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_6507549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507549 prefixEnd_6507549 := by exact prefixLift 6507549
  have htrace : WordTrace (prefixWord ++ tailWord_6507549) baseStart_6507549 baseEnd_6507549 := by
    simpa [prefixWord, tailWord_6507549, baseEnd_6507549] using wordTrace_append hprefix tailTrace_6507549
  have hstable : (prefixWord ++ tailWord_6507549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507549).length < 2 ^ (prefixWord ++ tailWord_6507549).sum := by decide
  have hdescent : baseEnd_6507549 < baseStart_6507549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507553 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 1, 4]
def baseStart_6507553 : Nat := 118140960795 + 6507553 * 2 ^ 59
def prefixEnd_6507553 : Nat := 4983230072969 + 3 ^ 40 * 6507553 * 2
def baseEnd_6507553 : Nat := 1113834191202694300886605

theorem tailTrace_6507553 : CollatzResearch.WordTrace tailWord_6507553 prefixEnd_6507553 1113834191202694300886605 := by
  unfold tailWord_6507553
  simp only [CollatzResearch.WordTrace]
  refine ⟨237349956993254357414311313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158233304662169571609540875 237349956993254357414311313)
  ·
    refine ⟨178012467744940768060733485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237349956993254357414311313 178012467744940768060733485)
    ·
      refine ⟨66754675404352788022775057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178012467744940768060733485 66754675404352788022775057)
      ·
        refine ⟨50066006553264591017081293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66754675404352788022775057 50066006553264591017081293)
        ·
          refine ⟨18774752457474221631405485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50066006553264591017081293 18774752457474221631405485)
          ·
            refine ⟨7040532171552833111777057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18774752457474221631405485 7040532171552833111777057)
            ·
              refine ⟨5280399128664624833832793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040532171552833111777057 5280399128664624833832793)
              ·
                refine ⟨3960299346498468625374595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280399128664624833832793 3960299346498468625374595)
                ·
                  refine ⟨5940449019747702938061893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960299346498468625374595 5940449019747702938061893)
                  ·
                    refine ⟨1113834191202694300886605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5940449019747702938061893 1113834191202694300886605)
                    ·
                      rfl

theorem cell23_6507553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_6507553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507553 prefixEnd_6507553 := by exact prefixLift 6507553
  have htrace : WordTrace (prefixWord ++ tailWord_6507553) baseStart_6507553 baseEnd_6507553 := by
    simpa [prefixWord, tailWord_6507553, baseEnd_6507553] using wordTrace_append hprefix tailTrace_6507553
  have hstable : (prefixWord ++ tailWord_6507553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507553).length < 2 ^ (prefixWord ++ tailWord_6507553).sum := by decide
  have hdescent : baseEnd_6507553 < baseStart_6507553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507592 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 4, 4]
def baseStart_6507592 : Nat := 118140960795 + 6507592 * 2 ^ 59
def prefixEnd_6507592 : Nat := 4983230072969 + 3 ^ 40 * 6507592 * 2
def baseEnd_6507592 : Nat := 1113840866451202750024045

theorem tailTrace_6507592 : CollatzResearch.WordTrace tailWord_6507592 prefixEnd_6507592 1113840866451202750024045 := by
  unfold tailWord_6507592
  simp only [CollatzResearch.WordTrace]
  refine ⟨118675689720056533537490515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158234252960075378049987353 118675689720056533537490515)
  ·
    refine ⟨178013534580084800306235773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118675689720056533537490515 178013534580084800306235773)
    ·
      refine ⟨66755075467531800114838415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178013534580084800306235773 66755075467531800114838415)
      ·
        refine ⟨100132613201297700172257623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66755075467531800114838415 100132613201297700172257623)
        ·
          refine ⟨150198919801946550258386435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100132613201297700172257623 150198919801946550258386435)
          ·
            refine ⟨225298379702919825387579653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150198919801946550258386435 225298379702919825387579653)
            ·
              refine ⟨42243446194297467260171185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225298379702919825387579653 42243446194297467260171185)
              ·
                refine ⟨31682584645723100445128389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42243446194297467260171185 31682584645723100445128389)
                ·
                  refine ⟨5940484621073081333461573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31682584645723100445128389 5940484621073081333461573)
                  ·
                    refine ⟨1113840866451202750024045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5940484621073081333461573 1113840866451202750024045)
                    ·
                      rfl

theorem cell23_6507592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_6507592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507592 prefixEnd_6507592 := by exact prefixLift 6507592
  have htrace : WordTrace (prefixWord ++ tailWord_6507592) baseStart_6507592 baseEnd_6507592 := by
    simpa [prefixWord, tailWord_6507592, baseEnd_6507592] using wordTrace_append hprefix tailTrace_6507592
  have hstable : (prefixWord ++ tailWord_6507592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507592).length < 2 ^ (prefixWord ++ tailWord_6507592).sum := by decide
  have hdescent : baseEnd_6507592 < baseStart_6507592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507605 : List Nat := [1, 3, 2, 2, 1, 2, 12]
def baseStart_6507605 : Nat := 118140960795 + 6507605 * 2 ^ 59
def prefixEnd_6507605 : Nat := 4983230072969 + 3 ^ 40 * 6507605 * 2
def baseEnd_6507605 : Nat := 41253447834594033323575

theorem tailTrace_6507605 : CollatzResearch.WordTrace tailWord_6507605 prefixEnd_6507605 41253447834594033323575 := by
  unfold tailWord_6507605
  simp only [CollatzResearch.WordTrace]
  refine ⟨237351853589065970295204269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158234569059377313530136179 237351853589065970295204269)
  ·
    refine ⟨89006945095899738860701601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237351853589065970295204269 89006945095899738860701601)
    ·
      refine ⟨66755208821924804145526201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89006945095899738860701601 66755208821924804145526201)
      ·
        refine ⟨50066406616443603109144651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66755208821924804145526201 50066406616443603109144651)
        ·
          refine ⟨75099609924665404663716977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50066406616443603109144651 75099609924665404663716977)
          ·
            refine ⟨56324707443499053497787733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75099609924665404663716977 56324707443499053497787733)
            ·
              refine ⟨41253447834594033323575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 56324707443499053497787733 41253447834594033323575)
              ·
                rfl

theorem cell23_6507605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 12].length) (baseStart_6507605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507605 prefixEnd_6507605 := by exact prefixLift 6507605
  have htrace : WordTrace (prefixWord ++ tailWord_6507605) baseStart_6507605 baseEnd_6507605 := by
    simpa [prefixWord, tailWord_6507605, baseEnd_6507605] using wordTrace_append hprefix tailTrace_6507605
  have hstable : (prefixWord ++ tailWord_6507605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507605).length < 2 ^ (prefixWord ++ tailWord_6507605).sum := by decide
  have hdescent : baseEnd_6507605 < baseStart_6507605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507612 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6507612 : Nat := 118140960795 + 6507612 * 2 ^ 59
def prefixEnd_6507612 : Nat := 4983230072969 + 3 ^ 40 * 6507612 * 2
def baseEnd_6507612 : Nat := 3341532868966698171822043

theorem tailTrace_6507612 : CollatzResearch.WordTrace tailWord_6507612 prefixEnd_6507612 3341532868966698171822043 := by
  unfold tailWord_6507612
  simp only [CollatzResearch.WordTrace]
  refine ⟨118676054450020305245354545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158234739266693740327139393 118676054450020305245354545)
  ·
    refine ⟨89007040837515228934015909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118676054450020305245354545 89007040837515228934015909)
    ·
      refine ⟨16688820157034105425127983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89007040837515228934015909 16688820157034105425127983)
      ·
        refine ⟨25033230235551158137691975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16688820157034105425127983 25033230235551158137691975)
        ·
          refine ⟨37549845353326737206537963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25033230235551158137691975 37549845353326737206537963)
          ·
            refine ⟨56324768029990105809806945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37549845353326737206537963 56324768029990105809806945)
            ·
              refine ⟨42243576022492579357355209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56324768029990105809806945 42243576022492579357355209)
              ·
                refine ⟨31682682016869434518016407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42243576022492579357355209 31682682016869434518016407)
                ·
                  refine ⟨47524023025304151777024611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31682682016869434518016407 47524023025304151777024611)
                  ·
                    refine ⟨71286034537956227665536917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47524023025304151777024611 71286034537956227665536917)
                    ·
                      refine ⟨3341532868966698171822043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71286034537956227665536917 3341532868966698171822043)
                      ·
                        rfl

theorem cell23_6507612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6507612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507612 prefixEnd_6507612 := by exact prefixLift 6507612
  have htrace : WordTrace (prefixWord ++ tailWord_6507612) baseStart_6507612 baseEnd_6507612 := by
    simpa [prefixWord, tailWord_6507612, baseEnd_6507612] using wordTrace_append hprefix tailTrace_6507612
  have hstable : (prefixWord ++ tailWord_6507612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507612).length < 2 ^ (prefixWord ++ tailWord_6507612).sum := by decide
  have hdescent : baseEnd_6507612 < baseStart_6507612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507616 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 3, 2, 2]
def baseStart_6507616 : Nat := 118140960795 + 6507616 * 2 ^ 59
def prefixEnd_6507616 : Nat := 4983230072969 + 3 ^ 40 * 6507616 * 2
def baseEnd_6507616 : Nat := 3341534922889316156172025

theorem tailTrace_6507616 : CollatzResearch.WordTrace tailWord_6507616 prefixEnd_6507616 3341534922889316156172025 := by
  unfold tailWord_6507616
  simp only [CollatzResearch.WordTrace]
  refine ⟨118676127396013059586927351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158234836528017412782569801 118676127396013059586927351)
  ·
    refine ⟨178014191094019589380391027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118676127396013059586927351 178014191094019589380391027)
    ·
      refine ⟨267021286641029384070586541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178014191094019589380391027 267021286641029384070586541)
      ·
        refine ⟨100132982490386019026469953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267021286641029384070586541 100132982490386019026469953)
        ·
          refine ⟨75099736867789514269852465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100132982490386019026469953 75099736867789514269852465)
          ·
            refine ⟨56324802650842135702389349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75099736867789514269852465 56324802650842135702389349)
            ·
              refine ⟨10560900497032900444198003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56324802650842135702389349 10560900497032900444198003)
              ·
                refine ⟨15841350745549350666297005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10560900497032900444198003 15841350745549350666297005)
                ·
                  refine ⟨5940506529581006499861377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15841350745549350666297005 5940506529581006499861377)
                  ·
                    refine ⟨4455379897185754874896033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5940506529581006499861377 4455379897185754874896033)
                    ·
                      refine ⟨3341534922889316156172025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455379897185754874896033 3341534922889316156172025)
                      ·
                        rfl

theorem cell23_6507616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_6507616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507616 prefixEnd_6507616 := by exact prefixLift 6507616
  have htrace : WordTrace (prefixWord ++ tailWord_6507616) baseStart_6507616 baseEnd_6507616 := by
    simpa [prefixWord, tailWord_6507616, baseEnd_6507616] using wordTrace_append hprefix tailTrace_6507616
  have hstable : (prefixWord ++ tailWord_6507616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507616).length < 2 ^ (prefixWord ++ tailWord_6507616).sum := by decide
  have hdescent : baseEnd_6507616 < baseStart_6507616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507629 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_6507629 : Nat := 118140960795 + 6507629 * 2 ^ 59
def prefixEnd_6507629 : Nat := 4983230072969 + 3 ^ 40 * 6507629 * 2
def baseEnd_6507629 : Nat := 3341541598137824605309465

theorem tailTrace_6507629 : CollatzResearch.WordTrace tailWord_6507629 prefixEnd_6507629 3341541598137824605309465 := by
  unfold tailWord_6507629
  simp only [CollatzResearch.WordTrace]
  refine ⟨237352728940979022394077941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158235152627319348262718627 237352728940979022394077941)
  ·
    refine ⟨22251818338216783349444807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237352728940979022394077941 22251818338216783349444807)
    ·
      refine ⟨33377727507325175024167211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22251818338216783349444807 33377727507325175024167211)
      ·
        refine ⟨50066591260987762536250817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33377727507325175024167211 50066591260987762536250817)
        ·
          refine ⟨37549943445740821902188113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50066591260987762536250817 37549943445740821902188113)
          ·
            refine ⟨28162457584305616426641085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37549943445740821902188113 28162457584305616426641085)
            ·
              refine ⟨10560921594114606159990407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28162457584305616426641085 10560921594114606159990407)
              ·
                refine ⟨15841382391171909239985611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10560921594114606159990407 15841382391171909239985611)
                ·
                  refine ⟨23762073586757863859978417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15841382391171909239985611 23762073586757863859978417)
                  ·
                    refine ⟨17821555190068397894983813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23762073586757863859978417 17821555190068397894983813)
                    ·
                      refine ⟨3341541598137824605309465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17821555190068397894983813 3341541598137824605309465)
                      ·
                        rfl

theorem cell23_6507629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_6507629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507629 prefixEnd_6507629 := by exact prefixLift 6507629
  have htrace : WordTrace (prefixWord ++ tailWord_6507629) baseStart_6507629 baseEnd_6507629 := by
    simpa [prefixWord, tailWord_6507629, baseEnd_6507629] using wordTrace_append hprefix tailTrace_6507629
  have hstable : (prefixWord ++ tailWord_6507629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507629).length < 2 ^ (prefixWord ++ tailWord_6507629).sum := by decide
  have hdescent : baseEnd_6507629 < baseStart_6507629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507666 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_6507666 : Nat := 118140960795 + 6507666 * 2 ^ 59
def prefixEnd_6507666 : Nat := 4983230072969 + 3 ^ 40 * 6507666 * 2
def baseEnd_6507666 : Nat := 3341560596922040960546795

theorem tailTrace_6507666 : CollatzResearch.WordTrace tailWord_6507666 prefixEnd_6507666 3341560596922040960546795 := by
  unfold tailWord_6507666
  simp only [CollatzResearch.WordTrace]
  refine ⟨59338519610461244428293713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158236052294563318475449901 59338519610461244428293713)
  ·
    refine ⟨44503889707845933321220285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59338519610461244428293713 44503889707845933321220285)
    ·
      refine ⟨16688958640442224995457607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44503889707845933321220285 16688958640442224995457607)
      ·
        refine ⟨25033437960663337493186411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16688958640442224995457607 25033437960663337493186411)
        ·
          refine ⟨37550156940995006239779617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25033437960663337493186411 37550156940995006239779617)
          ·
            refine ⟨28162617705746254679834713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37550156940995006239779617 28162617705746254679834713)
            ·
              refine ⟨21121963279309691009876035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28162617705746254679834713 21121963279309691009876035)
              ·
                refine ⟨31682944918964536514814053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21121963279309691009876035 31682944918964536514814053)
                ·
                  refine ⟨5940552172305850596527635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31682944918964536514814053 5940552172305850596527635)
                  ·
                    refine ⟨8910828258458775894791453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5940552172305850596527635 8910828258458775894791453)
                    ·
                      refine ⟨3341560596922040960546795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8910828258458775894791453 3341560596922040960546795)
                      ·
                        rfl

theorem cell23_6507666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_6507666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507666 prefixEnd_6507666 := by exact prefixLift 6507666
  have htrace : WordTrace (prefixWord ++ tailWord_6507666) baseStart_6507666 baseEnd_6507666 := by
    simpa [prefixWord, tailWord_6507666, baseEnd_6507666] using wordTrace_append hprefix tailTrace_6507666
  have hstable : (prefixWord ++ tailWord_6507666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507666).length < 2 ^ (prefixWord ++ tailWord_6507666).sum := by decide
  have hdescent : baseEnd_6507666 < baseStart_6507666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507692 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_6507692 : Nat := 118140960795 + 6507692 * 2 ^ 59
def prefixEnd_6507692 : Nat := 4983230072969 + 3 ^ 40 * 6507692 * 2
def baseEnd_6507692 : Nat := 3341573947419057858821675

theorem tailTrace_6507692 : CollatzResearch.WordTrace tailWord_6507692 prefixEnd_6507692 3341573947419057858821675 := by
  unfold tailWord_6507692
  simp only [CollatzResearch.WordTrace]
  refine ⟨118677513369875392076810665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158236684493167189435747553 118677513369875392076810665)
  ·
    refine ⟨89008135027406544057607999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118677513369875392076810665 89008135027406544057607999)
    ·
      refine ⟨133512202541109816086411999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89008135027406544057607999 133512202541109816086411999)
      ·
        refine ⟨200268303811664724129617999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133512202541109816086411999 200268303811664724129617999)
        ·
          refine ⟨300402455717497086194426999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200268303811664724129617999 300402455717497086194426999)
          ·
            refine ⟨450603683576245629291640499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300402455717497086194426999 450603683576245629291640499)
            ·
              refine ⟨675905525364368443937460749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450603683576245629291640499 675905525364368443937460749)
              ·
                refine ⟨253464572011638166476547781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675905525364368443937460749 253464572011638166476547781)
                ·
                  refine ⟨47524607252182156214352709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253464572011638166476547781 47524607252182156214352709)
                  ·
                    refine ⟨8910863859784154290191133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47524607252182156214352709 8910863859784154290191133)
                    ·
                      refine ⟨3341573947419057858821675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8910863859784154290191133 3341573947419057858821675)
                      ·
                        rfl

theorem cell23_6507692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_6507692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507692 prefixEnd_6507692 := by exact prefixLift 6507692
  have htrace : WordTrace (prefixWord ++ tailWord_6507692) baseStart_6507692 baseEnd_6507692 := by
    simpa [prefixWord, tailWord_6507692, baseEnd_6507692] using wordTrace_append hprefix tailTrace_6507692
  have hstable : (prefixWord ++ tailWord_6507692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507692).length < 2 ^ (prefixWord ++ tailWord_6507692).sum := by decide
  have hdescent : baseEnd_6507692 < baseStart_6507692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507693 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_6507693 : Nat := 118140960795 + 6507693 * 2 ^ 59
def prefixEnd_6507693 : Nat := 4983230072969 + 3 ^ 40 * 6507693 * 2
def baseEnd_6507693 : Nat := 3341574460899712354909171

theorem tailTrace_6507693 : CollatzResearch.WordTrace tailWord_6507693 prefixEnd_6507693 3341574460899712354909171 := by
  unfold tailWord_6507693
  simp only [CollatzResearch.WordTrace]
  refine ⟨237355063212747161324407733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158236708808498107549605155 237355063212747161324407733)
  ·
    refine ⟨22252037176195046374163225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237355063212747161324407733 22252037176195046374163225)
    ·
      refine ⟨16689027882146284780622419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22252037176195046374163225 16689027882146284780622419)
      ·
        refine ⟨25033541823219427170933629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16689027882146284780622419 25033541823219427170933629)
        ·
          refine ⟨9387578183707285189100111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25033541823219427170933629 9387578183707285189100111)
          ·
            refine ⟨14081367275560927783650167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387578183707285189100111 14081367275560927783650167)
            ·
              refine ⟨21122050913341391675475251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14081367275560927783650167 21122050913341391675475251)
              ·
                refine ⟨31683076370012087513212877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21122050913341391675475251 31683076370012087513212877)
                ·
                  refine ⟨11881153638754532817454829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31683076370012087513212877 11881153638754532817454829)
                  ·
                    refine ⟨4455432614532949806545561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11881153638754532817454829 4455432614532949806545561)
                    ·
                      refine ⟨3341574460899712354909171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455432614532949806545561 3341574460899712354909171)
                      ·
                        rfl

theorem cell23_6507693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_6507693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507693 prefixEnd_6507693 := by exact prefixLift 6507693
  have htrace : WordTrace (prefixWord ++ tailWord_6507693) baseStart_6507693 baseEnd_6507693 := by
    simpa [prefixWord, tailWord_6507693, baseEnd_6507693] using wordTrace_append hprefix tailTrace_6507693
  have hstable : (prefixWord ++ tailWord_6507693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507693).length < 2 ^ (prefixWord ++ tailWord_6507693).sum := by decide
  have hdescent : baseEnd_6507693 < baseStart_6507693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507710 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_6507710 : Nat := 118140960795 + 6507710 * 2 ^ 59
def prefixEnd_6507710 : Nat := 4983230072969 + 3 ^ 40 * 6507710 * 2
def baseEnd_6507710 : Nat := 3341583190070838788396593

theorem tailTrace_6507710 : CollatzResearch.WordTrace tailWord_6507710 prefixEnd_6507710 3341583190070838788396593 := by
  unfold tailWord_6507710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29669460406710696653472073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158237122169123715485184389 29669460406710696653472073)
  ·
    refine ⟨22252095305033022490104055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29669460406710696653472073 22252095305033022490104055)
    ·
      refine ⟨33378142957549533735156083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22252095305033022490104055 33378142957549533735156083)
      ·
        refine ⟨50067214436324300602734125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33378142957549533735156083 50067214436324300602734125)
        ·
          refine ⟨18775205413621612726025297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50067214436324300602734125 18775205413621612726025297)
          ·
            refine ⟨14081404060216209544518973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18775205413621612726025297 14081404060216209544518973)
            ·
              refine ⟨5280526522581078579194615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14081404060216209544518973 5280526522581078579194615)
              ·
                refine ⟨7920789783871617868791923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280526522581078579194615 7920789783871617868791923)
                ·
                  refine ⟨11881184675807426803187885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7920789783871617868791923 11881184675807426803187885)
                  ·
                    refine ⟨4455444253427785051195457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11881184675807426803187885 4455444253427785051195457)
                    ·
                      refine ⟨3341583190070838788396593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455444253427785051195457 3341583190070838788396593)
                      ·
                        rfl

theorem cell23_6507710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_6507710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507710 prefixEnd_6507710 := by exact prefixLift 6507710
  have htrace : WordTrace (prefixWord ++ tailWord_6507710) baseStart_6507710 baseEnd_6507710 := by
    simpa [prefixWord, tailWord_6507710, baseEnd_6507710] using wordTrace_append hprefix tailTrace_6507710
  have hstable : (prefixWord ++ tailWord_6507710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507710).length < 2 ^ (prefixWord ++ tailWord_6507710).sum := by decide
  have hdescent : baseEnd_6507710 < baseStart_6507710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507718 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6507718 : Nat := 118140960795 + 6507718 * 2 ^ 59
def prefixEnd_6507718 : Nat := 4983230072969 + 3 ^ 40 * 6507718 * 2
def baseEnd_6507718 : Nat := 3341587297916074757096557

theorem tailTrace_6507718 : CollatzResearch.WordTrace tailWord_6507718 prefixEnd_6507718 3341587297916074757096557 := by
  unfold tailWord_6507718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7417374219926768456064619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158237316691771060396045205 7417374219926768456064619)
  ·
    refine ⟨11126061329890152684096929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7417374219926768456064619 11126061329890152684096929)
    ·
      refine ⟨8344545997417614513072697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11126061329890152684096929 8344545997417614513072697)
      ·
        refine ⟨6258409498063210884804523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8344545997417614513072697 6258409498063210884804523)
        ·
          refine ⟨9387614247094816327206785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258409498063210884804523 9387614247094816327206785)
          ·
            refine ⟨7040710685321112245405089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9387614247094816327206785 7040710685321112245405089)
            ·
              refine ⟨5280533013990834184053817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040710685321112245405089 5280533013990834184053817)
              ·
                refine ⟨3960399760493125638040363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280533013990834184053817 3960399760493125638040363)
                ·
                  refine ⟨5940599640739688457060545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960399760493125638040363 5940599640739688457060545)
                  ·
                    refine ⟨4455449730554766342795409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5940599640739688457060545 4455449730554766342795409)
                    ·
                      refine ⟨3341587297916074757096557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455449730554766342795409 3341587297916074757096557)
                      ·
                        rfl

theorem cell23_6507718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6507718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507718 prefixEnd_6507718 := by exact prefixLift 6507718
  have htrace : WordTrace (prefixWord ++ tailWord_6507718) baseStart_6507718 baseEnd_6507718 := by
    simpa [prefixWord, tailWord_6507718, baseEnd_6507718] using wordTrace_append hprefix tailTrace_6507718
  have hstable : (prefixWord ++ tailWord_6507718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507718).length < 2 ^ (prefixWord ++ tailWord_6507718).sum := by decide
  have hdescent : baseEnd_6507718 < baseStart_6507718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507759 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 1, 7]
def baseStart_6507759 : Nat := 118140960795 + 6507759 * 2 ^ 59
def prefixEnd_6507759 : Nat := 4983230072969 + 3 ^ 40 * 6507759 * 2
def baseEnd_6507759 : Nat := 1113869450207636365561289

theorem tailTrace_6507759 : CollatzResearch.WordTrace tailWord_6507759 prefixEnd_6507759 1113869450207636365561289 := by
  unfold tailWord_6507759
  simp only [CollatzResearch.WordTrace]
  refine ⟨237357470430508054596310331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158238313620338703064206887 237357470430508054596310331)
  ·
    refine ⟨356036205645762081894465497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237357470430508054596310331 356036205645762081894465497)
    ·
      refine ⟨267027154234321561420849123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356036205645762081894465497 267027154234321561420849123)
      ·
        refine ⟨400540731351482342131273685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267027154234321561420849123 400540731351482342131273685)
        ·
          refine ⟨9387673391050367393701727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 400540731351482342131273685 9387673391050367393701727)
          ·
            refine ⟨14081510086575551090552591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387673391050367393701727 14081510086575551090552591)
            ·
              refine ⟨21122265129863326635828887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14081510086575551090552591 21122265129863326635828887)
              ·
                refine ⟨31683397694794989953743331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21122265129863326635828887 31683397694794989953743331)
                ·
                  refine ⟨47525096542192484930614997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31683397694794989953743331 47525096542192484930614997)
                  ·
                    refine ⟨1113869450207636365561289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47525096542192484930614997 1113869450207636365561289)
                    ·
                      rfl

theorem cell23_6507759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_6507759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507759 prefixEnd_6507759 := by exact prefixLift 6507759
  have htrace : WordTrace (prefixWord ++ tailWord_6507759) baseStart_6507759 baseEnd_6507759 := by
    simpa [prefixWord, tailWord_6507759, baseEnd_6507759] using wordTrace_append hprefix tailTrace_6507759
  have hstable : (prefixWord ++ tailWord_6507759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507759).length < 2 ^ (prefixWord ++ tailWord_6507759).sum := by decide
  have hdescent : baseEnd_6507759 < baseStart_6507759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507799 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_6507799 : Nat := 118140960795 + 6507799 * 2 ^ 59
def prefixEnd_6507799 : Nat := 4983230072969 + 3 ^ 40 * 6507799 * 2
def baseEnd_6507799 : Nat := 3341628889849088940183683

theorem tailTrace_6507799 : CollatzResearch.WordTrace tailWord_6507799 prefixEnd_6507799 3341628889849088940183683 := by
  unfold tailWord_6507799
  simp only [CollatzResearch.WordTrace]
  refine ⟨237358929350363141427766451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158239286233575427618510967 237358929350363141427766451)
  ·
    refine ⟨356038394025544712141649677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237358929350363141427766451 356038394025544712141649677)
    ·
      refine ⟨133514397759579267053118629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356038394025544712141649677 133514397759579267053118629)
      ·
        refine ⟨25033949579921112572459743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133514397759579267053118629 25033949579921112572459743)
        ·
          refine ⟨37550924369881668858689615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25033949579921112572459743 37550924369881668858689615)
          ·
            refine ⟨56326386554822503288034423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37550924369881668858689615 56326386554822503288034423)
            ·
              refine ⟨84489579832233754932051635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56326386554822503288034423 84489579832233754932051635)
              ·
                refine ⟨126734369748350632398077453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84489579832233754932051635 126734369748350632398077453)
                ·
                  refine ⟨47525388655631487149279045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126734369748350632398077453 47525388655631487149279045)
                  ·
                    refine ⟨8911010372930903840489821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47525388655631487149279045 8911010372930903840489821)
                    ·
                      refine ⟨3341628889849088940183683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911010372930903840489821 3341628889849088940183683)
                      ·
                        rfl

theorem cell23_6507799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_6507799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507799 prefixEnd_6507799 := by exact prefixLift 6507799
  have htrace : WordTrace (prefixWord ++ tailWord_6507799) baseStart_6507799 baseEnd_6507799 := by
    simpa [prefixWord, tailWord_6507799, baseEnd_6507799] using wordTrace_append hprefix tailTrace_6507799
  have hstable : (prefixWord ++ tailWord_6507799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507799).length < 2 ^ (prefixWord ++ tailWord_6507799).sum := by decide
  have hdescent : baseEnd_6507799 < baseStart_6507799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507816 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_6507816 : Nat := 118140960795 + 6507816 * 2 ^ 59
def prefixEnd_6507816 : Nat := 4983230072969 + 3 ^ 40 * 6507816 * 2
def baseEnd_6507816 : Nat := 3341637619020215373671105

theorem tailTrace_6507816 : CollatzResearch.WordTrace tailWord_6507816 prefixEnd_6507816 3341637619020215373671105 := by
  unfold tailWord_6507816
  simp only [CollatzResearch.WordTrace]
  refine ⟨118679774695650776665567651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158239699594201035554090201 118679774695650776665567651)
  ·
    refine ⟨178019662043476164998351477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118679774695650776665567651 178019662043476164998351477)
    ·
      refine ⟨16689343316575890468595451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178019662043476164998351477 16689343316575890468595451)
      ·
        refine ⟨25034014974863835702893177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16689343316575890468595451 25034014974863835702893177)
        ·
          refine ⟨18775511231147876777169883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25034014974863835702893177 18775511231147876777169883)
          ·
            refine ⟨28163266846721815165754825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18775511231147876777169883 28163266846721815165754825)
            ·
              refine ⟨21122450135041361374316119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28163266846721815165754825 21122450135041361374316119)
              ·
                refine ⟨31683675202562042061474179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21122450135041361374316119 31683675202562042061474179)
                ·
                  refine ⟨47525512803843063092211269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31683675202562042061474179 47525512803843063092211269)
                  ·
                    refine ⟨8911033650720574329789613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47525512803843063092211269 8911033650720574329789613)
                    ·
                      refine ⟨3341637619020215373671105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911033650720574329789613 3341637619020215373671105)
                      ·
                        rfl

theorem cell23_6507816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_6507816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507816 prefixEnd_6507816 := by exact prefixLift 6507816
  have htrace : WordTrace (prefixWord ++ tailWord_6507816) baseStart_6507816 baseEnd_6507816 := by
    simpa [prefixWord, tailWord_6507816, baseEnd_6507816] using wordTrace_append hprefix tailTrace_6507816
  have hstable : (prefixWord ++ tailWord_6507816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507816).length < 2 ^ (prefixWord ++ tailWord_6507816).sum := by decide
  have hdescent : baseEnd_6507816 < baseStart_6507816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507830 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6507830 : Nat := 118140960795 + 6507830 * 2 ^ 59
def prefixEnd_6507830 : Nat := 4983230072969 + 3 ^ 40 * 6507830 * 2
def baseEnd_6507830 : Nat := 3341644807749378318896041

theorem tailTrace_6507830 : CollatzResearch.WordTrace tailWord_6507830 prefixEnd_6507830 3341644807749378318896041 := by
  unfold tailWord_6507830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14835003750828177107634059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158240040008833889148096629 14835003750828177107634059)
  ·
    refine ⟨22252505626242265661451089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14835003750828177107634059 22252505626242265661451089)
    ·
      refine ⟨16689379219681699246088317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22252505626242265661451089 16689379219681699246088317)
      ·
        refine ⟨6258517207380637217283119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16689379219681699246088317 6258517207380637217283119)
        ·
          refine ⟨9387775811070955825924679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258517207380637217283119 9387775811070955825924679)
          ·
            refine ⟨14081663716606433738887019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387775811070955825924679 14081663716606433738887019)
            ·
              refine ⟨21122495574909650608330529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14081663716606433738887019 21122495574909650608330529)
              ·
                refine ⟨15841871681182237956247897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21122495574909650608330529 15841871681182237956247897)
                ·
                  refine ⟨11881403760886678467185923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15841871681182237956247897 11881403760886678467185923)
                  ·
                    refine ⟨17822105641330017700778885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11881403760886678467185923 17822105641330017700778885)
                    ·
                      refine ⟨3341644807749378318896041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17822105641330017700778885 3341644807749378318896041)
                      ·
                        rfl

theorem cell23_6507830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6507830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507830 prefixEnd_6507830 := by exact prefixLift 6507830
  have htrace : WordTrace (prefixWord ++ tailWord_6507830) baseStart_6507830 baseEnd_6507830 := by
    simpa [prefixWord, tailWord_6507830, baseEnd_6507830] using wordTrace_append hprefix tailTrace_6507830
  have hstable : (prefixWord ++ tailWord_6507830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507830).length < 2 ^ (prefixWord ++ tailWord_6507830).sum := by decide
  have hdescent : baseEnd_6507830 < baseStart_6507830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507833 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6507833 : Nat := 118140960795 + 6507833 * 2 ^ 59
def prefixEnd_6507833 : Nat := 4983230072969 + 3 ^ 40 * 6507833 * 2
def baseEnd_6507833 : Nat := 3341646348191341807158527

theorem tailTrace_6507833 : CollatzResearch.WordTrace tailWord_6507833 prefixEnd_6507833 3341646348191341807158527 := by
  unfold tailWord_6507833
  simp only [CollatzResearch.WordTrace]
  refine ⟨237360169432239965234504153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158240112954826643489669435 237360169432239965234504153)
  ·
    refine ⟨178020127074179973925878115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237360169432239965234504153 178020127074179973925878115)
    ·
      refine ⟨267030190611269960888817173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178020127074179973925878115 267030190611269960888817173)
      ·
        refine ⟨12517040184903279416663305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267030190611269960888817173 12517040184903279416663305)
        ·
          refine ⟨9387780138677459562497479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12517040184903279416663305 9387780138677459562497479)
          ·
            refine ⟨14081670208016189343746219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9387780138677459562497479 14081670208016189343746219)
            ·
              refine ⟨21122505312024284015619329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14081670208016189343746219 21122505312024284015619329)
              ·
                refine ⟨15841878984018213011714497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21122505312024284015619329 15841878984018213011714497)
                ·
                  refine ⟨11881409238013659758785873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15841878984018213011714497 11881409238013659758785873)
                  ·
                    refine ⟨8911056928510244819089405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11881409238013659758785873 8911056928510244819089405)
                    ·
                      refine ⟨3341646348191341807158527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911056928510244819089405 3341646348191341807158527)
                      ·
                        rfl

theorem cell23_6507833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6507833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507833 prefixEnd_6507833 := by exact prefixLift 6507833
  have htrace : WordTrace (prefixWord ++ tailWord_6507833) baseStart_6507833 baseEnd_6507833 := by
    simpa [prefixWord, tailWord_6507833, baseEnd_6507833] using wordTrace_append hprefix tailTrace_6507833
  have hstable : (prefixWord ++ tailWord_6507833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507833).length < 2 ^ (prefixWord ++ tailWord_6507833).sum := by decide
  have hdescent : baseEnd_6507833 < baseStart_6507833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507856 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 4, 3, 2]
def baseStart_6507856 : Nat := 118140960795 + 6507856 * 2 ^ 59
def prefixEnd_6507856 : Nat := 4983230072969 + 3 ^ 40 * 6507856 * 2
def baseEnd_6507856 : Nat := 3341658158246395217170921

theorem tailTrace_6507856 : CollatzResearch.WordTrace tailWord_6507856 prefixEnd_6507856 3341658158246395217170921 := by
  unfold tailWord_6507856
  simp only [CollatzResearch.WordTrace]
  refine ⟨118680504155578320081295711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158240672207437760108394281 118680504155578320081295711)
  ·
    refine ⟨178020756233367480121943567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118680504155578320081295711 178020756233367480121943567)
    ·
      refine ⟨267031134350051220182915351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178020756233367480121943567 267031134350051220182915351)
      ·
        refine ⟨400546701525076830274373027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267031134350051220182915351 400546701525076830274373027)
        ·
          refine ⟨600820052287615245411559541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400546701525076830274373027 600820052287615245411559541)
          ·
            refine ⟨56326879901963929257333707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 600820052287615245411559541 56326879901963929257333707)
            ·
              refine ⟨84490319852945893886000561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56326879901963929257333707 84490319852945893886000561)
              ·
                refine ⟨63367739889709420414500421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84490319852945893886000561 63367739889709420414500421)
                ·
                  refine ⟨11881451229320516327718829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63367739889709420414500421 11881451229320516327718829)
                  ·
                    refine ⟨4455544210995193622894561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11881451229320516327718829 4455544210995193622894561)
                    ·
                      refine ⟨3341658158246395217170921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455544210995193622894561 3341658158246395217170921)
                      ·
                        rfl

theorem cell23_6507856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 3, 2].length) (baseStart_6507856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507856 prefixEnd_6507856 := by exact prefixLift 6507856
  have htrace : WordTrace (prefixWord ++ tailWord_6507856) baseStart_6507856 baseEnd_6507856 := by
    simpa [prefixWord, tailWord_6507856, baseEnd_6507856] using wordTrace_append hprefix tailTrace_6507856
  have hstable : (prefixWord ++ tailWord_6507856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507856).length < 2 ^ (prefixWord ++ tailWord_6507856).sum := by decide
  have hdescent : baseEnd_6507856 < baseStart_6507856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507866 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_6507866 : Nat := 118140960795 + 6507866 * 2 ^ 59
def prefixEnd_6507866 : Nat := 4983230072969 + 3 ^ 40 * 6507866 * 2
def baseEnd_6507866 : Nat := 1113887764350980059348625

theorem tailTrace_6507866 : CollatzResearch.WordTrace tailWord_6507866 prefixEnd_6507866 1113887764350980059348625 := by
  unfold tailWord_6507866
  simp only [CollatzResearch.WordTrace]
  refine ⟨59340343260280102967613863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158240915360746941246970301 59340343260280102967613863)
  ·
    refine ⟨89010514890420154451420795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59340343260280102967613863 89010514890420154451420795)
    ·
      refine ⟨133515772335630231677131193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89010514890420154451420795 133515772335630231677131193)
      ·
        refine ⟨100136829251722673757848395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133515772335630231677131193 100136829251722673757848395)
        ·
          refine ⟨150205243877584010636772593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100136829251722673757848395 150205243877584010636772593)
          ·
            refine ⟨112653932908188007977579445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150205243877584010636772593 112653932908188007977579445)
            ·
              refine ⟨10561306210142625747898073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112653932908188007977579445 10561306210142625747898073)
              ·
                refine ⟨7920979657606969310923555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10561306210142625747898073 7920979657606969310923555)
                ·
                  refine ⟨11881469486410453966385333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7920979657606969310923555 11881469486410453966385333)
                  ·
                    refine ⟨1113887764350980059348625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11881469486410453966385333 1113887764350980059348625)
                    ·
                      rfl

theorem cell23_6507866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_6507866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507866 prefixEnd_6507866 := by exact prefixLift 6507866
  have htrace : WordTrace (prefixWord ++ tailWord_6507866) baseStart_6507866 baseEnd_6507866 := by
    simpa [prefixWord, tailWord_6507866, baseEnd_6507866] using wordTrace_append hprefix tailTrace_6507866
  have hstable : (prefixWord ++ tailWord_6507866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507866).length < 2 ^ (prefixWord ++ tailWord_6507866).sum := by decide
  have hdescent : baseEnd_6507866 < baseStart_6507866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507899 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4]
def baseStart_6507899 : Nat := 118140960795 + 6507899 * 2 ^ 59
def prefixEnd_6507899 : Nat := 4983230072969 + 3 ^ 40 * 6507899 * 2
def baseEnd_6507899 : Nat := 3341680237914538548933223

theorem tailTrace_6507899 : CollatzResearch.WordTrace tailWord_6507899 prefixEnd_6507899 3341680237914538548933223 := by
  unfold tailWord_6507899
  simp only [CollatzResearch.WordTrace]
  refine ⟨237362576650000858506406751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158241717766667239004271167 237362576650000858506406751)
  ·
    refine ⟨356043864975001287759610127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237362576650000858506406751 356043864975001287759610127)
    ·
      refine ⟨534065797462501931639415191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356043864975001287759610127 534065797462501931639415191)
      ·
        refine ⟨801098696193752897459122787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534065797462501931639415191 801098696193752897459122787)
        ·
          refine ⟨1201648044290629346188684181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801098696193752897459122787 1201648044290629346188684181)
          ·
            refine ⟨56327252076123250602594571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1201648044290629346188684181 56327252076123250602594571)
            ·
              refine ⟨84490878114184875903891857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56327252076123250602594571 84490878114184875903891857)
              ·
                refine ⟨63368158585638656927918893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84490878114184875903891857 63368158585638656927918893)
                ·
                  refine ⟨23763059469614496347969585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63368158585638656927918893 23763059469614496347969585)
                  ·
                    refine ⟨17822294602210872260977189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23763059469614496347969585 17822294602210872260977189)
                    ·
                      refine ⟨3341680237914538548933223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17822294602210872260977189 3341680237914538548933223)
                      ·
                        rfl

theorem cell23_6507899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_6507899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507899 prefixEnd_6507899 := by exact prefixLift 6507899
  have htrace : WordTrace (prefixWord ++ tailWord_6507899) baseStart_6507899 baseEnd_6507899 := by
    simpa [prefixWord, tailWord_6507899, baseEnd_6507899] using wordTrace_append hprefix tailTrace_6507899
  have hstable : (prefixWord ++ tailWord_6507899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507899).length < 2 ^ (prefixWord ++ tailWord_6507899).sum := by decide
  have hdescent : baseEnd_6507899 < baseStart_6507899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507909 : List Nat := [1, 3, 1, 1, 3, 1, 5, 8]
def baseStart_6507909 : Nat := 118140960795 + 6507909 * 2 ^ 59
def prefixEnd_6507909 : Nat := 4983230072969 + 3 ^ 40 * 6507909 * 2
def baseEnd_6507909 : Nat := 123766124915595685548451

theorem tailTrace_6507909 : CollatzResearch.WordTrace tailWord_6507909 prefixEnd_6507909 123766124915595685548451 := by
  unfold tailWord_6507909
  simp only [CollatzResearch.WordTrace]
  refine ⟨237362941379964630214270781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158241960919976420142847187 237362941379964630214270781)
  ·
    refine ⟨89011103017486736330351543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237362941379964630214270781 89011103017486736330351543)
    ·
      refine ⟨133516654526230104495527315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89011103017486736330351543 133516654526230104495527315)
      ·
        refine ⟨200274981789345156743290973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133516654526230104495527315 200274981789345156743290973)
        ·
          refine ⟨75103118171004433778734115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200274981789345156743290973 75103118171004433778734115)
          ·
            refine ⟨112654677256506650668101173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75103118171004433778734115 112654677256506650668101173)
            ·
              refine ⟨10561375992797498500134485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112654677256506650668101173 10561375992797498500134485)
              ·
                refine ⟨123766124915595685548451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10561375992797498500134485 123766124915595685548451)
                ·
                  rfl

theorem cell23_6507909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 8].length) (baseStart_6507909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507909 prefixEnd_6507909 := by exact prefixLift 6507909
  have htrace : WordTrace (prefixWord ++ tailWord_6507909) baseStart_6507909 baseEnd_6507909 := by
    simpa [prefixWord, tailWord_6507909, baseEnd_6507909] using wordTrace_append hprefix tailTrace_6507909
  have hstable : (prefixWord ++ tailWord_6507909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507909).length < 2 ^ (prefixWord ++ tailWord_6507909).sum := by decide
  have hdescent : baseEnd_6507909 < baseStart_6507909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507916 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_6507916 : Nat := 118140960795 + 6507916 * 2 ^ 59
def prefixEnd_6507916 : Nat := 4983230072969 + 3 ^ 40 * 6507916 * 2
def baseEnd_6507916 : Nat := 3341688967085664982420645

theorem tailTrace_6507916 : CollatzResearch.WordTrace tailWord_6507916 prefixEnd_6507916 3341688967085664982420645 := by
  unfold tailWord_6507916
  simp only [CollatzResearch.WordTrace]
  refine ⟨118681598345469635204887801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158242131127292846939850401 118681598345469635204887801)
  ·
    refine ⟨89011198759102226403665851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118681598345469635204887801 89011198759102226403665851)
    ·
      refine ⟨133516798138653339605498777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89011198759102226403665851 133516798138653339605498777)
      ·
        refine ⟨100137598603990004704124083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133516798138653339605498777 100137598603990004704124083)
        ·
          refine ⟨150206397905985007056186125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100137598603990004704124083 150206397905985007056186125)
          ·
            refine ⟨56327399214744377646069797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150206397905985007056186125 56327399214744377646069797)
            ·
              refine ⟨10561387352764570808638087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56327399214744377646069797 10561387352764570808638087)
              ·
                refine ⟨15842081029146856212957131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10561387352764570808638087 15842081029146856212957131)
                ·
                  refine ⟨23763121543720284319435697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15842081029146856212957131 23763121543720284319435697)
                  ·
                    refine ⟨17822341157790213239576773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23763121543720284319435697 17822341157790213239576773)
                    ·
                      refine ⟨3341688967085664982420645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17822341157790213239576773 3341688967085664982420645)
                      ·
                        rfl

theorem cell23_6507916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_6507916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507916 prefixEnd_6507916 := by exact prefixLift 6507916
  have htrace : WordTrace (prefixWord ++ tailWord_6507916) baseStart_6507916 baseEnd_6507916 := by
    simpa [prefixWord, tailWord_6507916, baseEnd_6507916] using wordTrace_append hprefix tailTrace_6507916
  have hstable : (prefixWord ++ tailWord_6507916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507916).length < 2 ^ (prefixWord ++ tailWord_6507916).sum := by decide
  have hdescent : baseEnd_6507916 < baseStart_6507916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507934 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6507934 : Nat := 118140960795 + 6507934 * 2 ^ 59
def prefixEnd_6507934 : Nat := 4983230072969 + 3 ^ 40 * 6507934 * 2
def baseEnd_6507934 : Nat := 1113899403245815303998521

theorem tailTrace_6507934 : CollatzResearch.WordTrace tailWord_6507934 prefixEnd_6507934 1113899403245815303998521 := by
  unfold tailWord_6507934
  simp only [CollatzResearch.WordTrace]
  refine ⟨29670481650609257435491357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158242568803249372989287237 29670481650609257435491357)
  ·
    refine ⟨11126430618978471538309259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29670481650609257435491357 11126430618978471538309259)
    ·
      refine ⟨16689645928467707307463889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11126430618978471538309259 16689645928467707307463889)
      ·
        refine ⟨12517234446350780480597917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16689645928467707307463889 12517234446350780480597917)
        ·
          refine ⟨4693962917381542680224219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12517234446350780480597917 4693962917381542680224219)
          ·
            refine ⟨7040944376072314020336329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693962917381542680224219 7040944376072314020336329)
            ·
              refine ⟨5280708282054235515252247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040944376072314020336329 5280708282054235515252247)
              ·
                refine ⟨7921062423081353272878371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280708282054235515252247 7921062423081353272878371)
                ·
                  refine ⟨11881593634622029909317557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921062423081353272878371 11881593634622029909317557)
                  ·
                    refine ⟨1113899403245815303998521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11881593634622029909317557 1113899403245815303998521)
                    ·
                      rfl

theorem cell23_6507934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6507934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507934 prefixEnd_6507934 := by exact prefixLift 6507934
  have htrace : WordTrace (prefixWord ++ tailWord_6507934) baseStart_6507934 baseEnd_6507934 := by
    simpa [prefixWord, tailWord_6507934, baseEnd_6507934] using wordTrace_append hprefix tailTrace_6507934
  have hstable : (prefixWord ++ tailWord_6507934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507934).length < 2 ^ (prefixWord ++ tailWord_6507934).sum := by decide
  have hdescent : baseEnd_6507934 < baseStart_6507934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507936 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_6507936 : Nat := 118140960795 + 6507936 * 2 ^ 59
def prefixEnd_6507936 : Nat := 4983230072969 + 3 ^ 40 * 6507936 * 2
def baseEnd_6507936 : Nat := 3341699236698754904170553

theorem tailTrace_6507936 : CollatzResearch.WordTrace tailWord_6507936 prefixEnd_6507936 3341699236698754904170553 := by
  unfold tailWord_6507936
  simp only [CollatzResearch.WordTrace]
  refine ⟨118681963075433406912751831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158242617433911209217002441 118681963075433406912751831)
  ·
    refine ⟨178022944613150110369127747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118681963075433406912751831 178022944613150110369127747)
    ·
      refine ⟨267034416919725165553691621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178022944613150110369127747 267034416919725165553691621)
      ·
        refine ⟨50068953172448468541317179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267034416919725165553691621 50068953172448468541317179)
        ·
          refine ⟨75103429758672702811975769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50068953172448468541317179 75103429758672702811975769)
          ·
            refine ⟨56327572319004527108981827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75103429758672702811975769 56327572319004527108981827)
            ·
              refine ⟨84491358478506790663472741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56327572319004527108981827 84491358478506790663472741)
              ·
                refine ⟨15842129714720023249401139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84491358478506790663472741 15842129714720023249401139)
                ·
                  refine ⟨23763194572080034874101709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15842129714720023249401139 23763194572080034874101709)
                  ·
                    refine ⟨8911197964530013077788141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23763194572080034874101709 8911197964530013077788141)
                    ·
                      refine ⟨3341699236698754904170553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911197964530013077788141 3341699236698754904170553)
                      ·
                        rfl

theorem cell23_6507936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_6507936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507936 prefixEnd_6507936 := by exact prefixLift 6507936
  have htrace : WordTrace (prefixWord ++ tailWord_6507936) baseStart_6507936 baseEnd_6507936 := by
    simpa [prefixWord, tailWord_6507936, baseEnd_6507936] using wordTrace_append hprefix tailTrace_6507936
  have hstable : (prefixWord ++ tailWord_6507936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507936).length < 2 ^ (prefixWord ++ tailWord_6507936).sum := by decide
  have hdescent : baseEnd_6507936 < baseStart_6507936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507953 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_6507953 : Nat := 118140960795 + 6507953 * 2 ^ 59
def prefixEnd_6507953 : Nat := 4983230072969 + 3 ^ 40 * 6507953 * 2
def baseEnd_6507953 : Nat := 3341707965869881337657975

theorem tailTrace_6507953 : CollatzResearch.WordTrace tailWord_6507953 prefixEnd_6507953 3341707965869881337657975 := by
  unfold tailWord_6507953
  simp only [CollatzResearch.WordTrace]
  refine ⟨237364546191805225728872513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158243030794536817152581675 237364546191805225728872513)
  ·
    refine ⟨178023409643853919296654385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237364546191805225728872513 178023409643853919296654385)
    ·
      refine ⟨133517557232890439472490789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178023409643853919296654385 133517557232890439472490789)
      ·
        refine ⟨25034541981166957401092023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133517557232890439472490789 25034541981166957401092023)
        ·
          refine ⟨37551812971750436101638035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25034541981166957401092023 37551812971750436101638035)
          ·
            refine ⟨56327719457625654152457053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37551812971750436101638035 56327719457625654152457053)
            ·
              refine ⟨21122894796609620307171395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56327719457625654152457053 21122894796609620307171395)
              ·
                refine ⟨31684342194914430460757093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21122894796609620307171395 31684342194914430460757093)
                ·
                  refine ⟨5940814161546455711391955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31684342194914430460757093 5940814161546455711391955)
                  ·
                    refine ⟨8911221242319683567087933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5940814161546455711391955 8911221242319683567087933)
                    ·
                      refine ⟨3341707965869881337657975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911221242319683567087933 3341707965869881337657975)
                      ·
                        rfl

theorem cell23_6507953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_6507953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507953 prefixEnd_6507953 := by exact prefixLift 6507953
  have htrace : WordTrace (prefixWord ++ tailWord_6507953) baseStart_6507953 baseEnd_6507953 := by
    simpa [prefixWord, tailWord_6507953, baseEnd_6507953] using wordTrace_append hprefix tailTrace_6507953
  have hstable : (prefixWord ++ tailWord_6507953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507953).length < 2 ^ (prefixWord ++ tailWord_6507953).sum := by decide
  have hdescent : baseEnd_6507953 < baseStart_6507953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6507980 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6507980 : Nat := 118140960795 + 6507980 * 2 ^ 59
def prefixEnd_6507980 : Nat := 4983230072969 + 3 ^ 40 * 6507980 * 2
def baseEnd_6507980 : Nat := 3341721829847552732020351

theorem tailTrace_6507980 : CollatzResearch.WordTrace tailWord_6507980 prefixEnd_6507980 3341721829847552732020351 := by
  unfold tailWord_6507980
  simp only [CollatzResearch.WordTrace]
  refine ⟨118682765481353704670052697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158243687308471606226736929 118682765481353704670052697)
  ·
    refine ⟨89012074111015278502539523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118682765481353704670052697 89012074111015278502539523)
    ·
      refine ⟨133518111166522917753809285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89012074111015278502539523 133518111166522917753809285)
      ·
        refine ⟨25034645843723047078839241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133518111166522917753809285 25034645843723047078839241)
        ·
          refine ⟨18775984382792285309129431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25034645843723047078839241 18775984382792285309129431)
          ·
            refine ⟨28163976574188427963694147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18775984382792285309129431 28163976574188427963694147)
            ·
              refine ⟨42245964861282641945541221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28163976574188427963694147 42245964861282641945541221)
              ·
                refine ⟨7921118411490495364788979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42245964861282641945541221 7921118411490495364788979)
                ·
                  refine ⟨11881677617235743047183469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921118411490495364788979 11881677617235743047183469)
                  ·
                    refine ⟨4455629106463403642693801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11881677617235743047183469 4455629106463403642693801)
                    ·
                      refine ⟨3341721829847552732020351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455629106463403642693801 3341721829847552732020351)
                      ·
                        rfl

theorem cell23_6507980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6507980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6507980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6507980 prefixEnd_6507980 := by exact prefixLift 6507980
  have htrace : WordTrace (prefixWord ++ tailWord_6507980) baseStart_6507980 baseEnd_6507980 := by
    simpa [prefixWord, tailWord_6507980, baseEnd_6507980] using wordTrace_append hprefix tailTrace_6507980
  have hstable : (prefixWord ++ tailWord_6507980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6507980).length < 2 ^ (prefixWord ++ tailWord_6507980).sum := by decide
  have hdescent : baseEnd_6507980 < baseStart_6507980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6507980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508016 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 7]
def baseStart_6508016 : Nat := 118140960795 + 6508016 * 2 ^ 59
def prefixEnd_6508016 : Nat := 4983230072969 + 3 ^ 40 * 6508016 * 2
def baseEnd_6508016 : Nat := 371304479461234954574465

theorem tailTrace_6508016 : CollatzResearch.WordTrace tailWord_6508016 prefixEnd_6508016 371304479461234954574465 := by
  unfold tailWord_6508016
  simp only [CollatzResearch.WordTrace]
  refine ⟨118683421995288493744207951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158244562660384658325610601 118683421995288493744207951)
  ·
    refine ⟨178025132992932740616311927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118683421995288493744207951 178025132992932740616311927)
    ·
      refine ⟨267037699489399110924467891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178025132992932740616311927 267037699489399110924467891)
      ·
        refine ⟨400556549234098666386701837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267037699489399110924467891 400556549234098666386701837)
        ·
          refine ⟨150208705962786999895013189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400556549234098666386701837 150208705962786999895013189)
          ·
            refine ⟨28164132368022562480314973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150208705962786999895013189 28164132368022562480314973)
            ·
              refine ⟨10561549638008460930118115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28164132368022562480314973 10561549638008460930118115)
              ·
                refine ⟨15842324457012691395177173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10561549638008460930118115 15842324457012691395177173)
                ·
                  refine ⟨371304479461234954574465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15842324457012691395177173 371304479461234954574465)
                  ·
                    rfl

theorem cell23_6508016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_6508016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508016 prefixEnd_6508016 := by exact prefixLift 6508016
  have htrace : WordTrace (prefixWord ++ tailWord_6508016) baseStart_6508016 baseEnd_6508016 := by
    simpa [prefixWord, tailWord_6508016, baseEnd_6508016] using wordTrace_append hprefix tailTrace_6508016
  have hstable : (prefixWord ++ tailWord_6508016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508016).length < 2 ^ (prefixWord ++ tailWord_6508016).sum := by decide
  have hdescent : baseEnd_6508016 < baseStart_6508016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508019 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_6508019 : Nat := 118140960795 + 6508019 * 2 ^ 59
def prefixEnd_6508019 : Nat := 4983230072969 + 3 ^ 40 * 6508019 * 2
def baseEnd_6508019 : Nat := 3341741855593078079432671

theorem tailTrace_6508019 : CollatzResearch.WordTrace tailWord_6508019 prefixEnd_6508019 3341741855593078079432671 := by
  unfold tailWord_6508019
  simp only [CollatzResearch.WordTrace]
  refine ⟨237366953409566119000775111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158244635606377412667183407 237366953409566119000775111)
  ·
    refine ⟨356050430114349178501162667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237366953409566119000775111 356050430114349178501162667)
    ·
      refine ⟨534075645171523767751744001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356050430114349178501162667 534075645171523767751744001)
      ·
        refine ⟨400556733878642825813808001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534075645171523767751744001 400556733878642825813808001)
        ·
          refine ⟨300417550408982119360356001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400556733878642825813808001 300417550408982119360356001)
          ·
            refine ⟨225313162806736589520267001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300417550408982119360356001 225313162806736589520267001)
            ·
              refine ⟨168984872105052442140200251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225313162806736589520267001 168984872105052442140200251)
              ·
                refine ⟨253477308157578663210300377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168984872105052442140200251 253477308157578663210300377)
                ·
                  refine ⟨190107981118183997407725283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253477308157578663210300377 190107981118183997407725283)
                  ·
                    refine ⟨285161971677275996111587925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190107981118183997407725283 285161971677275996111587925)
                    ·
                      refine ⟨3341741855593078079432671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 285161971677275996111587925 3341741855593078079432671)
                      ·
                        rfl

theorem cell23_6508019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_6508019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508019 prefixEnd_6508019 := by exact prefixLift 6508019
  have htrace : WordTrace (prefixWord ++ tailWord_6508019) baseStart_6508019 baseEnd_6508019 := by
    simpa [prefixWord, tailWord_6508019, baseEnd_6508019] using wordTrace_append hprefix tailTrace_6508019
  have hstable : (prefixWord ++ tailWord_6508019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508019).length < 2 ^ (prefixWord ++ tailWord_6508019).sum := by decide
  have hdescent : baseEnd_6508019 < baseStart_6508019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508026 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_6508026 : Nat := 118140960795 + 6508026 * 2 ^ 59
def prefixEnd_6508026 : Nat := 4983230072969 + 3 ^ 40 * 6508026 * 2
def baseEnd_6508026 : Nat := 3341745449957659552045139

theorem tailTrace_6508026 : CollatzResearch.WordTrace tailWord_6508026 prefixEnd_6508026 3341745449957659552045139 := by
  unfold tailWord_6508026
  simp only [CollatzResearch.WordTrace]
  refine ⟨59341802180135189799069983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158244805813693839464186621 59341802180135189799069983)
  ·
    refine ⟨89012703270202784698604975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59341802180135189799069983 89012703270202784698604975)
    ·
      refine ⟨133519054905304177047907463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89012703270202784698604975 133519054905304177047907463)
      ·
        refine ⟨200278582357956265571861195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133519054905304177047907463 200278582357956265571861195)
        ·
          refine ⟨300417873536934398357791793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200278582357956265571861195 300417873536934398357791793)
          ·
            refine ⟨225313405152700798768343845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300417873536934398357791793 225313405152700798768343845)
            ·
              refine ⟨42246263466131399769064471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225313405152700798768343845 42246263466131399769064471)
              ·
                refine ⟨63369395199197099653596707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42246263466131399769064471 63369395199197099653596707)
                ·
                  refine ⟨95054092798795649480395061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63369395199197099653596707 95054092798795649480395061)
                  ·
                    refine ⟨8911321199887092138787037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95054092798795649480395061 8911321199887092138787037)
                    ·
                      refine ⟨3341745449957659552045139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911321199887092138787037 3341745449957659552045139)
                      ·
                        rfl

theorem cell23_6508026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_6508026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508026 prefixEnd_6508026 := by exact prefixLift 6508026
  have htrace : WordTrace (prefixWord ++ tailWord_6508026) baseStart_6508026 baseEnd_6508026 := by
    simpa [prefixWord, tailWord_6508026, baseEnd_6508026] using wordTrace_append hprefix tailTrace_6508026
  have hstable : (prefixWord ++ tailWord_6508026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508026).length < 2 ^ (prefixWord ++ tailWord_6508026).sum := by decide
  have hdescent : baseEnd_6508026 < baseStart_6508026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508067 : List Nat := [1, 1, 1, 4, 5, 2, 2, 2, 5]
def baseStart_6508067 : Nat := 118140960795 + 6508067 * 2 ^ 59
def prefixEnd_6508067 : Nat := 4983230072969 + 3 ^ 40 * 6508067 * 2
def baseEnd_6508067 : Nat := 371307389184943765736939

theorem tailTrace_6508067 : CollatzResearch.WordTrace tailWord_6508067 prefixEnd_6508067 371307389184943765736939 := by
  unfold tailWord_6508067
  simp only [CollatzResearch.WordTrace]
  refine ⟨237368704113392223198522455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158245802742261482132348303 237368704113392223198522455)
  ·
    refine ⟨356053056170088334797783683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237368704113392223198522455 356053056170088334797783683)
    ·
      refine ⟨534079584255132502196675525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356053056170088334797783683 534079584255132502196675525)
      ·
        refine ⟨100139922047837344161876661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534079584255132502196675525 100139922047837344161876661)
        ·
          refine ⟨9388117691984751015175937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100139922047837344161876661 9388117691984751015175937)
          ·
            refine ⟨7041088268988563261381953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9388117691984751015175937 7041088268988563261381953)
            ·
              refine ⟨5280816201741422446036465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7041088268988563261381953 5280816201741422446036465)
              ·
                refine ⟨3960612151306066834527349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280816201741422446036465 3960612151306066834527349)
                ·
                  refine ⟨371307389184943765736939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960612151306066834527349 371307389184943765736939)
                  ·
                    rfl

theorem cell23_6508067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 5].length) (baseStart_6508067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508067 prefixEnd_6508067 := by exact prefixLift 6508067
  have htrace : WordTrace (prefixWord ++ tailWord_6508067) baseStart_6508067 baseEnd_6508067 := by
    simpa [prefixWord, tailWord_6508067, baseEnd_6508067] using wordTrace_append hprefix tailTrace_6508067
  have hstable : (prefixWord ++ tailWord_6508067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508067).length < 2 ^ (prefixWord ++ tailWord_6508067).sum := by decide
  have hdescent : baseEnd_6508067 < baseStart_6508067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508083 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 6, 2]
def baseStart_6508083 : Nat := 118140960795 + 6508083 * 2 ^ 59
def prefixEnd_6508083 : Nat := 4983230072969 + 3 ^ 40 * 6508083 * 2
def baseEnd_6508083 : Nat := 3341774718354965829032377

theorem tailTrace_6508083 : CollatzResearch.WordTrace tailWord_6508083 prefixEnd_6508083 3341774718354965829032377 := by
  unfold tailWord_6508083
  simp only [CollatzResearch.WordTrace]
  refine ⟨237369287681334257931104903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158246191787556171954069935 237369287681334257931104903)
  ·
    refine ⟨356053931522001386896657355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237369287681334257931104903 356053931522001386896657355)
    ·
      refine ⟨534080897283002080344986033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356053931522001386896657355 534080897283002080344986033)
      ·
        refine ⟨400560672962251560258739525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534080897283002080344986033 400560672962251560258739525)
        ·
          refine ⟨75105126180422167548513661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400560672962251560258739525 75105126180422167548513661)
          ·
            refine ⟨28164422317658312830692623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75105126180422167548513661 28164422317658312830692623)
            ·
              refine ⟨42246633476487469246038935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28164422317658312830692623 42246633476487469246038935)
              ·
                refine ⟨63369950214731203869058403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42246633476487469246038935 63369950214731203869058403)
                ·
                  refine ⟨95054925322096805803587605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63369950214731203869058403 95054925322096805803587605)
                  ·
                    refine ⟨4455699624473287772043169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95054925322096805803587605 4455699624473287772043169)
                    ·
                      refine ⟨3341774718354965829032377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455699624473287772043169 3341774718354965829032377)
                      ·
                        rfl

theorem cell23_6508083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6, 2].length) (baseStart_6508083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508083 prefixEnd_6508083 := by exact prefixLift 6508083
  have htrace : WordTrace (prefixWord ++ tailWord_6508083) baseStart_6508083 baseEnd_6508083 := by
    simpa [prefixWord, tailWord_6508083, baseEnd_6508083] using wordTrace_append hprefix tailTrace_6508083
  have hstable : (prefixWord ++ tailWord_6508083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508083).length < 2 ^ (prefixWord ++ tailWord_6508083).sum := by decide
  have hdescent : baseEnd_6508083 < baseStart_6508083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508106 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_6508106 : Nat := 118140960795 + 6508106 * 2 ^ 59
def prefixEnd_6508106 : Nat := 4983230072969 + 3 ^ 40 * 6508106 * 2
def baseEnd_6508106 : Nat := 371309614267779915449419

theorem tailTrace_6508106 : CollatzResearch.WordTrace tailWord_6508106 prefixEnd_6508106 371309614267779915449419 := by
  unfold tailWord_6508106
  simp only [CollatzResearch.WordTrace]
  refine ⟨59342531640062733214798043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158246751040167288572794781 59342531640062733214798043)
  ·
    refine ⟨89013797460094099822197065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59342531640062733214798043 89013797460094099822197065)
    ·
      refine ⟨66760348095070574866647799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89013797460094099822197065 66760348095070574866647799)
      ·
        refine ⟨100140522142605862299971699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66760348095070574866647799 100140522142605862299971699)
        ·
          refine ⟨150210783213908793449957549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100140522142605862299971699 150210783213908793449957549)
          ·
            refine ⟨56329043705215797543734081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150210783213908793449957549 56329043705215797543734081)
            ·
              refine ⟨42246782778911848157800561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56329043705215797543734081 42246782778911848157800561)
              ·
                refine ⟨31685087084183886118350421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42246782778911848157800561 31685087084183886118350421)
                ·
                  refine ⟨371309614267779915449419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31685087084183886118350421 371309614267779915449419)
                  ·
                    rfl

theorem cell23_6508106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_6508106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508106 prefixEnd_6508106 := by exact prefixLift 6508106
  have htrace : WordTrace (prefixWord ++ tailWord_6508106) baseStart_6508106 baseEnd_6508106 := by
    simpa [prefixWord, tailWord_6508106, baseEnd_6508106] using wordTrace_append hprefix tailTrace_6508106
  have hstable : (prefixWord ++ tailWord_6508106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508106).length < 2 ^ (prefixWord ++ tailWord_6508106).sum := by decide
  have hdescent : baseEnd_6508106 < baseStart_6508106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508160 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 2, 3, 2]
def baseStart_6508160 : Nat := 118140960795 + 6508160 * 2 ^ 59
def prefixEnd_6508160 : Nat := 4983230072969 + 3 ^ 40 * 6508160 * 2
def baseEnd_6508160 : Nat := 3341814256365362027769523

theorem tailTrace_6508160 : CollatzResearch.WordTrace tailWord_6508160 prefixEnd_6508160 3341814256365362027769523 := by
  unfold tailWord_6508160
  simp only [CollatzResearch.WordTrace]
  refine ⟨118686048051027650040828967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158248064068036866721105289 118686048051027650040828967)
  ·
    refine ⟨178029072076541475061243451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118686048051027650040828967 178029072076541475061243451)
    ·
      refine ⟨267043608114812212591865177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178029072076541475061243451 267043608114812212591865177)
      ·
        refine ⟨200282706086109159443898883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267043608114812212591865177 200282706086109159443898883)
        ·
          refine ⟨300424059129163739165848325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200282706086109159443898883 300424059129163739165848325)
          ·
            refine ⟨56329511086718201093596561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300424059129163739165848325 56329511086718201093596561)
            ·
              refine ⟨42247133315038650820197421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56329511086718201093596561 42247133315038650820197421)
              ·
                refine ⟨15842674993139494057574033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42247133315038650820197421 15842674993139494057574033)
                ·
                  refine ⟨11882006244854620543180525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15842674993139494057574033 11882006244854620543180525)
                  ·
                    refine ⟨4455752341820482703692697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11882006244854620543180525 4455752341820482703692697)
                    ·
                      refine ⟨3341814256365362027769523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455752341820482703692697 3341814256365362027769523)
                      ·
                        rfl

theorem cell23_6508160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_6508160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508160 prefixEnd_6508160 := by exact prefixLift 6508160
  have htrace : WordTrace (prefixWord ++ tailWord_6508160) baseStart_6508160 baseEnd_6508160 := by
    simpa [prefixWord, tailWord_6508160, baseEnd_6508160] using wordTrace_append hprefix tailTrace_6508160
  have hstable : (prefixWord ++ tailWord_6508160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508160).length < 2 ^ (prefixWord ++ tailWord_6508160).sum := by decide
  have hdescent : baseEnd_6508160 < baseStart_6508160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508170 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_6508170 : Nat := 118140960795 + 6508170 * 2 ^ 59
def prefixEnd_6508170 : Nat := 4983230072969 + 3 ^ 40 * 6508170 * 2
def baseEnd_6508170 : Nat := 1113939797057302329548159

theorem tailTrace_6508170 : CollatzResearch.WordTrace tailWord_6508170 prefixEnd_6508170 1113939797057302329548159 := by
  unfold tailWord_6508170
  simp only [CollatzResearch.WordTrace]
  refine ⟨59343115208004767947380491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158248307221346047859681309 59343115208004767947380491)
  ·
    refine ⟨89014672812007151921070737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59343115208004767947380491 89014672812007151921070737)
    ·
      refine ⟨66761004609005363940803053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89014672812007151921070737 66761004609005363940803053)
      ·
        refine ⟨25035376728377011477801145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66761004609005363940803053 25035376728377011477801145)
        ·
          refine ⟨18776532546282758608350859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25035376728377011477801145 18776532546282758608350859)
          ·
            refine ⟨28164798819424137912526289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18776532546282758608350859 28164798819424137912526289)
            ·
              refine ⟨21123599114568103434394717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28164798819424137912526289 21123599114568103434394717)
              ·
                refine ⟨7921349667963038787898019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21123599114568103434394717 7921349667963038787898019)
                ·
                  refine ⟨11882024501944558181847029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921349667963038787898019 11882024501944558181847029)
                  ·
                    refine ⟨1113939797057302329548159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11882024501944558181847029 1113939797057302329548159)
                    ·
                      rfl

theorem cell23_6508170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_6508170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508170 prefixEnd_6508170 := by exact prefixLift 6508170
  have htrace : WordTrace (prefixWord ++ tailWord_6508170) baseStart_6508170 baseEnd_6508170 := by
    simpa [prefixWord, tailWord_6508170, baseEnd_6508170] using wordTrace_append hprefix tailTrace_6508170
  have hstable : (prefixWord ++ tailWord_6508170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508170).length < 2 ^ (prefixWord ++ tailWord_6508170).sum := by decide
  have hdescent : baseEnd_6508170 < baseStart_6508170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508220 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6508220 : Nat := 118140960795 + 6508220 * 2 ^ 59
def prefixEnd_6508220 : Nat := 4983230072969 + 3 ^ 40 * 6508220 * 2
def baseEnd_6508220 : Nat := 3341845065204631793019247

theorem tailTrace_6508220 : CollatzResearch.WordTrace tailWord_6508220 prefixEnd_6508220 3341845065204631793019247 := by
  unfold tailWord_6508220
  simp only [CollatzResearch.WordTrace]
  refine ⟨118687142240918965164421057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158249522987891953552561409 118687142240918965164421057)
  ·
    refine ⟨89015356680689223873315793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118687142240918965164421057 89015356680689223873315793)
    ·
      refine ⟨66761517510516917904986845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89015356680689223873315793 66761517510516917904986845)
      ·
        refine ⟨25035569066443844214370067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66761517510516917904986845 25035569066443844214370067)
        ·
          refine ⟨37553353599665766321555101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25035569066443844214370067 37553353599665766321555101)
          ·
            refine ⟨14082507599874662370583163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37553353599665766321555101 14082507599874662370583163)
            ·
              refine ⟨21123761399811993555874745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14082507599874662370583163 21123761399811993555874745)
              ·
                refine ⟨15842821049858995166906059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21123761399811993555874745 15842821049858995166906059)
                ·
                  refine ⟨23764231574788492750359089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15842821049858995166906059 23764231574788492750359089)
                  ·
                    refine ⟨17823173681091369562769317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23764231574788492750359089 17823173681091369562769317)
                    ·
                      refine ⟨3341845065204631793019247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17823173681091369562769317 3341845065204631793019247)
                      ·
                        rfl

theorem cell23_6508220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6508220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508220 prefixEnd_6508220 := by exact prefixLift 6508220
  have htrace : WordTrace (prefixWord ++ tailWord_6508220) baseStart_6508220 baseEnd_6508220 := by
    simpa [prefixWord, tailWord_6508220, baseEnd_6508220] using wordTrace_append hprefix tailTrace_6508220
  have hstable : (prefixWord ++ tailWord_6508220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508220).length < 2 ^ (prefixWord ++ tailWord_6508220).sum := by decide
  have hdescent : baseEnd_6508220 < baseStart_6508220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508224 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 1, 2, 2]
def baseStart_6508224 : Nat := 118140960795 + 6508224 * 2 ^ 59
def prefixEnd_6508224 : Nat := 4983230072969 + 3 ^ 40 * 6508224 * 2
def baseEnd_6508224 : Nat := 3341847119127249777369229

theorem tailTrace_6508224 : CollatzResearch.WordTrace tailWord_6508224 prefixEnd_6508224 3341847119127249777369229 := by
  unfold tailWord_6508224
  simp only [CollatzResearch.WordTrace]
  refine ⟨118687215186911719505993863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158249620249215626007991817 118687215186911719505993863)
  ·
    refine ⟨178030822780367579258990795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118687215186911719505993863 178030822780367579258990795)
    ·
      refine ⟨267046234170551368888486193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178030822780367579258990795 267046234170551368888486193)
      ·
        refine ⟨200284675627913526666364645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267046234170551368888486193 200284675627913526666364645)
        ·
          refine ⟨37553376680233786249943371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200284675627913526666364645 37553376680233786249943371)
          ·
            refine ⟨56330065020350679374915057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37553376680233786249943371 56330065020350679374915057)
            ·
              refine ⟨42247548765263009531186293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56330065020350679374915057 42247548765263009531186293)
              ·
                refine ⟨3960707696743407143548715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42247548765263009531186293 3960707696743407143548715)
                ·
                  refine ⟨5941061545115110715323073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960707696743407143548715 5941061545115110715323073)
                  ·
                    refine ⟨4455796158836333036492305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941061545115110715323073 4455796158836333036492305)
                    ·
                      refine ⟨3341847119127249777369229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455796158836333036492305 3341847119127249777369229)
                      ·
                        rfl

theorem cell23_6508224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_6508224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508224 prefixEnd_6508224 := by exact prefixLift 6508224
  have htrace : WordTrace (prefixWord ++ tailWord_6508224) baseStart_6508224 baseEnd_6508224 := by
    simpa [prefixWord, tailWord_6508224, baseEnd_6508224] using wordTrace_append hprefix tailTrace_6508224
  have hstable : (prefixWord ++ tailWord_6508224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508224).length < 2 ^ (prefixWord ++ tailWord_6508224).sum := by decide
  have hdescent : baseEnd_6508224 < baseStart_6508224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508241 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 1, 2, 2]
def baseStart_6508241 : Nat := 118140960795 + 6508241 * 2 ^ 59
def prefixEnd_6508241 : Nat := 4983230072969 + 3 ^ 40 * 6508241 * 2
def baseEnd_6508241 : Nat := 3341855848298376210856651

theorem tailTrace_6508241 : CollatzResearch.WordTrace tailWord_6508241 prefixEnd_6508241 3341855848298376210856651 := by
  unfold tailWord_6508241
  simp only [CollatzResearch.WordTrace]
  refine ⟨237375050414761850915356577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158250033609841233943571051 237375050414761850915356577)
  ·
    refine ⟨178031287811071388186517433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237375050414761850915356577 178031287811071388186517433)
    ·
      refine ⟨133523465858303541139888075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178031287811071388186517433 133523465858303541139888075)
      ·
        refine ⟨200285198787455311709832113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133523465858303541139888075 200285198787455311709832113)
        ·
          refine ⟨150213899090591483782374085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200285198787455311709832113 150213899090591483782374085)
          ·
            refine ⟨28165106079485903209195141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150213899090591483782374085 28165106079485903209195141)
            ·
              refine ⟨5280957389903606851724089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28165106079485903209195141 5280957389903606851724089)
              ·
                refine ⟨3960718042427705138793067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5280957389903606851724089 3960718042427705138793067)
                ·
                  refine ⟨5941077063641557708189601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960718042427705138793067 5941077063641557708189601)
                  ·
                    refine ⟨4455807797731168281142201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941077063641557708189601 4455807797731168281142201)
                    ·
                      refine ⟨3341855848298376210856651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455807797731168281142201 3341855848298376210856651)
                      ·
                        rfl

theorem cell23_6508241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_6508241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508241 prefixEnd_6508241 := by exact prefixLift 6508241
  have htrace : WordTrace (prefixWord ++ tailWord_6508241) baseStart_6508241 baseEnd_6508241 := by
    simpa [prefixWord, tailWord_6508241, baseEnd_6508241] using wordTrace_append hprefix tailTrace_6508241
  have hstable : (prefixWord ++ tailWord_6508241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508241).length < 2 ^ (prefixWord ++ tailWord_6508241).sum := by decide
  have hdescent : baseEnd_6508241 < baseStart_6508241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508257 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_6508257 : Nat := 118140960795 + 6508257 * 2 ^ 59
def prefixEnd_6508257 : Nat := 4983230072969 + 3 ^ 40 * 6508257 * 2
def baseEnd_6508257 : Nat := 3341864063988848148256577

theorem tailTrace_6508257 : CollatzResearch.WordTrace tailWord_6508257 prefixEnd_6508257 3341864063988848148256577 := by
  unfold tailWord_6508257
  simp only [CollatzResearch.WordTrace]
  refine ⟨237375633982703885647939025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158250422655135923765292683 237375633982703885647939025)
  ·
    refine ⟨178031725487027914235954269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237375633982703885647939025 178031725487027914235954269)
    ·
      refine ⟨66761897057635467838482851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178031725487027914235954269 66761897057635467838482851)
      ·
        refine ⟨100142845586453201757724277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66761897057635467838482851 100142845586453201757724277)
        ·
          refine ⟨9388391773729987664786651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100142845586453201757724277 9388391773729987664786651)
          ·
            refine ⟨14082587660594981497179977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9388391773729987664786651 14082587660594981497179977)
            ·
              refine ⟨10561940745446236122884983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14082587660594981497179977 10561940745446236122884983)
              ·
                refine ⟨15842911118169354184327475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10561940745446236122884983 15842911118169354184327475)
                ·
                  refine ⟨23764366677254031276491213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15842911118169354184327475 23764366677254031276491213)
                  ·
                    refine ⟨8911637503970261728684205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23764366677254031276491213 8911637503970261728684205)
                    ·
                      refine ⟨3341864063988848148256577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911637503970261728684205 3341864063988848148256577)
                      ·
                        rfl

theorem cell23_6508257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_6508257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508257 prefixEnd_6508257 := by exact prefixLift 6508257
  have htrace : WordTrace (prefixWord ++ tailWord_6508257) baseStart_6508257 baseEnd_6508257 := by
    simpa [prefixWord, tailWord_6508257, baseEnd_6508257] using wordTrace_append hprefix tailTrace_6508257
  have hstable : (prefixWord ++ tailWord_6508257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508257).length < 2 ^ (prefixWord ++ tailWord_6508257).sum := by decide
  have hdescent : baseEnd_6508257 < baseStart_6508257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508280 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 3, 4, 2]
def baseStart_6508280 : Nat := 118140960795 + 6508280 * 2 ^ 59
def prefixEnd_6508280 : Nat := 4983230072969 + 3 ^ 40 * 6508280 * 2
def baseEnd_6508280 : Nat := 3341875874043901558268971

theorem tailTrace_6508280 : CollatzResearch.WordTrace tailWord_6508280 prefixEnd_6508280 3341875874043901558268971 := by
  unfold tailWord_6508280
  simp only [CollatzResearch.WordTrace]
  refine ⟨118688236430810280288013147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158250981907747040384017529 118688236430810280288013147)
  ·
    refine ⟨178032354646215420432019721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118688236430810280288013147 178032354646215420432019721)
    ·
      refine ⟨133524265984661565324014791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178032354646215420432019721 133524265984661565324014791)
      ·
        refine ⟨200286398976992347986022187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133524265984661565324014791 200286398976992347986022187)
        ·
          refine ⟨300429598465488521979033281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200286398976992347986022187 300429598465488521979033281)
          ·
            refine ⟨225322198849116391484274961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300429598465488521979033281 225322198849116391484274961)
            ·
              refine ⟨168991649136837293613206221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225322198849116391484274961 168991649136837293613206221)
              ·
                refine ⟨63371868426313985104952333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168991649136837293613206221 63371868426313985104952333)
                ·
                  refine ⟨23764450659867744414357125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63371868426313985104952333 23764450659867744414357125)
                  ·
                    refine ⟨4455834498725202077691961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23764450659867744414357125 4455834498725202077691961)
                    ·
                      refine ⟨3341875874043901558268971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455834498725202077691961 3341875874043901558268971)
                      ·
                        rfl

theorem cell23_6508280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_6508280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508280 prefixEnd_6508280 := by exact prefixLift 6508280
  have htrace : WordTrace (prefixWord ++ tailWord_6508280) baseStart_6508280 baseEnd_6508280 := by
    simpa [prefixWord, tailWord_6508280, baseEnd_6508280] using wordTrace_append hprefix tailTrace_6508280
  have hstable : (prefixWord ++ tailWord_6508280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508280).length < 2 ^ (prefixWord ++ tailWord_6508280).sum := by decide
  have hdescent : baseEnd_6508280 < baseStart_6508280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508283 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 3]
def baseStart_6508283 : Nat := 118140960795 + 6508283 * 2 ^ 59
def prefixEnd_6508283 : Nat := 4983230072969 + 3 ^ 40 * 6508283 * 2
def baseEnd_6508283 : Nat := 3341877414485865046531457

theorem tailTrace_6508283 : CollatzResearch.WordTrace tailWord_6508283 prefixEnd_6508283 3341877414485865046531457 := by
  unfold tailWord_6508283
  simp only [CollatzResearch.WordTrace]
  refine ⟨237376582280609692088385503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158251054853739794725590335 237376582280609692088385503)
  ·
    refine ⟨356064873420914538132578255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237376582280609692088385503 356064873420914538132578255)
    ·
      refine ⟨534097310131371807198867383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356064873420914538132578255 534097310131371807198867383)
      ·
        refine ⟨801145965197057710798301075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534097310131371807198867383 801145965197057710798301075)
        ·
          refine ⟨1201718947795586566197451613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801145965197057710798301075 1201718947795586566197451613)
          ·
            refine ⟨450644605423344962324044355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1201718947795586566197451613 450644605423344962324044355)
            ·
              refine ⟨675966908135017443486066533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450644605423344962324044355 675966908135017443486066533)
              ·
                refine ⟨126743795275315770653637475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675966908135017443486066533 126743795275315770653637475)
                ·
                  refine ⟨190115692912973655980456213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126743795275315770653637475 190115692912973655980456213)
                  ·
                    refine ⟨8911673105295640124083885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 190115692912973655980456213 8911673105295640124083885)
                    ·
                      refine ⟨3341877414485865046531457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911673105295640124083885 3341877414485865046531457)
                      ·
                        rfl

theorem cell23_6508283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 3].length) (baseStart_6508283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508283 prefixEnd_6508283 := by exact prefixLift 6508283
  have htrace : WordTrace (prefixWord ++ tailWord_6508283) baseStart_6508283 baseEnd_6508283 := by
    simpa [prefixWord, tailWord_6508283, baseEnd_6508283] using wordTrace_append hprefix tailTrace_6508283
  have hstable : (prefixWord ++ tailWord_6508283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508283).length < 2 ^ (prefixWord ++ tailWord_6508283).sum := by decide
  have hdescent : baseEnd_6508283 < baseStart_6508283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508290 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_6508290 : Nat := 118140960795 + 6508290 * 2 ^ 59
def prefixEnd_6508290 : Nat := 4983230072969 + 3 ^ 40 * 6508290 * 2
def baseEnd_6508290 : Nat := 1113960336283482173047975

theorem tailTrace_6508290 : CollatzResearch.WordTrace tailWord_6508290 prefixEnd_6508290 1113960336283482173047975 := by
  unfold tailWord_6508290
  simp only [CollatzResearch.WordTrace]
  refine ⟨59344209397896083070972581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158251225061056221522593549 59344209397896083070972581)
  ·
    refine ⟨11127039262105515575807359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59344209397896083070972581 11127039262105515575807359)
    ·
      refine ⟨16690558893158273363711039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11127039262105515575807359 16690558893158273363711039)
      ·
        refine ⟨25035838339737410045566559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16690558893158273363711039 25035838339737410045566559)
        ·
          refine ⟨37553757509606115068349839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25035838339737410045566559 37553757509606115068349839)
          ·
            refine ⟨56330636264409172602524759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37553757509606115068349839 56330636264409172602524759)
            ·
              refine ⟨84495954396613758903787139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56330636264409172602524759 84495954396613758903787139)
              ·
                refine ⟨126743931594920638355680709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84495954396613758903787139 126743931594920638355680709)
                ·
                  refine ⟨23764487174047619691690133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126743931594920638355680709 23764487174047619691690133)
                  ·
                    refine ⟨1113960336283482173047975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23764487174047619691690133 1113960336283482173047975)
                    ·
                      rfl

theorem cell23_6508290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_6508290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508290 prefixEnd_6508290 := by exact prefixLift 6508290
  have htrace : WordTrace (prefixWord ++ tailWord_6508290) baseStart_6508290 baseEnd_6508290 := by
    simpa [prefixWord, tailWord_6508290, baseEnd_6508290] using wordTrace_append hprefix tailTrace_6508290
  have hstable : (prefixWord ++ tailWord_6508290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508290).length < 2 ^ (prefixWord ++ tailWord_6508290).sum := by decide
  have hdescent : baseEnd_6508290 < baseStart_6508290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508308 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6508308 : Nat := 118140960795 + 6508308 * 2 ^ 59
def prefixEnd_6508308 : Nat := 4983230072969 + 3 ^ 40 * 6508308 * 2
def baseEnd_6508308 : Nat := 3341890251502227448718843

theorem tailTrace_6508308 : CollatzResearch.WordTrace tailWord_6508308 prefixEnd_6508308 3341890251502227448718843 := by
  unfold tailWord_6508308
  simp only [CollatzResearch.WordTrace]
  refine ⟨118688747052759560679022789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158251662737012747572030385 118688747052759560679022789)
  ·
    refine ⟨22254140072392417627316773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118688747052759560679022789 22254140072392417627316773)
    ·
      refine ⟨4172651263573578305121895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22254140072392417627316773 4172651263573578305121895)
      ·
        refine ⟨6258976895360367457682843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4172651263573578305121895 6258976895360367457682843)
        ·
          refine ⟨9388465343040551186524265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258976895360367457682843 9388465343040551186524265)
          ·
            refine ⟨7041349007280413389893199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9388465343040551186524265 7041349007280413389893199)
            ·
              refine ⟨10562023510920620084839799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041349007280413389893199 10562023510920620084839799)
              ·
                refine ⟨15843035266380930127259699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10562023510920620084839799 15843035266380930127259699)
                ·
                  refine ⟨23764552899571395190889549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15843035266380930127259699 23764552899571395190889549)
                  ·
                    refine ⟨8911707337339273196583581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23764552899571395190889549 8911707337339273196583581)
                    ·
                      refine ⟨3341890251502227448718843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911707337339273196583581 3341890251502227448718843)
                      ·
                        rfl

theorem cell23_6508308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6508308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508308 prefixEnd_6508308 := by exact prefixLift 6508308
  have htrace : WordTrace (prefixWord ++ tailWord_6508308) baseStart_6508308 baseEnd_6508308 := by
    simpa [prefixWord, tailWord_6508308, baseEnd_6508308] using wordTrace_append hprefix tailTrace_6508308
  have hstable : (prefixWord ++ tailWord_6508308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508308).length < 2 ^ (prefixWord ++ tailWord_6508308).sum := by decide
  have hdescent : baseEnd_6508308 < baseStart_6508308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508314 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2]
def baseStart_6508314 : Nat := 118140960795 + 6508314 * 2 ^ 59
def prefixEnd_6508314 : Nat := 4983230072969 + 3 ^ 40 * 6508314 * 2
def baseEnd_6508314 : Nat := 3341893332386154425243815

theorem tailTrace_6508314 : CollatzResearch.WordTrace tailWord_6508314 prefixEnd_6508314 3341893332386154425243815 := by
  unfold tailWord_6508314
  simp only [CollatzResearch.WordTrace]
  refine ⟨59344428235874346095690999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158251808628998256255175997 59344428235874346095690999)
  ·
    refine ⟨89016642353811519143536499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59344428235874346095690999 89016642353811519143536499)
    ·
      refine ⟨133524963530717278715304749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89016642353811519143536499 133524963530717278715304749)
      ·
        refine ⟨50071861324018979518239281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133524963530717278715304749 50071861324018979518239281)
        ·
          refine ⟨37553895993014234638679461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50071861324018979518239281 37553895993014234638679461)
          ·
            refine ⟨7041355498690168994752399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37553895993014234638679461 7041355498690168994752399)
            ·
              refine ⟨10562033248035253492128599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041355498690168994752399 10562033248035253492128599)
              ·
                refine ⟨15843049872052880238192899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10562033248035253492128599 15843049872052880238192899)
                ·
                  refine ⟨23764574808079320357289349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15843049872052880238192899 23764574808079320357289349)
                  ·
                    refine ⟨4455857776514872566991753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23764574808079320357289349 4455857776514872566991753)
                    ·
                      refine ⟨3341893332386154425243815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455857776514872566991753 3341893332386154425243815)
                      ·
                        rfl

theorem cell23_6508314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_6508314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508314 prefixEnd_6508314 := by exact prefixLift 6508314
  have htrace : WordTrace (prefixWord ++ tailWord_6508314) baseStart_6508314 baseEnd_6508314 := by
    simpa [prefixWord, tailWord_6508314, baseEnd_6508314] using wordTrace_append hprefix tailTrace_6508314
  have hstable : (prefixWord ++ tailWord_6508314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508314).length < 2 ^ (prefixWord ++ tailWord_6508314).sum := by decide
  have hdescent : baseEnd_6508314 < baseStart_6508314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508337 : List Nat := [1, 2, 2, 3, 2, 2, 3, 3, 5]
def baseStart_6508337 : Nat := 118140960795 + 6508337 * 2 ^ 59
def prefixEnd_6508337 : Nat := 4983230072969 + 3 ^ 40 * 6508337 * 2
def baseEnd_6508337 : Nat := 371322793604578648361801

theorem tailTrace_6508337 : CollatzResearch.WordTrace tailWord_6508337 prefixEnd_6508337 371322793604578648361801 := by
  unfold tailWord_6508337
  simp only [CollatzResearch.WordTrace]
  refine ⟨237378551822414059310851265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158252367881609372873900843 237378551822414059310851265)
  ·
    refine ⟨178033913866810544483138449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237378551822414059310851265 178033913866810544483138449)
    ·
      refine ⟨133525435400107908362353837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178033913866810544483138449 133525435400107908362353837)
      ·
        refine ⟨50072038275040465635882689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133525435400107908362353837 50072038275040465635882689)
        ·
          refine ⟨37554028706280349226912017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50072038275040465635882689 37554028706280349226912017)
          ·
            refine ⟨28165521529710261920184013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37554028706280349226912017 28165521529710261920184013)
            ·
              refine ⟨10562070573641348220069005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28165521529710261920184013 10562070573641348220069005)
              ·
                refine ⟨3960776465115505582525877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10562070573641348220069005 3960776465115505582525877)
                ·
                  refine ⟨371322793604578648361801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960776465115505582525877 371322793604578648361801)
                  ·
                    rfl

theorem cell23_6508337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 5].length) (baseStart_6508337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508337 prefixEnd_6508337 := by exact prefixLift 6508337
  have htrace : WordTrace (prefixWord ++ tailWord_6508337) baseStart_6508337 baseEnd_6508337 := by
    simpa [prefixWord, tailWord_6508337, baseEnd_6508337] using wordTrace_append hprefix tailTrace_6508337
  have hstable : (prefixWord ++ tailWord_6508337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508337).length < 2 ^ (prefixWord ++ tailWord_6508337).sum := by decide
  have hdescent : baseEnd_6508337 < baseStart_6508337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508360 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_6508360 : Nat := 118140960795 + 6508360 * 2 ^ 59
def prefixEnd_6508360 : Nat := 4983230072969 + 3 ^ 40 * 6508360 * 2
def baseEnd_6508360 : Nat := 3341916952496261245268603

theorem tailTrace_6508360 : CollatzResearch.WordTrace tailWord_6508360 prefixEnd_6508360 3341916952496261245268603 := by
  unfold tailWord_6508360
  simp only [CollatzResearch.WordTrace]
  refine ⟨118689695350665367119469267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158252927134220489492625689 118689695350665367119469267)
  ·
    refine ⟨178034543025998050679203901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118689695350665367119469267 178034543025998050679203901)
    ·
      refine ⟨66762953634749269004701463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178034543025998050679203901 66762953634749269004701463)
      ·
        refine ⟨100144430452123903507052195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66762953634749269004701463 100144430452123903507052195)
        ·
          refine ⟨150216645678185855260578293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100144430452123903507052195 150216645678185855260578293)
          ·
            refine ⟨14082810532329923930679215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150216645678185855260578293 14082810532329923930679215)
            ·
              refine ⟨21124215798494885896018823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14082810532329923930679215 21124215798494885896018823)
              ·
                refine ⟨31686323697742328844028235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21124215798494885896018823 31686323697742328844028235)
                ·
                  refine ⟨47529485546613493266042353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31686323697742328844028235 47529485546613493266042353)
                  ·
                    refine ⟨35647114159960119949531765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47529485546613493266042353 35647114159960119949531765)
                    ·
                      refine ⟨3341916952496261245268603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35647114159960119949531765 3341916952496261245268603)
                      ·
                        rfl

theorem cell23_6508360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_6508360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508360 prefixEnd_6508360 := by exact prefixLift 6508360
  have htrace : WordTrace (prefixWord ++ tailWord_6508360) baseStart_6508360 baseEnd_6508360 := by
    simpa [prefixWord, tailWord_6508360, baseEnd_6508360] using wordTrace_append hprefix tailTrace_6508360
  have hstable : (prefixWord ++ tailWord_6508360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508360).length < 2 ^ (prefixWord ++ tailWord_6508360).sum := by decide
  have hdescent : baseEnd_6508360 < baseStart_6508360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508365 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_6508365 : Nat := 118140960795 + 6508365 * 2 ^ 59
def prefixEnd_6508365 : Nat := 4983230072969 + 3 ^ 40 * 6508365 * 2
def baseEnd_6508365 : Nat := 3341919519899533725706081

theorem tailTrace_6508365 : CollatzResearch.WordTrace tailWord_6508365 prefixEnd_6508365 3341919519899533725706081 := by
  unfold tailWord_6508365
  simp only [CollatzResearch.WordTrace]
  refine ⟨237379573066312620092870549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158253048710875080061913699 237379573066312620092870549)
  ·
    refine ⟨11127167487483404066853307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237379573066312620092870549 11127167487483404066853307)
    ·
      refine ⟨16690751231225106100279961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11127167487483404066853307 16690751231225106100279961)
      ·
        refine ⟨12518063423418829575209971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16690751231225106100279961 12518063423418829575209971)
        ·
          refine ⟨18777095135128244362814957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12518063423418829575209971 18777095135128244362814957)
          ·
            refine ⟨7041410675673091636055609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18777095135128244362814957 7041410675673091636055609)
            ·
              refine ⟨5281058006754818727041707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7041410675673091636055609 5281058006754818727041707)
              ·
                refine ⟨7921587010132228090562561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281058006754818727041707 7921587010132228090562561)
                ·
                  refine ⟨5941190257599171067921921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7921587010132228090562561 5941190257599171067921921)
                  ·
                    refine ⟨4455892693199378300941441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941190257599171067921921 4455892693199378300941441)
                    ·
                      refine ⟨3341919519899533725706081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4455892693199378300941441 3341919519899533725706081)
                      ·
                        rfl

theorem cell23_6508365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_6508365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508365 prefixEnd_6508365 := by exact prefixLift 6508365
  have htrace : WordTrace (prefixWord ++ tailWord_6508365) baseStart_6508365 baseEnd_6508365 := by
    simpa [prefixWord, tailWord_6508365, baseEnd_6508365] using wordTrace_append hprefix tailTrace_6508365
  have hstable : (prefixWord ++ tailWord_6508365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508365).length < 2 ^ (prefixWord ++ tailWord_6508365).sum := by decide
  have hdescent : baseEnd_6508365 < baseStart_6508365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508393 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 10]
def baseStart_6508393 : Nat := 118140960795 + 6508393 * 2 ^ 59
def prefixEnd_6508393 : Nat := 4983230072969 + 3 ^ 40 * 6508393 * 2
def baseEnd_6508393 : Nat := 371325988595317735128439

theorem tailTrace_6508393 : CollatzResearch.WordTrace tailWord_6508393 prefixEnd_6508393 371325988595317735128439 := by
  unfold tailWord_6508393
  simp only [CollatzResearch.WordTrace]
  refine ⟨237380594310211180874889833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158253729540140787249926555 237380594310211180874889833)
  ·
    refine ⟨178035445732658385656167375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237380594310211180874889833 178035445732658385656167375)
    ·
      refine ⟨267053168598987578484251063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178035445732658385656167375 267053168598987578484251063)
      ·
        refine ⟨400579752898481367726376595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267053168598987578484251063 400579752898481367726376595)
        ·
          refine ⟨600869629347722051589564893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400579752898481367726376595 600869629347722051589564893)
          ·
            refine ⟨225326111005395769346086835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600869629347722051589564893 225326111005395769346086835)
            ·
              refine ⟨337989166508093654019130253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225326111005395769346086835 337989166508093654019130253)
              ·
                refine ⟨126745937440535120257173845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337989166508093654019130253 126745937440535120257173845)
                ·
                  refine ⟨371325988595317735128439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126745937440535120257173845 371325988595317735128439)
                  ·
                    rfl

theorem cell23_6508393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_6508393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508393 prefixEnd_6508393 := by exact prefixLift 6508393
  have htrace : WordTrace (prefixWord ++ tailWord_6508393) baseStart_6508393 baseEnd_6508393 := by
    simpa [prefixWord, tailWord_6508393, baseEnd_6508393] using wordTrace_append hprefix tailTrace_6508393
  have hstable : (prefixWord ++ tailWord_6508393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508393).length < 2 ^ (prefixWord ++ tailWord_6508393).sum := by decide
  have hdescent : baseEnd_6508393 < baseStart_6508393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508410 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_6508410 : Nat := 118140960795 + 6508410 * 2 ^ 59
def prefixEnd_6508410 : Nat := 4983230072969 + 3 ^ 40 * 6508410 * 2
def baseEnd_6508410 : Nat := 371326958503220672182597

theorem tailTrace_6508410 : CollatzResearch.WordTrace tailWord_6508410 prefixEnd_6508410 371326958503220672182597 := by
  unfold tailWord_6508410
  simp only [CollatzResearch.WordTrace]
  refine ⟨59345303587787398194564671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158254142900766395185505789 59345303587787398194564671)
  ·
    refine ⟨89017955381681097291847007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59345303587787398194564671 89017955381681097291847007)
    ·
      refine ⟨133526933072521645937770511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89017955381681097291847007 133526933072521645937770511)
      ·
        refine ⟨200290399608782468906655767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133526933072521645937770511 200290399608782468906655767)
        ·
          refine ⟨300435599413173703359983651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200290399608782468906655767 300435599413173703359983651)
          ·
            refine ⟨450653399119760555039975477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300435599413173703359983651 450653399119760555039975477)
            ·
              refine ⟨42248756167477552034997701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 450653399119760555039975477 42248756167477552034997701)
              ·
                refine ⟨7921641781402041006562069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42248756167477552034997701 7921641781402041006562069)
                ·
                  refine ⟨371326958503220672182597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7921641781402041006562069 371326958503220672182597)
                  ·
                    rfl

theorem cell23_6508410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_6508410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508410 prefixEnd_6508410 := by exact prefixLift 6508410
  have htrace : WordTrace (prefixWord ++ tailWord_6508410) baseStart_6508410 baseEnd_6508410 := by
    simpa [prefixWord, tailWord_6508410, baseEnd_6508410] using wordTrace_append hprefix tailTrace_6508410
  have hstable : (prefixWord ++ tailWord_6508410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508410).length < 2 ^ (prefixWord ++ tailWord_6508410).sum := by decide
  have hdescent : baseEnd_6508410 < baseStart_6508410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508494 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_6508494 : Nat := 118140960795 + 6508494 * 2 ^ 59
def prefixEnd_6508494 : Nat := 4983230072969 + 3 ^ 40 * 6508494 * 2
def baseEnd_6508494 : Nat := 3341985758903963720992987

theorem tailTrace_6508494 : CollatzResearch.WordTrace tailWord_6508494 prefixEnd_6508494 3341985758903963720992987 := by
  unfold tailWord_6508494
  simp only [CollatzResearch.WordTrace]
  refine ⟨29673034760355659390539567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158256185388563516749544357 29673034760355659390539567)
  ·
    refine ⟨44509552140533489085809351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29673034760355659390539567 44509552140533489085809351)
    ·
      refine ⟨66764328210800233628714027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44509552140533489085809351 66764328210800233628714027)
      ·
        refine ⟨100146492316200350443071041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66764328210800233628714027 100146492316200350443071041)
        ·
          refine ⟨75109869237150262832303281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100146492316200350443071041 75109869237150262832303281)
          ·
            refine ⟨56332401927862697124227461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75109869237150262832303281 56332401927862697124227461)
            ·
              refine ⟨10562325361474255710792649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56332401927862697124227461 10562325361474255710792649)
              ·
                refine ⟨7921744021105691783094487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10562325361474255710792649 7921744021105691783094487)
                ·
                  refine ⟨11882616031658537674641731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7921744021105691783094487 11882616031658537674641731)
                  ·
                    refine ⟨17823924047487806511962597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11882616031658537674641731 17823924047487806511962597)
                    ·
                      refine ⟨3341985758903963720992987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17823924047487806511962597 3341985758903963720992987)
                      ·
                        rfl

theorem cell23_6508494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_6508494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508494 prefixEnd_6508494 := by exact prefixLift 6508494
  have htrace : WordTrace (prefixWord ++ tailWord_6508494) baseStart_6508494 baseEnd_6508494 := by
    simpa [prefixWord, tailWord_6508494, baseEnd_6508494] using wordTrace_append hprefix tailTrace_6508494
  have hstable : (prefixWord ++ tailWord_6508494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508494).length < 2 ^ (prefixWord ++ tailWord_6508494).sum := by decide
  have hdescent : baseEnd_6508494 < baseStart_6508494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508505 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 1, 1, 3]
def baseStart_6508505 : Nat := 118140960795 + 6508505 * 2 ^ 59
def prefixEnd_6508505 : Nat := 4983230072969 + 3 ^ 40 * 6508505 * 2
def baseEnd_6508505 : Nat := 3341991407191163177955437

theorem tailTrace_6508505 : CollatzResearch.WordTrace tailWord_6508505 prefixEnd_6508505 3341991407191163177955437 := by
  unfold tailWord_6508505
  simp only [CollatzResearch.WordTrace]
  refine ⟨237384679285805424002966969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158256452857203616001977979 237384679285805424002966969)
  ·
    refine ⟨178038509464354068002225227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237384679285805424002966969 178038509464354068002225227)
    ·
      refine ⟨267057764196531102003337841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178038509464354068002225227 267057764196531102003337841)
      ·
        refine ⟨200293323147398326502503381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267057764196531102003337841 200293323147398326502503381)
        ·
          refine ⟨4694374761267148277402423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 200293323147398326502503381 4694374761267148277402423)
          ·
            refine ⟨7041562141900722416103635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4694374761267148277402423 7041562141900722416103635)
            ·
              refine ⟨10562343212851083624155453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041562141900722416103635 10562343212851083624155453)
              ·
                refine ⟨3960878704819156359058295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10562343212851083624155453 3960878704819156359058295)
                ·
                  refine ⟨5941318057228734538587443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3960878704819156359058295 5941318057228734538587443)
                  ·
                    refine ⟨8911977085843101807881165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5941318057228734538587443 8911977085843101807881165)
                    ·
                      refine ⟨3341991407191163177955437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8911977085843101807881165 3341991407191163177955437)
                      ·
                        rfl

theorem cell23_6508505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_6508505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508505 prefixEnd_6508505 := by exact prefixLift 6508505
  have htrace : WordTrace (prefixWord ++ tailWord_6508505) baseStart_6508505 baseEnd_6508505 := by
    simpa [prefixWord, tailWord_6508505, baseEnd_6508505] using wordTrace_append hprefix tailTrace_6508505
  have hstable : (prefixWord ++ tailWord_6508505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508505).length < 2 ^ (prefixWord ++ tailWord_6508505).sum := by decide
  have hdescent : baseEnd_6508505 < baseStart_6508505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508534 : List Nat := [5, 1, 1, 1, 4, 1, 2, 8]
def baseStart_6508534 : Nat := 118140960795 + 6508534 * 2 ^ 59
def prefixEnd_6508534 : Nat := 4983230072969 + 3 ^ 40 * 6508534 * 2
def baseEnd_6508534 : Nat := 123778011041857169055289

theorem tailTrace_6508534 : CollatzResearch.WordTrace tailWord_6508534 prefixEnd_6508534 123778011041857169055289 := by
  unfold tailWord_6508534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836608562668772622235791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158257158001800241303848437 14836608562668772622235791)
  ·
    refine ⟨22254912844003158933353687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14836608562668772622235791 22254912844003158933353687)
    ·
      refine ⟨33382369266004738400030531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22254912844003158933353687 33382369266004738400030531)
      ·
        refine ⟨50073553899007107600045797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33382369266004738400030531 50073553899007107600045797)
        ·
          refine ⟨9388791356063832675008587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50073553899007107600045797 9388791356063832675008587)
          ·
            refine ⟨14083187034095749012512881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9388791356063832675008587 14083187034095749012512881)
            ·
              refine ⟨10562390275571811759384661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14083187034095749012512881 10562390275571811759384661)
              ·
                refine ⟨123778011041857169055289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10562390275571811759384661 123778011041857169055289)
                ·
                  rfl

theorem cell23_6508534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_6508534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508534 prefixEnd_6508534 := by exact prefixLift 6508534
  have htrace : WordTrace (prefixWord ++ tailWord_6508534) baseStart_6508534 baseEnd_6508534 := by
    simpa [prefixWord, tailWord_6508534, baseEnd_6508534] using wordTrace_append hprefix tailTrace_6508534
  have hstable : (prefixWord ++ tailWord_6508534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508534).length < 2 ^ (prefixWord ++ tailWord_6508534).sum := by decide
  have hdescent : baseEnd_6508534 < baseStart_6508534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508560 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 8]
def baseStart_6508560 : Nat := 118140960795 + 6508560 * 2 ^ 59
def prefixEnd_6508560 : Nat := 4983230072969 + 3 ^ 40 * 6508560 * 2
def baseEnd_6508560 : Nat := 1114006549542386820922561

theorem tailTrace_6508560 : CollatzResearch.WordTrace tailWord_6508560 prefixEnd_6508560 1114006549542386820922561 := by
  unfold tailWord_6508560
  simp only [CollatzResearch.WordTrace]
  refine ⟨118693342650303084198109567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158257790200404112264146089 118693342650303084198109567)
  ·
    refine ⟨178040013975454626297164351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118693342650303084198109567 178040013975454626297164351)
    ·
      refine ⟨267060020963181939445746527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178040013975454626297164351 267060020963181939445746527)
      ·
        refine ⟨400590031444772909168619791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267060020963181939445746527 400590031444772909168619791)
        ·
          refine ⟨600885047167159363752929687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400590031444772909168619791 600885047167159363752929687)
          ·
            refine ⟨901327570750739045629394531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600885047167159363752929687 901327570750739045629394531)
            ·
              refine ⟨1351991356126108568444091797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901327570750739045629394531 1351991356126108568444091797)
              ·
                refine ⟨63374594818411339145816803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1351991356126108568444091797 63374594818411339145816803)
                ·
                  refine ⟨95061892227617008718725205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63374594818411339145816803 95061892227617008718725205)
                  ·
                    refine ⟨1114006549542386820922561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95061892227617008718725205 1114006549542386820922561)
                    ·
                      rfl

theorem cell23_6508560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_6508560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508560 prefixEnd_6508560 := by exact prefixLift 6508560
  have htrace : WordTrace (prefixWord ++ tailWord_6508560) baseStart_6508560 baseEnd_6508560 := by
    simpa [prefixWord, tailWord_6508560, baseEnd_6508560] using wordTrace_append hprefix tailTrace_6508560
  have hstable : (prefixWord ++ tailWord_6508560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508560).length < 2 ^ (prefixWord ++ tailWord_6508560).sum := by decide
  have hdescent : baseEnd_6508560 < baseStart_6508560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508597 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_6508597 : Nat := 118140960795 + 6508597 * 2 ^ 59
def prefixEnd_6508597 : Nat := 4983230072969 + 3 ^ 40 * 6508597 * 2
def baseEnd_6508597 : Nat := 3342038647411376818005013

theorem tailTrace_6508597 : CollatzResearch.WordTrace tailWord_6508597 prefixEnd_6508597 3342038647411376818005013 := by
  unfold tailWord_6508597
  simp only [CollatzResearch.WordTrace]
  refine ⟨237388034801472123715316045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158258689867648082476877363 237388034801472123715316045)
  ·
    refine ⟨89020513050552046393243517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237388034801472123715316045 89020513050552046393243517)
    ·
      refine ⟨33382692393957017397466319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89020513050552046393243517 33382692393957017397466319)
      ·
        refine ⟨50074038590935526096199479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33382692393957017397466319 50074038590935526096199479)
        ·
          refine ⟨75111057886403289144299219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50074038590935526096199479 75111057886403289144299219)
          ·
            refine ⟨112666586829604933716448829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75111057886403289144299219 112666586829604933716448829)
            ·
              refine ⟨42249970061101850143668311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112666586829604933716448829 42249970061101850143668311)
              ·
                refine ⟨63374955091652775215502467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42249970061101850143668311 63374955091652775215502467)
                ·
                  refine ⟨95062432637479162823253701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63374955091652775215502467 95062432637479162823253701)
                  ·
                    refine ⟨17824206119527343029360069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95062432637479162823253701 17824206119527343029360069)
                    ·
                      refine ⟨3342038647411376818005013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17824206119527343029360069 3342038647411376818005013)
                      ·
                        rfl

theorem cell23_6508597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_6508597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508597 prefixEnd_6508597 := by exact prefixLift 6508597
  have htrace : WordTrace (prefixWord ++ tailWord_6508597) baseStart_6508597 baseEnd_6508597 := by
    simpa [prefixWord, tailWord_6508597, baseEnd_6508597] using wordTrace_append hprefix tailTrace_6508597
  have hstable : (prefixWord ++ tailWord_6508597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508597).length < 2 ^ (prefixWord ++ tailWord_6508597).sum := by decide
  have hdescent : baseEnd_6508597 < baseStart_6508597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508617 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_6508617 : Nat := 118140960795 + 6508617 * 2 ^ 59
def prefixEnd_6508617 : Nat := 4983230072969 + 3 ^ 40 * 6508617 * 2
def baseEnd_6508617 : Nat := 3342048917024466739754921

theorem tailTrace_6508617 : CollatzResearch.WordTrace tailWord_6508617 prefixEnd_6508617 3342048917024466739754921 := by
  unfold tailWord_6508617
  simp only [CollatzResearch.WordTrace]
  refine ⟨237388764261399667131044105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158259176174266444754029403 237388764261399667131044105)
  ·
    refine ⟨178041573196049750348283079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237388764261399667131044105 178041573196049750348283079)
    ·
      refine ⟨267062359794074625522424619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178041573196049750348283079 267062359794074625522424619)
      ·
        refine ⟨400593539691111938283636929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267062359794074625522424619 400593539691111938283636929)
        ·
          refine ⟨300445154768333953712727697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400593539691111938283636929 300445154768333953712727697)
          ·
            refine ⟨225333866076250465284545773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300445154768333953712727697 225333866076250465284545773)
            ·
              refine ⟨84500199778593924481704665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225333866076250465284545773 84500199778593924481704665)
              ·
                refine ⟨63375149833945443361278499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84500199778593924481704665 63375149833945443361278499)
                ·
                  refine ⟨95062724750918165041917749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63375149833945443361278499 95062724750918165041917749)
                  ·
                    refine ⟨8912130445398577972679789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95062724750918165041917749 8912130445398577972679789)
                    ·
                      refine ⟨3342048917024466739754921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8912130445398577972679789 3342048917024466739754921)
                      ·
                        rfl

theorem cell23_6508617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_6508617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508617 prefixEnd_6508617 := by exact prefixLift 6508617
  have htrace : WordTrace (prefixWord ++ tailWord_6508617) baseStart_6508617 baseEnd_6508617 := by
    simpa [prefixWord, tailWord_6508617, baseEnd_6508617] using wordTrace_append hprefix tailTrace_6508617
  have hstable : (prefixWord ++ tailWord_6508617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508617).length < 2 ^ (prefixWord ++ tailWord_6508617).sum := by decide
  have hdescent : baseEnd_6508617 < baseStart_6508617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508644 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_6508644 : Nat := 118140960795 + 6508644 * 2 ^ 59
def prefixEnd_6508644 : Nat := 4983230072969 + 3 ^ 40 * 6508644 * 2
def baseEnd_6508644 : Nat := 3342062781002138134117297

theorem tailTrace_6508644 : CollatzResearch.WordTrace tailWord_6508644 prefixEnd_6508644 3342062781002138134117297 := by
  unfold tailWord_6508644
  simp only [CollatzResearch.WordTrace]
  refine ⟨118694874516150925371138493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158259832688201233828184657 118694874516150925371138493)
  ·
    refine ⟨44510577943556597014176935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118694874516150925371138493 44510577943556597014176935)
    ·
      refine ⟨66765866915334895521265403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44510577943556597014176935 66765866915334895521265403)
      ·
        refine ⟨100148800373002343281898105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66765866915334895521265403 100148800373002343281898105)
        ·
          refine ⟨75111600279751757461423579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100148800373002343281898105 75111600279751757461423579)
          ·
            refine ⟨112667400419627636192135369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75111600279751757461423579 112667400419627636192135369)
            ·
              refine ⟨84500550314720727144101527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112667400419627636192135369 84500550314720727144101527)
              ·
                refine ⟨126750825472081090716152291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84500550314720727144101527 126750825472081090716152291)
                ·
                  refine ⟨190126238208121636074228437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126750825472081090716152291 190126238208121636074228437)
                  ·
                    refine ⟨4456083708002850845489729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 190126238208121636074228437 4456083708002850845489729)
                    ·
                      refine ⟨3342062781002138134117297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456083708002850845489729 3342062781002138134117297)
                      ·
                        rfl

theorem cell23_6508644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_6508644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508644 prefixEnd_6508644 := by exact prefixLift 6508644
  have htrace : WordTrace (prefixWord ++ tailWord_6508644) baseStart_6508644 baseEnd_6508644 := by
    simpa [prefixWord, tailWord_6508644, baseEnd_6508644] using wordTrace_append hprefix tailTrace_6508644
  have hstable : (prefixWord ++ tailWord_6508644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508644).length < 2 ^ (prefixWord ++ tailWord_6508644).sum := by decide
  have hdescent : baseEnd_6508644 < baseStart_6508644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508647 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6508647 : Nat := 118140960795 + 6508647 * 2 ^ 59
def prefixEnd_6508647 : Nat := 4983230072969 + 3 ^ 40 * 6508647 * 2
def baseEnd_6508647 : Nat := 3342064321444101622379783

theorem tailTrace_6508647 : CollatzResearch.WordTrace tailWord_6508647 prefixEnd_6508647 3342064321444101622379783 := by
  unfold tailWord_6508647
  simp only [CollatzResearch.WordTrace]
  refine ⟨237389858451290982254636195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158259905634193988169757463 237389858451290982254636195)
  ·
    refine ⟨356084787676936473381954293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237389858451290982254636195 356084787676936473381954293)
    ·
      refine ⟨33382948844712794379558215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356084787676936473381954293 33382948844712794379558215)
      ·
        refine ⟨50074423267069191569337323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33382948844712794379558215 50074423267069191569337323)
        ·
          refine ⟨75111634900603787354005985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50074423267069191569337323 75111634900603787354005985)
          ·
            refine ⟨56333726175452840515504489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75111634900603787354005985 56333726175452840515504489)
            ·
              refine ⟨42250294631589630386628367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56333726175452840515504489 42250294631589630386628367)
              ·
                refine ⟨63375441947384445579942551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42250294631589630386628367 63375441947384445579942551)
                ·
                  refine ⟨95063162921076668369913827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63375441947384445579942551 95063162921076668369913827)
                  ·
                    refine ⟨142594744381615002554870741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95063162921076668369913827 142594744381615002554870741)
                    ·
                      refine ⟨3342064321444101622379783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142594744381615002554870741 3342064321444101622379783)
                      ·
                        rfl

theorem cell23_6508647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6508647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508647 prefixEnd_6508647 := by exact prefixLift 6508647
  have htrace : WordTrace (prefixWord ++ tailWord_6508647) baseStart_6508647 baseEnd_6508647 := by
    simpa [prefixWord, tailWord_6508647, baseEnd_6508647] using wordTrace_append hprefix tailTrace_6508647
  have hstable : (prefixWord ++ tailWord_6508647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508647).length < 2 ^ (prefixWord ++ tailWord_6508647).sum := by decide
  have hdescent : baseEnd_6508647 < baseStart_6508647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508657 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_6508657 : Nat := 118140960795 + 6508657 * 2 ^ 59
def prefixEnd_6508657 : Nat := 4983230072969 + 3 ^ 40 * 6508657 * 2
def baseEnd_6508657 : Nat := 3342069456250646583254737

theorem tailTrace_6508657 : CollatzResearch.WordTrace tailWord_6508657 prefixEnd_6508657 3342069456250646583254737 := by
  unfold tailWord_6508657
  simp only [CollatzResearch.WordTrace]
  refine ⟨237390223181254753962500225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158260148787503169308333483 237390223181254753962500225)
  ·
    refine ⟨178042667385941065471875169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237390223181254753962500225 178042667385941065471875169)
    ·
      refine ⟨133532000539455799103906377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178042667385941065471875169 133532000539455799103906377)
      ·
        refine ⟨100149000404591849327929783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133532000539455799103906377 100149000404591849327929783)
        ·
          refine ⟨150223500606887773991894675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100149000404591849327929783 150223500606887773991894675)
          ·
            refine ⟨225335250910331660987842013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150223500606887773991894675 225335250910331660987842013)
            ·
              refine ⟨84500719091374372870440755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225335250910331660987842013 84500719091374372870440755)
              ·
                refine ⟨126751078637061559305661133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84500719091374372870440755 126751078637061559305661133)
                ·
                  refine ⟨47531654488898084739622925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126751078637061559305661133 47531654488898084739622925)
                  ·
                    refine ⟨17824370433336781777358597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47531654488898084739622925 17824370433336781777358597)
                    ·
                      refine ⟨3342069456250646583254737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17824370433336781777358597 3342069456250646583254737)
                      ·
                        rfl

theorem cell23_6508657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_6508657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508657 prefixEnd_6508657 := by exact prefixLift 6508657
  have htrace : WordTrace (prefixWord ++ tailWord_6508657) baseStart_6508657 baseEnd_6508657 := by
    simpa [prefixWord, tailWord_6508657, baseEnd_6508657] using wordTrace_append hprefix tailTrace_6508657
  have hstable : (prefixWord ++ tailWord_6508657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508657).length < 2 ^ (prefixWord ++ tailWord_6508657).sum := by decide
  have hdescent : baseEnd_6508657 < baseStart_6508657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508701 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6508701 : Nat := 118140960795 + 6508701 * 2 ^ 59
def prefixEnd_6508701 : Nat := 4983230072969 + 3 ^ 40 * 6508701 * 2
def baseEnd_6508701 : Nat := 1114030683133148137034845

theorem tailTrace_6508701 : CollatzResearch.WordTrace tailWord_6508701 prefixEnd_6508701 1114030683133148137034845 := by
  unfold tailWord_6508701
  simp only [CollatzResearch.WordTrace]
  refine ⟨237391827993095349477101957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158261218662063566318067971 237391827993095349477101957)
  ·
    refine ⟨44510967748705378026956617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237391827993095349477101957 44510967748705378026956617)
    ·
      refine ⟨33383225811529033520217463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44510967748705378026956617 33383225811529033520217463)
      ·
        refine ⟨50074838717293550280326195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33383225811529033520217463 50074838717293550280326195)
        ·
          refine ⟨75112258075940325420489293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50074838717293550280326195 75112258075940325420489293)
          ·
            refine ⟨28167096778477622032683485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75112258075940325420489293 28167096778477622032683485)
            ·
              refine ⟨10562661291929108262256307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28167096778477622032683485 10562661291929108262256307)
              ·
                refine ⟨15843991937893662393384461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10562661291929108262256307 15843991937893662393384461)
                ·
                  refine ⟨5941496976710123397519173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15843991937893662393384461 5941496976710123397519173)
                  ·
                    refine ⟨1114030683133148137034845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5941496976710123397519173 1114030683133148137034845)
                    ·
                      rfl

theorem cell23_6508701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6508701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508701 prefixEnd_6508701 := by exact prefixLift 6508701
  have htrace : WordTrace (prefixWord ++ tailWord_6508701) baseStart_6508701 baseEnd_6508701 := by
    simpa [prefixWord, tailWord_6508701, baseEnd_6508701] using wordTrace_append hprefix tailTrace_6508701
  have hstable : (prefixWord ++ tailWord_6508701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508701).length < 2 ^ (prefixWord ++ tailWord_6508701).sum := by decide
  have hdescent : baseEnd_6508701 < baseStart_6508701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508748 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 6]
def baseStart_6508748 : Nat := 118140960795 + 6508748 * 2 ^ 59
def prefixEnd_6508748 : Nat := 4983230072969 + 3 ^ 40 * 6508748 * 2
def baseEnd_6508748 : Nat := 371346242554467303024091

theorem tailTrace_6508748 : CollatzResearch.WordTrace tailWord_6508748 prefixEnd_6508748 371346242554467303024091 := by
  unfold tailWord_6508748
  simp only [CollatzResearch.WordTrace]
  refine ⟨118696771111962538252031449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158262361482616717669375265 118696771111962538252031449)
  ·
    refine ⟨89022578333971903689023587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118696771111962538252031449 89022578333971903689023587)
    ·
      refine ⟨133533867500957855533535381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89022578333971903689023587 133533867500957855533535381)
      ·
        refine ⟨6259400039107399478134471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133533867500957855533535381 6259400039107399478134471)
        ·
          refine ⟨9389100058661099217201707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6259400039107399478134471 9389100058661099217201707)
          ·
            refine ⟨14083650087991648825802561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9389100058661099217201707 14083650087991648825802561)
            ·
              refine ⟨10562737565993736619351921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14083650087991648825802561 10562737565993736619351921)
              ·
                refine ⟨7922053174495302464513941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10562737565993736619351921 7922053174495302464513941)
                ·
                  refine ⟨371346242554467303024091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7922053174495302464513941 371346242554467303024091)
                  ·
                    rfl

theorem cell23_6508748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_6508748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508748 prefixEnd_6508748 := by exact prefixLift 6508748
  have htrace : WordTrace (prefixWord ++ tailWord_6508748) baseStart_6508748 baseEnd_6508748 := by
    simpa [prefixWord, tailWord_6508748, baseEnd_6508748] using wordTrace_append hprefix tailTrace_6508748
  have hstable : (prefixWord ++ tailWord_6508748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508748).length < 2 ^ (prefixWord ++ tailWord_6508748).sum := by decide
  have hdescent : baseEnd_6508748 < baseStart_6508748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508751 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 2, 3, 2]
def baseStart_6508751 : Nat := 118140960795 + 6508751 * 2 ^ 59
def prefixEnd_6508751 : Nat := 4983230072969 + 3 ^ 40 * 6508751 * 2
def baseEnd_6508751 : Nat := 3342117723432169215479305

theorem tailTrace_6508751 : CollatzResearch.WordTrace tailWord_6508751 prefixEnd_6508751 3342117723432169215479305 := by
  unfold tailWord_6508751
  simp only [CollatzResearch.WordTrace]
  refine ⟨237393651642914208016422107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158262434428609472010948071 237393651642914208016422107)
  ·
    refine ⟨356090477464371312024633161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237393651642914208016422107 356090477464371312024633161)
    ·
      refine ⟨267067858098278484018474871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356090477464371312024633161 267067858098278484018474871)
      ·
        refine ⟨400601787147417726027712307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267067858098278484018474871 400601787147417726027712307)
        ·
          refine ⟨600902680721126589041568461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400601787147417726027712307 600902680721126589041568461)
          ·
            refine ⟨225338505270422470890588173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600902680721126589041568461 225338505270422470890588173)
            ·
              refine ⟨84501939476408426583970565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225338505270422470890588173 84501939476408426583970565)
              ·
                refine ⟨15844113651826579984494481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84501939476408426583970565 15844113651826579984494481)
                ·
                  refine ⟨11883085238869934988370861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15844113651826579984494481 11883085238869934988370861)
                  ·
                    refine ⟨4456156964576225620639073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11883085238869934988370861 4456156964576225620639073)
                    ·
                      refine ⟨3342117723432169215479305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456156964576225620639073 3342117723432169215479305)
                      ·
                        rfl

theorem cell23_6508751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3, 2].length) (baseStart_6508751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508751 prefixEnd_6508751 := by exact prefixLift 6508751
  have htrace : WordTrace (prefixWord ++ tailWord_6508751) baseStart_6508751 baseEnd_6508751 := by
    simpa [prefixWord, tailWord_6508751, baseEnd_6508751] using wordTrace_append hprefix tailTrace_6508751
  have hstable : (prefixWord ++ tailWord_6508751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508751).length < 2 ^ (prefixWord ++ tailWord_6508751).sum := by decide
  have hdescent : baseEnd_6508751 < baseStart_6508751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508798 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_6508798 : Nat := 118140960795 + 6508798 * 2 ^ 59
def prefixEnd_6508798 : Nat := 4983230072969 + 3 ^ 40 * 6508798 * 2
def baseEnd_6508798 : Nat := 3342141857022930531591589

theorem tailTrace_6508798 : CollatzResearch.WordTrace tailWord_6508798 prefixEnd_6508798 3342141857022930531591589 := by
  unfold tailWord_6508798
  simp only [CollatzResearch.WordTrace]
  refine ⟨29674420734217991880422881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158263577249162623362255365 29674420734217991880422881)
  ·
    refine ⟨22255815550663493910317161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29674420734217991880422881 22255815550663493910317161)
    ·
      refine ⟨16691861662997620432737871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22255815550663493910317161 16691861662997620432737871)
      ·
        refine ⟨25037792494496430649106807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16691861662997620432737871 25037792494496430649106807)
        ·
          refine ⟨37556688741744645973660211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25037792494496430649106807 37556688741744645973660211)
          ·
            refine ⟨56335033112616968960490317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37556688741744645973660211 56335033112616968960490317)
            ·
              refine ⟨21125637417231363360183869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56335033112616968960490317 21125637417231363360183869)
              ·
                refine ⟨7922114031461761260068951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21125637417231363360183869 7922114031461761260068951)
                ·
                  refine ⟨11883171047192641890103427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7922114031461761260068951 11883171047192641890103427)
                  ·
                    refine ⟨17824756570788962835155141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11883171047192641890103427 17824756570788962835155141)
                    ·
                      refine ⟨3342141857022930531591589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17824756570788962835155141 3342141857022930531591589)
                      ·
                        rfl

theorem cell23_6508798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_6508798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508798 prefixEnd_6508798 := by exact prefixLift 6508798
  have htrace : WordTrace (prefixWord ++ tailWord_6508798) baseStart_6508798 baseEnd_6508798 := by
    simpa [prefixWord, tailWord_6508798, baseEnd_6508798] using wordTrace_append hprefix tailTrace_6508798
  have hstable : (prefixWord ++ tailWord_6508798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508798).length < 2 ^ (prefixWord ++ tailWord_6508798).sum := by decide
  have hdescent : baseEnd_6508798 < baseStart_6508798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508808 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 2, 4]
def baseStart_6508808 : Nat := 118140960795 + 6508808 * 2 ^ 59
def prefixEnd_6508808 : Nat := 4983230072969 + 3 ^ 40 * 6508808 * 2
def baseEnd_6508808 : Nat := 1114048997276491830822181

theorem tailTrace_6508808 : CollatzResearch.WordTrace tailWord_6508808 prefixEnd_6508808 1114048997276491830822181 := by
  unfold tailWord_6508808
  simp only [CollatzResearch.WordTrace]
  refine ⟨118697865301853853375623539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158263820402471804500831385 118697865301853853375623539)
  ·
    refine ⟨178046797952780780063435309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118697865301853853375623539 178046797952780780063435309)
    ·
      refine ⟨66767549232292792523788241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178046797952780780063435309 66767549232292792523788241)
      ·
        refine ⟨50075661924219594392841181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66767549232292792523788241 50075661924219594392841181)
        ·
          refine ⟨18778373221582347897315443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50075661924219594392841181 18778373221582347897315443)
          ·
            refine ⟨28167559832373521845973165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18778373221582347897315443 28167559832373521845973165)
            ·
              refine ⟨10562834937140070692239937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28167559832373521845973165 10562834937140070692239937)
              ·
                refine ⟨7922126202855053019179953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10562834937140070692239937 7922126202855053019179953)
                ·
                  refine ⟨5941594652141289764384965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7922126202855053019179953 5941594652141289764384965)
                  ·
                    refine ⟨1114048997276491830822181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5941594652141289764384965 1114048997276491830822181)
                    ·
                      rfl

theorem cell23_6508808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_6508808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508808 prefixEnd_6508808 := by exact prefixLift 6508808
  have htrace : WordTrace (prefixWord ++ tailWord_6508808) baseStart_6508808 baseEnd_6508808 := by
    simpa [prefixWord, tailWord_6508808, baseEnd_6508808] using wordTrace_append hprefix tailTrace_6508808
  have hstable : (prefixWord ++ tailWord_6508808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508808).length < 2 ^ (prefixWord ++ tailWord_6508808).sum := by decide
  have hdescent : baseEnd_6508808 < baseStart_6508808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508844 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_6508844 : Nat := 118140960795 + 6508844 * 2 ^ 59
def prefixEnd_6508844 : Nat := 4983230072969 + 3 ^ 40 * 6508844 * 2
def baseEnd_6508844 : Nat := 3342165477133037351616377

theorem tailTrace_6508844 : CollatzResearch.WordTrace tailWord_6508844 prefixEnd_6508844 3342165477133037351616377 := by
  unfold tailWord_6508844
  simp only [CollatzResearch.WordTrace]
  refine ⟨118698521815788642449778793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158264695754384856599705057 118698521815788642449778793)
  ·
    refine ⟨89023891361841481837334095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118698521815788642449778793 89023891361841481837334095)
    ·
      refine ⟨133535837042762222756001143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89023891361841481837334095 133535837042762222756001143)
      ·
        refine ⟨200303755564143334134001715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133535837042762222756001143 200303755564143334134001715)
        ·
          refine ⟨300455633346215001201002573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200303755564143334134001715 300455633346215001201002573)
          ·
            refine ⟨112670862504830625450375965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300455633346215001201002573 112670862504830625450375965)
            ·
              refine ⟨42251573439311484543890987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112670862504830625450375965 42251573439311484543890987)
              ·
                refine ⟨63377360158967226815836481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42251573439311484543890987 63377360158967226815836481)
                ·
                  refine ⟨47533020119225420111877361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63377360158967226815836481 47533020119225420111877361)
                  ·
                    refine ⟨35649765089419065083908021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47533020119225420111877361 35649765089419065083908021)
                    ·
                      refine ⟨3342165477133037351616377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35649765089419065083908021 3342165477133037351616377)
                      ·
                        rfl

theorem cell23_6508844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_6508844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508844 prefixEnd_6508844 := by exact prefixLift 6508844
  have htrace : WordTrace (prefixWord ++ tailWord_6508844) baseStart_6508844 baseEnd_6508844 := by
    simpa [prefixWord, tailWord_6508844, baseEnd_6508844] using wordTrace_append hprefix tailTrace_6508844
  have hstable : (prefixWord ++ tailWord_6508844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508844).length < 2 ^ (prefixWord ++ tailWord_6508844).sum := by decide
  have hdescent : baseEnd_6508844 < baseStart_6508844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508849 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 1, 2, 2]
def baseStart_6508849 : Nat := 118140960795 + 6508849 * 2 ^ 59
def prefixEnd_6508849 : Nat := 4983230072969 + 3 ^ 40 * 6508849 * 2
def baseEnd_6508849 : Nat := 3342168044536309832053855

theorem tailTrace_6508849 : CollatzResearch.WordTrace tailWord_6508849 prefixEnd_6508849 3342168044536309832053855 := by
  unfold tailWord_6508849
  simp only [CollatzResearch.WordTrace]
  refine ⟨237397225996559170753489601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158264817331039447168993067 237397225996559170753489601)
  ·
    refine ⟨178047919497419378065117201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237397225996559170753489601 178047919497419378065117201)
    ·
      refine ⟨133535939623064533548837901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178047919497419378065117201 133535939623064533548837901)
      ·
        refine ⟨50075977358649200080814213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133535939623064533548837901 50075977358649200080814213)
        ·
          refine ⟨9389245754746725015152665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50075977358649200080814213 9389245754746725015152665)
          ·
            refine ⟨7041934316060043761364499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9389245754746725015152665 7041934316060043761364499)
            ·
              refine ⟨10562901474090065642046749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7041934316060043761364499 10562901474090065642046749)
              ·
                refine ⟨3961088052783774615767531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10562901474090065642046749 3961088052783774615767531)
                ·
                  refine ⟨5941632079175661923651297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961088052783774615767531 5941632079175661923651297)
                  ·
                    refine ⟨4456224059381746442738473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941632079175661923651297 4456224059381746442738473)
                    ·
                      refine ⟨3342168044536309832053855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456224059381746442738473 3342168044536309832053855)
                      ·
                        rfl

theorem cell23_6508849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_6508849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508849 prefixEnd_6508849 := by exact prefixLift 6508849
  have htrace : WordTrace (prefixWord ++ tailWord_6508849) baseStart_6508849 baseEnd_6508849 := by
    simpa [prefixWord, tailWord_6508849, baseEnd_6508849] using wordTrace_append hprefix tailTrace_6508849
  have hstable : (prefixWord ++ tailWord_6508849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508849).length < 2 ^ (prefixWord ++ tailWord_6508849).sum := by decide
  have hdescent : baseEnd_6508849 < baseStart_6508849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508864 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 2, 6]
def baseStart_6508864 : Nat := 118140960795 + 6508864 * 2 ^ 59
def prefixEnd_6508864 : Nat := 4983230072969 + 3 ^ 40 * 6508864 * 2
def baseEnd_6508864 : Nat := 1114058582248709091122095

theorem tailTrace_6508864 : CollatzResearch.WordTrace tailWord_6508864 prefixEnd_6508864 1114058582248709091122095 := by
  unfold tailWord_6508864
  simp only [CollatzResearch.WordTrace]
  refine ⟨118698886545752414157642823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158265182061003218876857097 118698886545752414157642823)
  ·
    refine ⟨178048329818628621236464235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118698886545752414157642823 178048329818628621236464235)
    ·
      refine ⟨267072494727942931854696353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178048329818628621236464235 267072494727942931854696353)
      ·
        refine ⟨200304371045957198891022265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267072494727942931854696353 200304371045957198891022265)
        ·
          refine ⟨150228278284467899168266699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200304371045957198891022265 150228278284467899168266699)
          ·
            refine ⟨225342417426701848752400049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150228278284467899168266699 225342417426701848752400049)
            ·
              refine ⟨169006813070026386564300037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225342417426701848752400049 169006813070026386564300037)
              ·
                refine ⟨31688777450629947480806257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169006813070026386564300037 31688777450629947480806257)
                ·
                  refine ⟨23766583087972460610604693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31688777450629947480806257 23766583087972460610604693)
                  ·
                    refine ⟨1114058582248709091122095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23766583087972460610604693 1114058582248709091122095)
                    ·
                      rfl

theorem cell23_6508864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_6508864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508864 prefixEnd_6508864 := by exact prefixLift 6508864
  have htrace : WordTrace (prefixWord ++ tailWord_6508864) baseStart_6508864 baseEnd_6508864 := by
    simpa [prefixWord, tailWord_6508864, baseEnd_6508864] using wordTrace_append hprefix tailTrace_6508864
  have hstable : (prefixWord ++ tailWord_6508864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508864).length < 2 ^ (prefixWord ++ tailWord_6508864).sum := by decide
  have hdescent : baseEnd_6508864 < baseStart_6508864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508888 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 6, 2, 2]
def baseStart_6508888 : Nat := 118140960795 + 6508888 * 2 ^ 59
def prefixEnd_6508888 : Nat := 4983230072969 + 3 ^ 40 * 6508888 * 2
def baseEnd_6508888 : Nat := 3342188070281835179466175

theorem tailTrace_6508888 : CollatzResearch.WordTrace tailWord_6508888 prefixEnd_6508888 3342188070281835179466175 := by
  unfold tailWord_6508888
  simp only [CollatzResearch.WordTrace]
  refine ⟨118699324221708940207079659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158265765628945253609439545 118699324221708940207079659)
  ·
    refine ⟨178048986332563410310619489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118699324221708940207079659 178048986332563410310619489)
    ·
      refine ⟨133536739749422557732964617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178048986332563410310619489 133536739749422557732964617)
      ·
        refine ⟨100152554812066918299723463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133536739749422557732964617 100152554812066918299723463)
        ·
          refine ⟨150228832218100377449585195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100152554812066918299723463 150228832218100377449585195)
          ·
            refine ⟨225343248327150566174377793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150228832218100377449585195 225343248327150566174377793)
            ·
              refine ⟨169007436245362924630783345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225343248327150566174377793 169007436245362924630783345)
              ·
                refine ⟨126755577184022193473087509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169007436245362924630783345 126755577184022193473087509)
                ·
                  refine ⟨5941667680501040319050977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126755577184022193473087509 5941667680501040319050977)
                  ·
                    refine ⟨4456250760375780239288233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5941667680501040319050977 4456250760375780239288233)
                    ·
                      refine ⟨3342188070281835179466175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456250760375780239288233 3342188070281835179466175)
                      ·
                        rfl

theorem cell23_6508888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_6508888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508888 prefixEnd_6508888 := by exact prefixLift 6508888
  have htrace : WordTrace (prefixWord ++ tailWord_6508888) baseStart_6508888 baseEnd_6508888 := by
    simpa [prefixWord, tailWord_6508888, baseEnd_6508888] using wordTrace_append hprefix tailTrace_6508888
  have hstable : (prefixWord ++ tailWord_6508888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508888).length < 2 ^ (prefixWord ++ tailWord_6508888).sum := by decide
  have hdescent : baseEnd_6508888 < baseStart_6508888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508892 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6508892 : Nat := 118140960795 + 6508892 * 2 ^ 59
def prefixEnd_6508892 : Nat := 4983230072969 + 3 ^ 40 * 6508892 * 2
def baseEnd_6508892 : Nat := 3342190124204453163816157

theorem tailTrace_6508892 : CollatzResearch.WordTrace tailWord_6508892 prefixEnd_6508892 3342190124204453163816157 := by
  unfold tailWord_6508892
  simp only [CollatzResearch.WordTrace]
  refine ⟨118699397167701694548652465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158265862890268926064869953 118699397167701694548652465)
  ·
    refine ⟨89024547875776270911489349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118699397167701694548652465 89024547875776270911489349)
    ·
      refine ⟨16692102726708050795904253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89024547875776270911489349 16692102726708050795904253)
      ·
        refine ⟨6259538522515519048464095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16692102726708050795904253 6259538522515519048464095)
        ·
          refine ⟨9389307783773278572696143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6259538522515519048464095 9389307783773278572696143)
          ·
            refine ⟨14083961675659917859044215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9389307783773278572696143 14083961675659917859044215)
            ·
              refine ⟨21125942513489876788566323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14083961675659917859044215 21125942513489876788566323)
              ·
                refine ⟨31688913770234815182849485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21125942513489876788566323 31688913770234815182849485)
                ·
                  refine ⟨11883342663838055693568557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31688913770234815182849485 11883342663838055693568557)
                  ·
                    refine ⟨4456253498939270885088209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11883342663838055693568557 4456253498939270885088209)
                    ·
                      refine ⟨3342190124204453163816157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456253498939270885088209 3342190124204453163816157)
                      ·
                        rfl

theorem cell23_6508892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6508892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508892 prefixEnd_6508892 := by exact prefixLift 6508892
  have htrace : WordTrace (prefixWord ++ tailWord_6508892) baseStart_6508892 baseEnd_6508892 := by
    simpa [prefixWord, tailWord_6508892, baseEnd_6508892] using wordTrace_append hprefix tailTrace_6508892
  have hstable : (prefixWord ++ tailWord_6508892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508892).length < 2 ^ (prefixWord ++ tailWord_6508892).sum := by decide
  have hdescent : baseEnd_6508892 < baseStart_6508892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508921 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_6508921 : Nat := 118140960795 + 6508921 * 2 ^ 59
def prefixEnd_6508921 : Nat := 4983230072969 + 3 ^ 40 * 6508921 * 2
def baseEnd_6508921 : Nat := 3342205015143433550353523

theorem tailTrace_6508921 : CollatzResearch.WordTrace tailWord_6508921 prefixEnd_6508921 3342205015143433550353523 := by
  unfold tailWord_6508921
  simp only [CollatzResearch.WordTrace]
  refine ⟨237399852052298327050110617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158266568034865551366740411 237399852052298327050110617)
  ·
    refine ⟨178049889039223745287582963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237399852052298327050110617 178049889039223745287582963)
    ·
      refine ⟨267074833558835617931374445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178049889039223745287582963 267074833558835617931374445)
      ·
        refine ⟨100153062584563356724265417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267074833558835617931374445 100153062584563356724265417)
        ·
          refine ⟨75114796938422517543199063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100153062584563356724265417 75114796938422517543199063)
          ·
            refine ⟨112672195407633776314798595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75114796938422517543199063 112672195407633776314798595)
            ·
              refine ⟨169008293111450664472197893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112672195407633776314798595 169008293111450664472197893)
              ·
                refine ⟨31689054958396999588537105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169008293111450664472197893 31689054958396999588537105)
                ·
                  refine ⟨23766791218797749691402829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31689054958396999588537105 23766791218797749691402829)
                  ·
                    refine ⟨8912546707049156134276061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23766791218797749691402829 8912546707049156134276061)
                    ·
                      refine ⟨3342205015143433550353523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8912546707049156134276061 3342205015143433550353523)
                      ·
                        rfl

theorem cell23_6508921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_6508921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508921 prefixEnd_6508921 := by exact prefixLift 6508921
  have htrace : WordTrace (prefixWord ++ tailWord_6508921) baseStart_6508921 baseEnd_6508921 := by
    simpa [prefixWord, tailWord_6508921, baseEnd_6508921] using wordTrace_append hprefix tailTrace_6508921
  have hstable : (prefixWord ++ tailWord_6508921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508921).length < 2 ^ (prefixWord ++ tailWord_6508921).sum := by decide
  have hdescent : baseEnd_6508921 < baseStart_6508921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6508978 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_6508978 : Nat := 118140960795 + 6508978 * 2 ^ 59
def prefixEnd_6508978 : Nat := 4983230072969 + 3 ^ 40 * 6508978 * 2
def baseEnd_6508978 : Nat := 3342234283540739827340761

theorem tailTrace_6508978 : CollatzResearch.WordTrace tailWord_6508978 prefixEnd_6508978 3342234283540739827340761 := by
  unfold tailWord_6508978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59350482753272956446233897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158267954008727883856623725 59350482753272956446233897)
  ·
    refine ⟨44512862064954717334675423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59350482753272956446233897 44512862064954717334675423)
    ·
      refine ⟨66769293097432076002013135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44512862064954717334675423 66769293097432076002013135)
      ·
        refine ⟨100153939646148114003019703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66769293097432076002013135 100153939646148114003019703)
        ·
          refine ⟨150230909469222171004529555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100153939646148114003019703 150230909469222171004529555)
          ·
            refine ⟨225346364203833256506794333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150230909469222171004529555 225346364203833256506794333)
            ·
              refine ⟨84504886576437471190047875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225346364203833256506794333 84504886576437471190047875)
              ·
                refine ⟨126757329864656206785071813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84504886576437471190047875 126757329864656206785071813)
                ·
                  refine ⟨23766999349623038772200965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126757329864656206785071813 23766999349623038772200965)
                  ·
                    refine ⟨4456312378054319769787681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23766999349623038772200965 4456312378054319769787681)
                    ·
                      refine ⟨3342234283540739827340761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456312378054319769787681 3342234283540739827340761)
                      ·
                        rfl

theorem cell23_6508978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_6508978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6508978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6508978 prefixEnd_6508978 := by exact prefixLift 6508978
  have htrace : WordTrace (prefixWord ++ tailWord_6508978) baseStart_6508978 baseEnd_6508978 := by
    simpa [prefixWord, tailWord_6508978, baseEnd_6508978] using wordTrace_append hprefix tailTrace_6508978
  have hstable : (prefixWord ++ tailWord_6508978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6508978).length < 2 ^ (prefixWord ++ tailWord_6508978).sum := by decide
  have hdescent : baseEnd_6508978 < baseStart_6508978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6508978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509001 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 6]
def baseStart_6509001 : Nat := 118140960795 + 6509001 * 2 ^ 59
def prefixEnd_6509001 : Nat := 4983230072969 + 3 ^ 40 * 6509001 * 2
def baseEnd_6509001 : Nat := 371360677066199248594795

theorem tailTrace_6509001 : CollatzResearch.WordTrace tailWord_6509001 prefixEnd_6509001 371360677066199248594795 := by
  unfold tailWord_6509001
  simp only [CollatzResearch.WordTrace]
  refine ⟨237402769892008500713022857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158268513261339000475348571 237402769892008500713022857)
  ·
    refine ⟨178052077419006375534767143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237402769892008500713022857 178052077419006375534767143)
    ·
      refine ⟨267078116128509563302150715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178052077419006375534767143 267078116128509563302150715)
      ·
        refine ⟨400617174192764344953226073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267078116128509563302150715 400617174192764344953226073)
        ·
          refine ⟨300462880644573258714919555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400617174192764344953226073 300462880644573258714919555)
          ·
            refine ⟨450694320966859888072379333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300462880644573258714919555 450694320966859888072379333)
            ·
              refine ⟨84505185181286229013571125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450694320966859888072379333 84505185181286229013571125)
              ·
                refine ⟨7922361110745583970022293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84505185181286229013571125 7922361110745583970022293)
                ·
                  refine ⟨371360677066199248594795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7922361110745583970022293 371360677066199248594795)
                  ·
                    rfl

theorem cell23_6509001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_6509001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509001 prefixEnd_6509001 := by exact prefixLift 6509001
  have htrace : WordTrace (prefixWord ++ tailWord_6509001) baseStart_6509001 baseEnd_6509001 := by
    simpa [prefixWord, tailWord_6509001, baseEnd_6509001] using wordTrace_append hprefix tailTrace_6509001
  have hstable : (prefixWord ++ tailWord_6509001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509001).length < 2 ^ (prefixWord ++ tailWord_6509001).sum := by decide
  have hdescent : baseEnd_6509001 < baseStart_6509001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509071 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_6509071 : Nat := 118140960795 + 6509071 * 2 ^ 59
def prefixEnd_6509071 : Nat := 4983230072969 + 3 ^ 40 * 6509071 * 2
def baseEnd_6509071 : Nat := 3342282037241607963477833

theorem tailTrace_6509071 : CollatzResearch.WordTrace tailWord_6509071 prefixEnd_6509071 3342282037241607963477833 := by
  unfold tailWord_6509071
  simp only [CollatzResearch.WordTrace]
  refine ⟨237405323001754902668071067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158270215334503268445380711 237405323001754902668071067)
  ·
    refine ⟨356107984502632354002106601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237405323001754902668071067 356107984502632354002106601)
    ·
      refine ⟨267080988376974265501579951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356107984502632354002106601 267080988376974265501579951)
      ·
        refine ⟨400621482565461398252369927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267080988376974265501579951 400621482565461398252369927)
        ·
          refine ⟨600932223848192097378554891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400621482565461398252369927 600932223848192097378554891)
          ·
            refine ⟨901398335772288146067832337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600932223848192097378554891 901398335772288146067832337)
            ·
              refine ⟨676048751829216109550874253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901398335772288146067832337 676048751829216109550874253)
              ·
                refine ⟨253518281935956041081577845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676048751829216109550874253 253518281935956041081577845)
                ·
                  refine ⟨23767338931495878851397923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253518281935956041081577845 23767338931495878851397923)
                  ·
                    refine ⟨35651008397243818277096885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23767338931495878851397923 35651008397243818277096885)
                    ·
                      refine ⟨3342282037241607963477833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35651008397243818277096885 3342282037241607963477833)
                      ·
                        rfl

theorem cell23_6509071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_6509071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509071 prefixEnd_6509071 := by exact prefixLift 6509071
  have htrace : WordTrace (prefixWord ++ tailWord_6509071) baseStart_6509071 baseEnd_6509071 := by
    simpa [prefixWord, tailWord_6509071, baseEnd_6509071] using wordTrace_append hprefix tailTrace_6509071
  have hstable : (prefixWord ++ tailWord_6509071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509071).length < 2 ^ (prefixWord ++ tailWord_6509071).sum := by decide
  have hdescent : baseEnd_6509071 < baseStart_6509071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509091 : List Nat := [1, 1, 1, 4, 4, 12]
def baseStart_6509091 : Nat := 118140960795 + 6509091 * 2 ^ 59
def prefixEnd_6509091 : Nat := 4983230072969 + 3 ^ 40 * 6509091 * 2
def baseEnd_6509091 : Nat := 13754289328620155906287

theorem tailTrace_6509091 : CollatzResearch.WordTrace tailWord_6509091 prefixEnd_6509091 13754289328620155906287 := by
  unfold tailWord_6509091
  simp only [CollatzResearch.WordTrace]
  refine ⟨237406052461682446083799127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158270701641121630722532751 237406052461682446083799127)
  ·
    refine ⟨356109078692523669125698691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237406052461682446083799127 356109078692523669125698691)
    ·
      refine ⟨534163618038785503688548037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356109078692523669125698691 534163618038785503688548037)
      ·
        refine ⟨100155678382272281941602757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534163618038785503688548037 100155678382272281941602757)
        ·
          refine ⟨18779189696676052864050517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100155678382272281941602757 18779189696676052864050517)
          ·
            refine ⟨13754289328620155906287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18779189696676052864050517 13754289328620155906287)
            ·
              rfl

theorem cell23_6509091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 12].length) (baseStart_6509091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509091 prefixEnd_6509091 := by exact prefixLift 6509091
  have htrace : WordTrace (prefixWord ++ tailWord_6509091) baseStart_6509091 baseEnd_6509091 := by
    simpa [prefixWord, tailWord_6509091, baseEnd_6509091] using wordTrace_append hprefix tailTrace_6509091
  have hstable : (prefixWord ++ tailWord_6509091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509091).length < 2 ^ (prefixWord ++ tailWord_6509091).sum := by decide
  have hdescent : baseEnd_6509091 < baseStart_6509091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509096 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6509096 : Nat := 118140960795 + 6509096 * 2 ^ 59
def prefixEnd_6509096 : Nat := 4983230072969 + 3 ^ 40 * 6509096 * 2
def baseEnd_6509096 : Nat := 3342294874257970365665219

theorem tailTrace_6509096 : CollatzResearch.WordTrace tailWord_6509096 prefixEnd_6509096 3342294874257970365665219 := by
  unfold tailWord_6509096
  simp only [CollatzResearch.WordTrace]
  refine ⟨118703117413332165968865571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158270823217776221291820761 118703117413332165968865571)
  ·
    refine ⟨178054676119998248953298357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118703117413332165968865571 178054676119998248953298357)
    ·
      refine ⟨16692625886249835839371721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178054676119998248953298357 16692625886249835839371721)
      ·
        refine ⟨12519469414687376879528791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16692625886249835839371721 12519469414687376879528791)
        ·
          refine ⟨18779204122031065319293187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12519469414687376879528791 18779204122031065319293187)
          ·
            refine ⟨28168806183046597978939781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18779204122031065319293187 28168806183046597978939781)
            ·
              refine ⟨5281651159321237121051209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28168806183046597978939781 5281651159321237121051209)
              ·
                refine ⟨3961238369490927840788407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5281651159321237121051209 3961238369490927840788407)
                ·
                  refine ⟨5941857554236391761182611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961238369490927840788407 5941857554236391761182611)
                  ·
                    refine ⟨8912786331354587641773917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5941857554236391761182611 8912786331354587641773917)
                    ·
                      refine ⟨3342294874257970365665219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8912786331354587641773917 3342294874257970365665219)
                      ·
                        rfl

theorem cell23_6509096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6509096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509096 prefixEnd_6509096 := by exact prefixLift 6509096
  have htrace : WordTrace (prefixWord ++ tailWord_6509096) baseStart_6509096 baseEnd_6509096 := by
    simpa [prefixWord, tailWord_6509096, baseEnd_6509096] using wordTrace_append hprefix tailTrace_6509096
  have hstable : (prefixWord ++ tailWord_6509096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509096).length < 2 ^ (prefixWord ++ tailWord_6509096).sum := by decide
  have hdescent : baseEnd_6509096 < baseStart_6509096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509152 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 2, 1, 3]
def baseStart_6509152 : Nat := 118140960795 + 6509152 * 2 ^ 59
def prefixEnd_6509152 : Nat := 4983230072969 + 3 ^ 40 * 6509152 * 2
def baseEnd_6509152 : Nat := 3342323629174622146564961

theorem tailTrace_6509152 : CollatzResearch.WordTrace tailWord_6509152 prefixEnd_6509152 3342323629174622146564961 := by
  unfold tailWord_6509152
  simp only [CollatzResearch.WordTrace]
  refine ⟨118704138657230726750884855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158272184876307635667846473 118704138657230726750884855)
  ·
    refine ⟨178056207985846090126327283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118704138657230726750884855 178056207985846090126327283)
    ·
      refine ⟨267084311978769135189490925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178056207985846090126327283 267084311978769135189490925)
      ·
        refine ⟨100156616992038425696059097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267084311978769135189490925 100156616992038425696059097)
        ·
          refine ⟨75117462744028819272044323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100156616992038425696059097 75117462744028819272044323)
          ·
            refine ⟨112676194116043228908066485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75117462744028819272044323 112676194116043228908066485)
            ·
              refine ⟨10563393198379052710131233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112676194116043228908066485 10563393198379052710131233)
              ·
                refine ⟨7922544898784289532598425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10563393198379052710131233 7922544898784289532598425)
                ·
                  refine ⟨5941908674088217149448819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7922544898784289532598425 5941908674088217149448819)
                  ·
                    refine ⟨8912863011132325724173229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5941908674088217149448819 8912863011132325724173229)
                    ·
                      refine ⟨3342323629174622146564961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8912863011132325724173229 3342323629174622146564961)
                      ·
                        rfl

theorem cell23_6509152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_6509152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509152 prefixEnd_6509152 := by exact prefixLift 6509152
  have htrace : WordTrace (prefixWord ++ tailWord_6509152) baseStart_6509152 baseEnd_6509152 := by
    simpa [prefixWord, tailWord_6509152, baseEnd_6509152] using wordTrace_append hprefix tailTrace_6509152
  have hstable : (prefixWord ++ tailWord_6509152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509152).length < 2 ^ (prefixWord ++ tailWord_6509152).sum := by decide
  have hdescent : baseEnd_6509152 < baseStart_6509152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509178 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_6509178 : Nat := 118140960795 + 6509178 * 2 ^ 59
def prefixEnd_6509178 : Nat := 4983230072969 + 3 ^ 40 * 6509178 * 2
def baseEnd_6509178 : Nat := 3342336979671639044839841

theorem tailTrace_6509178 : CollatzResearch.WordTrace tailWord_6509178 prefixEnd_6509178 3342336979671639044839841 := by
  unfold tailWord_6509178
  simp only [CollatzResearch.WordTrace]
  refine ⟨59352306403091814985554047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158272817074911506628144125 59352306403091814985554047)
  ·
    refine ⟨89028459604637722478331071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59352306403091814985554047 89028459604637722478331071)
    ·
      refine ⟨133542689406956583717496607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89028459604637722478331071 133542689406956583717496607)
      ·
        refine ⟨200314034110434875576244911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133542689406956583717496607 200314034110434875576244911)
        ·
          refine ⟨300471051165652313364367367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200314034110434875576244911 300471051165652313364367367)
          ·
            refine ⟨450706576748478470046551051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300471051165652313364367367 450706576748478470046551051)
            ·
              refine ⟨676059865122717705069826577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450706576748478470046551051 676059865122717705069826577)
              ·
                refine ⟨507044898842038278802369933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676059865122717705069826577 507044898842038278802369933)
                ·
                  refine ⟨190141837065764354550888725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507044898842038278802369933 190141837065764354550888725)
                  ·
                    refine ⟨8912898612457704119572909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 190141837065764354550888725 8912898612457704119572909)
                    ·
                      refine ⟨3342336979671639044839841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8912898612457704119572909 3342336979671639044839841)
                      ·
                        rfl

theorem cell23_6509178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_6509178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509178 prefixEnd_6509178 := by exact prefixLift 6509178
  have htrace : WordTrace (prefixWord ++ tailWord_6509178) baseStart_6509178 baseEnd_6509178 := by
    simpa [prefixWord, tailWord_6509178, baseEnd_6509178] using wordTrace_append hprefix tailTrace_6509178
  have hstable : (prefixWord ++ tailWord_6509178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509178).length < 2 ^ (prefixWord ++ tailWord_6509178).sum := by decide
  have hdescent : baseEnd_6509178 < baseStart_6509178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509208 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6509208 : Nat := 118140960795 + 6509208 * 2 ^ 59
def prefixEnd_6509208 : Nat := 4983230072969 + 3 ^ 40 * 6509208 * 2
def baseEnd_6509208 : Nat := 3342352384091273927464703

theorem tailTrace_6509208 : CollatzResearch.WordTrace tailWord_6509208 prefixEnd_6509208 3342352384091273927464703 := by
  unfold tailWord_6509208
  simp only [CollatzResearch.WordTrace]
  refine ⟨118705159901129287532904139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158273546534839050043872185 118705159901129287532904139)
  ·
    refine ⟨178057739851693931299356209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118705159901129287532904139 178057739851693931299356209)
    ·
      refine ⟨133543304888770448474517157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178057739851693931299356209 133543304888770448474517157)
      ·
        refine ⟨25039369666644459088971967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133543304888770448474517157 25039369666644459088971967)
        ·
          refine ⟨37559054499966688633457951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25039369666644459088971967 37559054499966688633457951)
          ·
            refine ⟨56338581749950032950186927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37559054499966688633457951 56338581749950032950186927)
            ·
              refine ⟨84507872624925049425280391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56338581749950032950186927 84507872624925049425280391)
              ·
                refine ⟨126761808937387574137920587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84507872624925049425280391 126761808937387574137920587)
                ·
                  refine ⟨190142713406081361206880881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126761808937387574137920587 190142713406081361206880881)
                  ·
                    refine ⟨142607035054561020905160661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190142713406081361206880881 142607035054561020905160661)
                    ·
                      refine ⟨3342352384091273927464703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142607035054561020905160661 3342352384091273927464703)
                      ·
                        rfl

theorem cell23_6509208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6509208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509208 prefixEnd_6509208 := by exact prefixLift 6509208
  have htrace : WordTrace (prefixWord ++ tailWord_6509208) baseStart_6509208 baseEnd_6509208 := by
    simpa [prefixWord, tailWord_6509208, baseEnd_6509208] using wordTrace_append hprefix tailTrace_6509208
  have hstable : (prefixWord ++ tailWord_6509208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509208).length < 2 ^ (prefixWord ++ tailWord_6509208).sum := by decide
  have hdescent : baseEnd_6509208 < baseStart_6509208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509245 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_6509245 : Nat := 118140960795 + 6509245 * 2 ^ 59
def prefixEnd_6509245 : Nat := 4983230072969 + 3 ^ 40 * 6509245 * 2
def baseEnd_6509245 : Nat := 1114123794291830094234011

theorem tailTrace_6509245 : CollatzResearch.WordTrace tailWord_6509245 prefixEnd_6509245 1114123794291830094234011 := by
  unfold tailWord_6509245
  simp only [CollatzResearch.WordTrace]
  refine ⟨237411669303124530384905189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158274446202083020256603459 237411669303124530384905189)
  ·
    refine ⟨44514687994335849447169723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237411669303124530384905189 44514687994335849447169723)
    ·
      refine ⟨66772031991503774170754585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44514687994335849447169723 66772031991503774170754585)
      ·
        refine ⟨50079023993627830628065939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66772031991503774170754585 50079023993627830628065939)
        ·
          refine ⟨75118535990441745942098909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50079023993627830628065939 75118535990441745942098909)
          ·
            refine ⟨28169450996415654728287091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75118535990441745942098909 28169450996415654728287091)
            ·
              refine ⟨42254176494623482092430637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28169450996415654728287091 42254176494623482092430637)
              ·
                refine ⟨15845316185483805784661489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42254176494623482092430637 15845316185483805784661489)
                ·
                  refine ⟨11883987139112854338496117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15845316185483805784661489 11883987139112854338496117)
                  ·
                    refine ⟨1114123794291830094234011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11883987139112854338496117 1114123794291830094234011)
                    ·
                      rfl

theorem cell23_6509245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_6509245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509245 prefixEnd_6509245 := by exact prefixLift 6509245
  have htrace : WordTrace (prefixWord ++ tailWord_6509245) baseStart_6509245 baseEnd_6509245 := by
    simpa [prefixWord, tailWord_6509245, baseEnd_6509245] using wordTrace_append hprefix tailTrace_6509245
  have hstable : (prefixWord ++ tailWord_6509245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509245).length < 2 ^ (prefixWord ++ tailWord_6509245).sum := by decide
  have hdescent : baseEnd_6509245 < baseStart_6509245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509265 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_6509265 : Nat := 118140960795 + 6509265 * 2 ^ 59
def prefixEnd_6509265 : Nat := 4983230072969 + 3 ^ 40 * 6509265 * 2
def baseEnd_6509265 : Nat := 3342381652488580204451941

theorem tailTrace_6509265 : CollatzResearch.WordTrace tailWord_6509265 prefixEnd_6509265 3342381652488580204451941 := by
  unfold tailWord_6509265
  simp only [CollatzResearch.WordTrace]
  refine ⟨237412398763052073800633249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158274932508701382533755499 237412398763052073800633249)
  ·
    refine ⟨178059299072289055350474937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237412398763052073800633249 178059299072289055350474937)
    ·
      refine ⟨133544474304216791512856203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178059299072289055350474937 133544474304216791512856203)
      ·
        refine ⟨200316711456325187269284305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133544474304216791512856203 200316711456325187269284305)
        ·
          refine ⟨150237533592243890451963229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200316711456325187269284305 150237533592243890451963229)
          ·
            refine ⟨56339075097091458919486211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150237533592243890451963229 56339075097091458919486211)
            ·
              refine ⟨84508612645637188379229317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56339075097091458919486211 84508612645637188379229317)
              ·
                refine ⟨15845364871056972821105497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84508612645637188379229317 15845364871056972821105497)
                ·
                  refine ⟨11884023653292729615829123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15845364871056972821105497 11884023653292729615829123)
                  ·
                    refine ⟨17826035479939094423743685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11884023653292729615829123 17826035479939094423743685)
                    ·
                      refine ⟨3342381652488580204451941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17826035479939094423743685 3342381652488580204451941)
                      ·
                        rfl

theorem cell23_6509265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_6509265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509265 prefixEnd_6509265 := by exact prefixLift 6509265
  have htrace : WordTrace (prefixWord ++ tailWord_6509265) baseStart_6509265 baseEnd_6509265 := by
    simpa [prefixWord, tailWord_6509265, baseEnd_6509265] using wordTrace_append hprefix tailTrace_6509265
  have hstable : (prefixWord ++ tailWord_6509265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509265).length < 2 ^ (prefixWord ++ tailWord_6509265).sum := by decide
  have hdescent : baseEnd_6509265 < baseStart_6509265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509266 : List Nat := [3, 2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_6509266 : Nat := 118140960795 + 6509266 * 2 ^ 59
def prefixEnd_6509266 : Nat := 4983230072969 + 3 ^ 40 * 6509266 * 2
def baseEnd_6509266 : Nat := 371375796218803855615493

theorem tailTrace_6509266 : CollatzResearch.WordTrace tailWord_6509266 prefixEnd_6509266 371375796218803855615493 := by
  unfold tailWord_6509266
  simp only [CollatzResearch.WordTrace]
  refine ⟨59353108809012112742854913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158274956824032300647613101 59353108809012112742854913)
  ·
    refine ⟨44514831606759084557141185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59353108809012112742854913 44514831606759084557141185)
    ·
      refine ⟨33386123705069313417855889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44514831606759084557141185 33386123705069313417855889)
      ·
        refine ⟨25039592778801985063391917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33386123705069313417855889 25039592778801985063391917)
        ·
          refine ⟨9389847292050744398771969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25039592778801985063391917 9389847292050744398771969)
          ·
            refine ⟨7042385469038058299078977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9389847292050744398771969 7042385469038058299078977)
            ·
              refine ⟨5281789101778543724309233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7042385469038058299078977 5281789101778543724309233)
              ·
                refine ⟨3961341826333907793231925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5281789101778543724309233 3961341826333907793231925)
                ·
                  refine ⟨371375796218803855615493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3961341826333907793231925 371375796218803855615493)
                  ·
                    rfl

theorem cell23_6509266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_6509266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509266 prefixEnd_6509266 := by exact prefixLift 6509266
  have htrace : WordTrace (prefixWord ++ tailWord_6509266) baseStart_6509266 baseEnd_6509266 := by
    simpa [prefixWord, tailWord_6509266, baseEnd_6509266] using wordTrace_append hprefix tailTrace_6509266
  have hstable : (prefixWord ++ tailWord_6509266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509266).length < 2 ^ (prefixWord ++ tailWord_6509266).sum := by decide
  have hdescent : baseEnd_6509266 < baseStart_6509266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509302 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6509302 : Nat := 118140960795 + 6509302 * 2 ^ 59
def prefixEnd_6509302 : Nat := 4983230072969 + 3 ^ 40 * 6509302 * 2
def baseEnd_6509302 : Nat := 3342400651272796559689271

theorem tailTrace_6509302 : CollatzResearch.WordTrace tailWord_6509302 prefixEnd_6509302 3342400651272796559689271 := by
  unfold tailWord_6509302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838359266494876819983135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158275832175945352746486773 14838359266494876819983135)
  ·
    refine ⟨22257538899742315229974703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14838359266494876819983135 22257538899742315229974703)
    ·
      refine ⟨33386308349613472844962055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22257538899742315229974703 33386308349613472844962055)
      ·
        refine ⟨50079462524420209267443083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33386308349613472844962055 50079462524420209267443083)
        ·
          refine ⟨75119193786630313901164625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50079462524420209267443083 75119193786630313901164625)
          ·
            refine ⟨56339395339972735425873469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75119193786630313901164625 56339395339972735425873469)
            ·
              refine ⟨21127273252489775784702551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56339395339972735425873469 21127273252489775784702551)
              ·
                refine ⟨31690909878734663677053827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21127273252489775784702551 31690909878734663677053827)
                ·
                  refine ⟨47536364818101995515580741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31690909878734663677053827 47536364818101995515580741)
                  ·
                    refine ⟨8913068403394124159171389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47536364818101995515580741 8913068403394124159171389)
                    ·
                      refine ⟨3342400651272796559689271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8913068403394124159171389 3342400651272796559689271)
                      ·
                        rfl

theorem cell23_6509302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6509302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509302 prefixEnd_6509302 := by exact prefixLift 6509302
  have htrace : WordTrace (prefixWord ++ tailWord_6509302) baseStart_6509302 baseEnd_6509302 := by
    simpa [prefixWord, tailWord_6509302, baseEnd_6509302] using wordTrace_append hprefix tailTrace_6509302
  have hstable : (prefixWord ++ tailWord_6509302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509302).length < 2 ^ (prefixWord ++ tailWord_6509302).sum := by decide
  have hdescent : baseEnd_6509302 < baseStart_6509302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509309 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_6509309 : Nat := 118140960795 + 6509309 * 2 ^ 59
def prefixEnd_6509309 : Nat := 4983230072969 + 3 ^ 40 * 6509309 * 2
def baseEnd_6509309 : Nat := 1114134748545792677433913

theorem tailTrace_6509309 : CollatzResearch.WordTrace tailWord_6509309 prefixEnd_6509309 1114134748545792677433913 := by
  unfold tailWord_6509309
  simp only [CollatzResearch.WordTrace]
  refine ⟨237414003574892669315234981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158276002383261779543489987 237414003574892669315234981)
  ·
    refine ⟨44515125670292375496606559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237414003574892669315234981 44515125670292375496606559)
    ·
      refine ⟨66772688505438563244909839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44515125670292375496606559 66772688505438563244909839)
      ·
        refine ⟨100159032758157844867364759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66772688505438563244909839 100159032758157844867364759)
        ·
          refine ⟨150238549137236767301047139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100159032758157844867364759 150238549137236767301047139)
          ·
            refine ⟨225357823705855150951570709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150238549137236767301047139 225357823705855150951570709)
            ·
              refine ⟨10563647986211960200854877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225357823705855150951570709 10563647986211960200854877)
              ·
                refine ⟨3961367994829485075320579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10563647986211960200854877 3961367994829485075320579)
                ·
                  refine ⟨5942051992244227612980869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961367994829485075320579 5942051992244227612980869)
                  ·
                    refine ⟨1114134748545792677433913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5942051992244227612980869 1114134748545792677433913)
                    ·
                      rfl

theorem cell23_6509309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_6509309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509309 prefixEnd_6509309 := by exact prefixLift 6509309
  have htrace : WordTrace (prefixWord ++ tailWord_6509309) baseStart_6509309 baseEnd_6509309 := by
    simpa [prefixWord, tailWord_6509309, baseEnd_6509309] using wordTrace_append hprefix tailTrace_6509309
  have hstable : (prefixWord ++ tailWord_6509309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509309).length < 2 ^ (prefixWord ++ tailWord_6509309).sum := by decide
  have hdescent : baseEnd_6509309 < baseStart_6509309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509385 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_6509385 : Nat := 118140960795 + 6509385 * 2 ^ 59
def prefixEnd_6509385 : Nat := 4983230072969 + 3 ^ 40 * 6509385 * 2
def baseEnd_6509385 : Nat := 3342443270167119734951389

theorem tailTrace_6509385 : CollatzResearch.WordTrace tailWord_6509385 prefixEnd_6509385 3342443270167119734951389 := by
  unfold tailWord_6509385
  simp only [CollatzResearch.WordTrace]
  refine ⟨237416775522617334295001609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158277850348411556196667739 237416775522617334295001609)
  ·
    refine ⟨178062581641963000721251207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237416775522617334295001609 178062581641963000721251207)
    ·
      refine ⟨267093872462944501081876811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178062581641963000721251207 267093872462944501081876811)
      ·
        refine ⟨400640808694416751622815217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267093872462944501081876811 400640808694416751622815217)
        ·
          refine ⟨300480606520812563717111413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400640808694416751622815217 300480606520812563717111413)
          ·
            refine ⟨28170056861326177848479195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300480606520812563717111413 28170056861326177848479195)
            ·
              refine ⟨42255085291989266772718793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28170056861326177848479195 42255085291989266772718793)
              ·
                refine ⟨31691313968991950079539095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42255085291989266772718793 31691313968991950079539095)
                ·
                  refine ⟨47536970953487925119308643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31691313968991950079539095 47536970953487925119308643)
                  ·
                    refine ⟨71305456430231887678962965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47536970953487925119308643 71305456430231887678962965)
                    ·
                      refine ⟨3342443270167119734951389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71305456430231887678962965 3342443270167119734951389)
                      ·
                        rfl

theorem cell23_6509385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_6509385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509385 prefixEnd_6509385 := by exact prefixLift 6509385
  have htrace : WordTrace (prefixWord ++ tailWord_6509385) baseStart_6509385 baseEnd_6509385 := by
    simpa [prefixWord, tailWord_6509385, baseEnd_6509385] using wordTrace_append hprefix tailTrace_6509385
  have hstable : (prefixWord ++ tailWord_6509385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509385).length < 2 ^ (prefixWord ++ tailWord_6509385).sum := by decide
  have hdescent : baseEnd_6509385 < baseStart_6509385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509399 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 2, 4]
def baseStart_6509399 : Nat := 118140960795 + 6509399 * 2 ^ 59
def prefixEnd_6509399 : Nat := 4983230072969 + 3 ^ 40 * 6509399 * 2
def baseEnd_6509399 : Nat := 1114150152965427560058775

theorem tailTrace_6509399 : CollatzResearch.WordTrace tailWord_6509399 prefixEnd_6509399 1114150152965427560058775 := by
  unfold tailWord_6509399
  simp only [CollatzResearch.WordTrace]
  refine ⟨237417286144566614686011251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158278190763044409790674167 237417286144566614686011251)
  ·
    refine ⟨356125929216849922029016877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237417286144566614686011251 356125929216849922029016877)
    ·
      refine ⟨133547223456318720760881329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356125929216849922029016877 133547223456318720760881329)
      ·
        refine ⟨100160417592239040570660997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133547223456318720760881329 100160417592239040570660997)
        ·
          refine ⟨18780078298544820106998937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100160417592239040570660997 18780078298544820106998937)
          ·
            refine ⟨14085058723908615080249203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18780078298544820106998937 14085058723908615080249203)
            ·
              refine ⟨21127588085862922620373805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14085058723908615080249203 21127588085862922620373805)
              ·
                refine ⟨7922845532198595982640177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21127588085862922620373805 7922845532198595982640177)
                ·
                  refine ⟨5942134149148946986980133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7922845532198595982640177 5942134149148946986980133)
                  ·
                    refine ⟨1114150152965427560058775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5942134149148946986980133 1114150152965427560058775)
                    ·
                      rfl

theorem cell23_6509399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_6509399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509399 prefixEnd_6509399 := by exact prefixLift 6509399
  have htrace : WordTrace (prefixWord ++ tailWord_6509399) baseStart_6509399 baseEnd_6509399 := by
    simpa [prefixWord, tailWord_6509399, baseEnd_6509399] using wordTrace_append hprefix tailTrace_6509399
  have hstable : (prefixWord ++ tailWord_6509399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509399).length < 2 ^ (prefixWord ++ tailWord_6509399).sum := by decide
  have hdescent : baseEnd_6509399 < baseStart_6509399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509435 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5]
def baseStart_6509435 : Nat := 118140960795 + 6509435 * 2 ^ 59
def prefixEnd_6509435 : Nat := 4983230072969 + 3 ^ 40 * 6509435 * 2
def baseEnd_6509435 : Nat := 3342468944199844539326159

theorem tailTrace_6509435 : CollatzResearch.WordTrace tailWord_6509435 prefixEnd_6509435 3342468944199844539326159 := by
  unfold tailWord_6509435
  simp only [CollatzResearch.WordTrace]
  refine ⟨237418599172436192834321759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158279066114957461889547839 237418599172436192834321759)
  ·
    refine ⟨356127898758654289251482639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237418599172436192834321759 356127898758654289251482639)
    ·
      refine ⟨534191848137981433877223959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356127898758654289251482639 534191848137981433877223959)
      ·
        refine ⟨801287772206972150815835939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534191848137981433877223959 801287772206972150815835939)
        ·
          refine ⟨1201931658310458226223753909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801287772206972150815835939 1201931658310458226223753909)
          ·
            refine ⟨112681092966605458708476929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1201931658310458226223753909 112681092966605458708476929)
            ·
              refine ⟨84510819724954094031357697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112681092966605458708476929 84510819724954094031357697)
              ·
                refine ⟨63383114793715570523518273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84510819724954094031357697 63383114793715570523518273)
                ·
                  refine ⟨47537336095286677892638705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63383114793715570523518273 47537336095286677892638705)
                  ·
                    refine ⟨35653002071465008419479029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47537336095286677892638705 35653002071465008419479029)
                    ·
                      refine ⟨3342468944199844539326159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35653002071465008419479029 3342468944199844539326159)
                      ·
                        rfl

theorem cell23_6509435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_6509435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509435 prefixEnd_6509435 := by exact prefixLift 6509435
  have htrace : WordTrace (prefixWord ++ tailWord_6509435) baseStart_6509435 baseEnd_6509435 := by
    simpa [prefixWord, tailWord_6509435, baseEnd_6509435] using wordTrace_append hprefix tailTrace_6509435
  have hstable : (prefixWord ++ tailWord_6509435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509435).length < 2 ^ (prefixWord ++ tailWord_6509435).sum := by decide
  have hdescent : baseEnd_6509435 < baseStart_6509435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509439 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 3]
def baseStart_6509439 : Nat := 118140960795 + 6509439 * 2 ^ 59
def prefixEnd_6509439 : Nat := 4983230072969 + 3 ^ 40 * 6509439 * 2
def baseEnd_6509439 : Nat := 3342470998122462523676141

theorem tailTrace_6509439 : CollatzResearch.WordTrace tailWord_6509439 prefixEnd_6509439 3342470998122462523676141 := by
  unfold tailWord_6509439
  simp only [CollatzResearch.WordTrace]
  refine ⟨237418745064421701517467371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158279163376281134344978247 237418745064421701517467371)
  ·
    refine ⟨356128117596632552276201057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237418745064421701517467371 356128117596632552276201057)
    ·
      refine ⟨267096088197474414207150793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356128117596632552276201057 267096088197474414207150793)
      ·
        refine ⟨200322066148105810655363095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267096088197474414207150793 200322066148105810655363095)
        ·
          refine ⟨300483099222158715983044643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200322066148105810655363095 300483099222158715983044643)
          ·
            refine ⟨450724648833238073974566965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300483099222158715983044643 450724648833238073974566965)
            ·
              refine ⟨42255435828116069435115653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 450724648833238073974566965 42255435828116069435115653)
              ·
                refine ⟨7922894217771763019084185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42255435828116069435115653 7922894217771763019084185)
                ·
                  refine ⟨5942170663328822264313139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7922894217771763019084185 5942170663328822264313139)
                  ·
                    refine ⟨8913255994993233396469709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5942170663328822264313139 8913255994993233396469709)
                    ·
                      refine ⟨3342470998122462523676141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8913255994993233396469709 3342470998122462523676141)
                      ·
                        rfl

theorem cell23_6509439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_6509439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509439 prefixEnd_6509439 := by exact prefixLift 6509439
  have htrace : WordTrace (prefixWord ++ tailWord_6509439) baseStart_6509439 baseEnd_6509439 := by
    simpa [prefixWord, tailWord_6509439, baseEnd_6509439] using wordTrace_append hprefix tailTrace_6509439
  have hstable : (prefixWord ++ tailWord_6509439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509439).length < 2 ^ (prefixWord ++ tailWord_6509439).sum := by decide
  have hdescent : baseEnd_6509439 < baseStart_6509439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509449 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 3, 3, 2]
def baseStart_6509449 : Nat := 118140960795 + 6509449 * 2 ^ 59
def prefixEnd_6509449 : Nat := 4983230072969 + 3 ^ 40 * 6509449 * 2
def baseEnd_6509449 : Nat := 3342476132929007484551095

theorem tailTrace_6509449 : CollatzResearch.WordTrace tailWord_6509449 prefixEnd_6509449 3342476132929007484551095 := by
  unfold tailWord_6509449
  simp only [CollatzResearch.WordTrace]
  refine ⟨237419109794385473225331401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158279406529590315483554267 237419109794385473225331401)
  ·
    refine ⟨178064332345789104918998551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237419109794385473225331401 178064332345789104918998551)
    ·
      refine ⟨267096498518683657378497827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178064332345789104918998551 267096498518683657378497827)
      ·
        refine ⟨400644747778025486067746741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267096498518683657378497827 400644747778025486067746741)
        ·
          refine ⟨37560445104189889318851257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 400644747778025486067746741 37560445104189889318851257)
          ·
            refine ⟨28170333828142416989138443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37560445104189889318851257 28170333828142416989138443)
            ·
              refine ⟨42255500742213625483707665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28170333828142416989138443 42255500742213625483707665)
              ·
                refine ⟨31691625556660219112780749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42255500742213625483707665 31691625556660219112780749)
                ·
                  refine ⟨11884359583747582167292781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31691625556660219112780749 11884359583747582167292781)
                  ·
                    refine ⟨4456634843905343312734793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11884359583747582167292781 4456634843905343312734793)
                    ·
                      refine ⟨3342476132929007484551095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456634843905343312734793 3342476132929007484551095)
                      ·
                        rfl

theorem cell23_6509449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 3, 2].length) (baseStart_6509449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509449 prefixEnd_6509449 := by exact prefixLift 6509449
  have htrace : WordTrace (prefixWord ++ tailWord_6509449) baseStart_6509449 baseEnd_6509449 := by
    simpa [prefixWord, tailWord_6509449, baseEnd_6509449] using wordTrace_append hprefix tailTrace_6509449
  have hstable : (prefixWord ++ tailWord_6509449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509449).length < 2 ^ (prefixWord ++ tailWord_6509449).sum := by decide
  have hdescent : baseEnd_6509449 < baseStart_6509449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509496 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 4, 2, 2]
def baseStart_6509496 : Nat := 118140960795 + 6509496 * 2 ^ 59
def prefixEnd_6509496 : Nat := 4983230072969 + 3 ^ 40 * 6509496 * 2
def baseEnd_6509496 : Nat := 3342500266519768800663379

theorem tailTrace_6509496 : CollatzResearch.WordTrace tailWord_6509496 prefixEnd_6509496 3342500266519768800663379 := by
  unfold tailWord_6509496
  simp only [CollatzResearch.WordTrace]
  refine ⟨118710412012607600126146171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158280549350143466834861561 118710412012607600126146171)
  ·
    refine ⟨178065618018911400189219257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118710412012607600126146171 178065618018911400189219257)
    ·
      refine ⟨133549213514183550141914443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178065618018911400189219257 133549213514183550141914443)
      ·
        refine ⟨200323820271275325212871665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133549213514183550141914443 200323820271275325212871665)
        ·
          refine ⟨150242865203456493909653749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200323820271275325212871665 150242865203456493909653749)
          ·
            refine ⟨14085268612824046304030039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150242865203456493909653749 14085268612824046304030039)
            ·
              refine ⟨21127902919236069456045059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14085268612824046304030039 21127902919236069456045059)
              ·
                refine ⟨31691854378854104184067589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21127902919236069456045059 31691854378854104184067589)
                ·
                  refine ⟨5942222696035144534512673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31691854378854104184067589 5942222696035144534512673)
                  ·
                    refine ⟨4456667022026358400884505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5942222696035144534512673 4456667022026358400884505)
                    ·
                      refine ⟨3342500266519768800663379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456667022026358400884505 3342500266519768800663379)
                      ·
                        rfl

theorem cell23_6509496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_6509496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509496 prefixEnd_6509496 := by exact prefixLift 6509496
  have htrace : WordTrace (prefixWord ++ tailWord_6509496) baseStart_6509496 baseEnd_6509496 := by
    simpa [prefixWord, tailWord_6509496, baseEnd_6509496] using wordTrace_append hprefix tailTrace_6509496
  have hstable : (prefixWord ++ tailWord_6509496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509496).length < 2 ^ (prefixWord ++ tailWord_6509496).sum := by decide
  have hdescent : baseEnd_6509496 < baseStart_6509496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509612 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_6509612 : Nat := 118140960795 + 6509612 * 2 ^ 59
def prefixEnd_6509612 : Nat := 4983230072969 + 3 ^ 40 * 6509612 * 2
def baseEnd_6509612 : Nat := 3342559830275690346812845

theorem tailTrace_6509612 : CollatzResearch.WordTrace tailWord_6509612 prefixEnd_6509612 3342559830275690346812845 := by
  unfold tailWord_6509612
  simp only [CollatzResearch.WordTrace]
  refine ⟨118712527446397476031757545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158283369928529968042343393 118712527446397476031757545)
  ·
    refine ⟨89034395584798107023818159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118712527446397476031757545 89034395584798107023818159)
    ·
      refine ⟨133551593377197160535727239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89034395584798107023818159 133551593377197160535727239)
      ·
        refine ⟨200327390065795740803590859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133551593377197160535727239 200327390065795740803590859)
        ·
          refine ⟨300491085098693611205386289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200327390065795740803590859 300491085098693611205386289)
          ·
            refine ⟨225368313824020208404039717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300491085098693611205386289 225368313824020208404039717)
            ·
              refine ⟨42256558842003789075757447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225368313824020208404039717 42256558842003789075757447)
              ·
                refine ⟨63384838263005683613636171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42256558842003789075757447 63384838263005683613636171)
                ·
                  refine ⟨95077257394508525420454257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63384838263005683613636171 95077257394508525420454257)
                  ·
                    refine ⟨71307943045881394065340693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95077257394508525420454257 71307943045881394065340693)
                    ·
                      refine ⟨3342559830275690346812845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71307943045881394065340693 3342559830275690346812845)
                      ·
                        rfl

theorem cell23_6509612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_6509612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509612 prefixEnd_6509612 := by exact prefixLift 6509612
  have htrace : WordTrace (prefixWord ++ tailWord_6509612) baseStart_6509612 baseEnd_6509612 := by
    simpa [prefixWord, tailWord_6509612, baseEnd_6509612] using wordTrace_append hprefix tailTrace_6509612
  have hstable : (prefixWord ++ tailWord_6509612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509612).length < 2 ^ (prefixWord ++ tailWord_6509612).sum := by decide
  have hdescent : baseEnd_6509612 < baseStart_6509612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509632 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_6509632 : Nat := 118140960795 + 6509632 * 2 ^ 59
def prefixEnd_6509632 : Nat := 4983230072969 + 3 ^ 40 * 6509632 * 2
def baseEnd_6509632 : Nat := 3342570099888780268562753

theorem tailTrace_6509632 : CollatzResearch.WordTrace tailWord_6509632 prefixEnd_6509632 3342570099888780268562753 := by
  unfold tailWord_6509632
  simp only [CollatzResearch.WordTrace]
  refine ⟨118712892176361247739621575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158283856235148330319495433 118712892176361247739621575)
  ·
    refine ⟨178069338264541871609432363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118712892176361247739621575 178069338264541871609432363)
    ·
      refine ⟨267104007396812807414148545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178069338264541871609432363 267104007396812807414148545)
      ·
        refine ⟨200328005547609605560611409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267104007396812807414148545 200328005547609605560611409)
        ·
          refine ⟨150246004160707204170458557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200328005547609605560611409 150246004160707204170458557)
          ·
            refine ⟨56342251560265201563921959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150246004160707204170458557 56342251560265201563921959)
            ·
              refine ⟨84513377340397802345882939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56342251560265201563921959 84513377340397802345882939)
              ·
                refine ⟨126770066010596703518824409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84513377340397802345882939 126770066010596703518824409)
                ·
                  refine ⟨95077549507947527639118307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126770066010596703518824409 95077549507947527639118307)
                  ·
                    refine ⟨142616324261921291458677461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95077549507947527639118307 142616324261921291458677461)
                    ·
                      refine ⟨3342570099888780268562753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142616324261921291458677461 3342570099888780268562753)
                      ·
                        rfl

theorem cell23_6509632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_6509632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509632 prefixEnd_6509632 := by exact prefixLift 6509632
  have htrace : WordTrace (prefixWord ++ tailWord_6509632) baseStart_6509632 baseEnd_6509632 := by
    simpa [prefixWord, tailWord_6509632, baseEnd_6509632] using wordTrace_append hprefix tailTrace_6509632
  have hstable : (prefixWord ++ tailWord_6509632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509632).length < 2 ^ (prefixWord ++ tailWord_6509632).sum := by decide
  have hdescent : baseEnd_6509632 < baseStart_6509632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509639 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 3, 5]
def baseStart_6509639 : Nat := 118140960795 + 6509639 * 2 ^ 59
def prefixEnd_6509639 : Nat := 4983230072969 + 3 ^ 40 * 6509639 * 2
def baseEnd_6509639 : Nat := 1114191231417787247058407

theorem tailTrace_6509639 : CollatzResearch.WordTrace tailWord_6509639 prefixEnd_6509639 1114191231417787247058407 := by
  unfold tailWord_6509639
  simp only [CollatzResearch.WordTrace]
  refine ⟨237426039663697135674747971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158284026442464757116498647 237426039663697135674747971)
  ·
    refine ⟨356139059495545703512121957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237426039663697135674747971 356139059495545703512121957)
    ·
      refine ⟨66776073655414819408522867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356139059495545703512121957 66776073655414819408522867)
      ·
        refine ⟨100164110483122229112784301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66776073655414819408522867 100164110483122229112784301)
        ·
          refine ⟨37561541431170835917294113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100164110483122229112784301 37561541431170835917294113)
          ·
            refine ⟨28171156073378126937970585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37561541431170835917294113 28171156073378126937970585)
            ·
              refine ⟨21128367055033595203477939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28171156073378126937970585 21128367055033595203477939)
              ·
                refine ⟨31692550582550392805216909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21128367055033595203477939 31692550582550392805216909)
                ·
                  refine ⟨11884706468456397301956341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31692550582550392805216909 11884706468456397301956341)
                  ·
                    refine ⟨1114191231417787247058407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11884706468456397301956341 1114191231417787247058407)
                    ·
                      rfl

theorem cell23_6509639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_6509639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509639 prefixEnd_6509639 := by exact prefixLift 6509639
  have htrace : WordTrace (prefixWord ++ tailWord_6509639) baseStart_6509639 baseEnd_6509639 := by
    simpa [prefixWord, tailWord_6509639, baseEnd_6509639] using wordTrace_append hprefix tailTrace_6509639
  have hstable : (prefixWord ++ tailWord_6509639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509639).length < 2 ^ (prefixWord ++ tailWord_6509639).sum := by decide
  have hdescent : baseEnd_6509639 < baseStart_6509639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509646 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_6509646 : Nat := 118140960795 + 6509646 * 2 ^ 59
def prefixEnd_6509646 : Nat := 4983230072969 + 3 ^ 40 * 6509646 * 2
def baseEnd_6509646 : Nat := 3342577288617943213787689

theorem tailTrace_6509646 : CollatzResearch.WordTrace tailWord_6509646 prefixEnd_6509646 3342577288617943213787689 := by
  unfold tailWord_6509646
  simp only [CollatzResearch.WordTrace]
  refine ⟨29678286871833971983781599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158284196649781183913501861 29678286871833971983781599)
  ·
    refine ⟨44517430307750957975672399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29678286871833971983781599 44517430307750957975672399)
    ·
      refine ⟨66776145461626436963508599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44517430307750957975672399 66776145461626436963508599)
      ·
        refine ⟨100164218192439655445262899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66776145461626436963508599 100164218192439655445262899)
        ·
          refine ⟨150246327288659483167894349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100164218192439655445262899 150246327288659483167894349)
          ·
            refine ⟨56342372733247306187960381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150246327288659483167894349 56342372733247306187960381)
            ·
              refine ⟨21128389774967739820485143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56342372733247306187960381 21128389774967739820485143)
              ·
                refine ⟨31692584662451609730727715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21128389774967739820485143 31692584662451609730727715)
                ·
                  refine ⟨47538876993677414596091573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31692584662451609730727715 47538876993677414596091573)
                  ·
                    refine ⟨4456769718157257618383585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47538876993677414596091573 4456769718157257618383585)
                    ·
                      refine ⟨3342577288617943213787689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456769718157257618383585 3342577288617943213787689)
                      ·
                        rfl

theorem cell23_6509646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_6509646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509646 prefixEnd_6509646 := by exact prefixLift 6509646
  have htrace : WordTrace (prefixWord ++ tailWord_6509646) baseStart_6509646 baseEnd_6509646 := by
    simpa [prefixWord, tailWord_6509646, baseEnd_6509646] using wordTrace_append hprefix tailTrace_6509646
  have hstable : (prefixWord ++ tailWord_6509646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509646).length < 2 ^ (prefixWord ++ tailWord_6509646).sum := by decide
  have hdescent : baseEnd_6509646 < baseStart_6509646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509679 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_6509679 : Nat := 118140960795 + 6509679 * 2 ^ 59
def prefixEnd_6509679 : Nat := 4983230072969 + 3 ^ 40 * 6509679 * 2
def baseEnd_6509679 : Nat := 3342594233479541584675037

theorem tailTrace_6509679 : CollatzResearch.WordTrace tailWord_6509679 prefixEnd_6509679 3342594233479541584675037 := by
  unfold tailWord_6509679
  simp only [CollatzResearch.WordTrace]
  refine ⟨237427498583552222506204091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158284999055701481670802727 237427498583552222506204091)
  ·
    refine ⟨356141247875328333759306137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237427498583552222506204091 356141247875328333759306137)
    ·
      refine ⟨267105935906496250319479603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356141247875328333759306137 267105935906496250319479603)
      ·
        refine ⟨400658903859744375479219405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267105935906496250319479603 400658903859744375479219405)
        ·
          refine ⟨150247088947404140804707277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400658903859744375479219405 150247088947404140804707277)
          ·
            refine ⟨56342658355276552801765229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150247088947404140804707277 56342658355276552801765229)
            ·
              refine ⟨21128496883228707300661961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56342658355276552801765229 21128496883228707300661961)
              ·
                refine ⟨15846372662421530475496471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21128496883228707300661961 15846372662421530475496471)
                ·
                  refine ⟨23769558993632295713244707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15846372662421530475496471 23769558993632295713244707)
                  ·
                    refine ⟨35654338490448443569867061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23769558993632295713244707 35654338490448443569867061)
                    ·
                      refine ⟨3342594233479541584675037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35654338490448443569867061 3342594233479541584675037)
                      ·
                        rfl

theorem cell23_6509679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_6509679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509679 prefixEnd_6509679 := by exact prefixLift 6509679
  have htrace : WordTrace (prefixWord ++ tailWord_6509679) baseStart_6509679 baseEnd_6509679 := by
    simpa [prefixWord, tailWord_6509679, baseEnd_6509679] using wordTrace_append hprefix tailTrace_6509679
  have hstable : (prefixWord ++ tailWord_6509679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509679).length < 2 ^ (prefixWord ++ tailWord_6509679).sum := by decide
  have hdescent : baseEnd_6509679 < baseStart_6509679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509693 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_6509693 : Nat := 118140960795 + 6509693 * 2 ^ 59
def prefixEnd_6509693 : Nat := 4983230072969 + 3 ^ 40 * 6509693 * 2
def baseEnd_6509693 : Nat := 3342601422208704529899973

theorem tailTrace_6509693 : CollatzResearch.WordTrace tailWord_6509693 prefixEnd_6509693 3342601422208704529899973 := by
  unfold tailWord_6509693
  simp only [CollatzResearch.WordTrace]
  refine ⟨237428009205501502897213733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158285339470334335264809155 237428009205501502897213733)
  ·
    refine ⟨44517751726031531793227575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237428009205501502897213733 44517751726031531793227575)
    ·
      refine ⟨66776627589047297689841363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44517751726031531793227575 66776627589047297689841363)
      ·
        refine ⟨100164941383570946534762045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66776627589047297689841363 100164941383570946534762045)
        ·
          refine ⟨37561853018839104950535767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100164941383570946534762045 37561853018839104950535767)
          ·
            refine ⟨56342779528258657425803651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37561853018839104950535767 56342779528258657425803651)
            ·
              refine ⟨84514169292387986138705477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56342779528258657425803651 84514169292387986138705477)
              ·
                refine ⟨15846406742322747401007277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84514169292387986138705477 15846406742322747401007277)
                ·
                  refine ⟨5942402528371030275377729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15846406742322747401007277 5942402528371030275377729)
                  ·
                    refine ⟨4456801896278272706533297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5942402528371030275377729 4456801896278272706533297)
                    ·
                      refine ⟨3342601422208704529899973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456801896278272706533297 3342601422208704529899973)
                      ·
                        rfl

theorem cell23_6509693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_6509693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509693 prefixEnd_6509693 := by exact prefixLift 6509693
  have htrace : WordTrace (prefixWord ++ tailWord_6509693) baseStart_6509693 baseEnd_6509693 := by
    simpa [prefixWord, tailWord_6509693, baseEnd_6509693] using wordTrace_append hprefix tailTrace_6509693
  have hstable : (prefixWord ++ tailWord_6509693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509693).length < 2 ^ (prefixWord ++ tailWord_6509693).sum := by decide
  have hdescent : baseEnd_6509693 < baseStart_6509693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509696 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3]
def baseStart_6509696 : Nat := 118140960795 + 6509696 * 2 ^ 59
def prefixEnd_6509696 : Nat := 4983230072969 + 3 ^ 40 * 6509696 * 2
def baseEnd_6509696 : Nat := 3342602962650668018162459

theorem tailTrace_6509696 : CollatzResearch.WordTrace tailWord_6509696 prefixEnd_6509696 3342602962650668018162459 := by
  unfold tailWord_6509696
  simp only [CollatzResearch.WordTrace]
  refine ⟨118714059312245317204786471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158285412416327089606381961 118714059312245317204786471)
  ·
    refine ⟨178071088968367975807179707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118714059312245317204786471 178071088968367975807179707)
    ·
      refine ⟨267106633452551963710769561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178071088968367975807179707 267106633452551963710769561)
      ·
        refine ⟨200329975089413972783077171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267106633452551963710769561 200329975089413972783077171)
        ·
          refine ⟨300494962634120959174615757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200329975089413972783077171 300494962634120959174615757)
          ·
            refine ⟨112685610987795359690480909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300494962634120959174615757 112685610987795359690480909)
            ·
              refine ⟨42257104120423259883930341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112685610987795359690480909 42257104120423259883930341)
              ·
                refine ⟨7923207022579361228236939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42257104120423259883930341 7923207022579361228236939)
                ·
                  refine ⟨11884810533869041842355409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7923207022579361228236939 11884810533869041842355409)
                  ·
                    refine ⟨8913607900401781381766557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11884810533869041842355409 8913607900401781381766557)
                    ·
                      refine ⟨3342602962650668018162459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8913607900401781381766557 3342602962650668018162459)
                      ·
                        rfl

theorem cell23_6509696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_6509696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509696 prefixEnd_6509696 := by exact prefixLift 6509696
  have htrace : WordTrace (prefixWord ++ tailWord_6509696) baseStart_6509696 baseEnd_6509696 := by
    simpa [prefixWord, tailWord_6509696, baseEnd_6509696] using wordTrace_append hprefix tailTrace_6509696
  have hstable : (prefixWord ++ tailWord_6509696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509696).length < 2 ^ (prefixWord ++ tailWord_6509696).sum := by decide
  have hdescent : baseEnd_6509696 < baseStart_6509696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509704 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6509704 : Nat := 118140960795 + 6509704 * 2 ^ 59
def prefixEnd_6509704 : Nat := 4983230072969 + 3 ^ 40 * 6509704 * 2
def baseEnd_6509704 : Nat := 3342607070495903986862423

theorem tailTrace_6509704 : CollatzResearch.WordTrace tailWord_6509704 prefixEnd_6509704 3342607070495903986862423 := by
  unfold tailWord_6509704
  simp only [CollatzResearch.WordTrace]
  refine ⟨118714205204230825887932083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158285606938974434517242777 118714205204230825887932083)
  ·
    refine ⟨178071307806346238831898125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118714205204230825887932083 178071307806346238831898125)
    ·
      refine ⟨66776740427379839561961797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178071307806346238831898125 66776740427379839561961797)
      ·
        refine ⟨12520638830133719917867837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66776740427379839561961797 12520638830133719917867837)
        ·
          refine ⟨4695239561300144969200439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12520638830133719917867837 4695239561300144969200439)
          ·
            refine ⟨7042859341950217453800659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695239561300144969200439 7042859341950217453800659)
            ·
              refine ⟨10564289012925326180700989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042859341950217453800659 10564289012925326180700989)
              ·
                refine ⟨3961608379846997317762871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10564289012925326180700989 3961608379846997317762871)
                ·
                  refine ⟨5942412569770495976644307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961608379846997317762871 5942412569770495976644307)
                  ·
                    refine ⟨8913618854655743964966461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5942412569770495976644307 8913618854655743964966461)
                    ·
                      refine ⟨3342607070495903986862423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8913618854655743964966461 3342607070495903986862423)
                      ·
                        rfl

theorem cell23_6509704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6509704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509704 prefixEnd_6509704 := by exact prefixLift 6509704
  have htrace : WordTrace (prefixWord ++ tailWord_6509704) baseStart_6509704 baseEnd_6509704 := by
    simpa [prefixWord, tailWord_6509704, baseEnd_6509704] using wordTrace_append hprefix tailTrace_6509704
  have hstable : (prefixWord ++ tailWord_6509704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509704).length < 2 ^ (prefixWord ++ tailWord_6509704).sum := by decide
  have hdescent : baseEnd_6509704 < baseStart_6509704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509727 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6509727 : Nat := 118140960795 + 6509727 * 2 ^ 59
def prefixEnd_6509727 : Nat := 4983230072969 + 3 ^ 40 * 6509727 * 2
def baseEnd_6509727 : Nat := 3342618880550957396874817

theorem tailTrace_6509727 : CollatzResearch.WordTrace tailWord_6509727 prefixEnd_6509727 3342618880550957396874817 := by
  unfold tailWord_6509727
  simp only [CollatzResearch.WordTrace]
  refine ⟨237429249287378326703951435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158286166191585551135967623 237429249287378326703951435)
  ·
    refine ⟨356143873931067490055927153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237429249287378326703951435 356143873931067490055927153)
    ·
      refine ⟨267107905448300617541945365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356143873931067490055927153 267107905448300617541945365)
      ·
        refine ⟨12520683067889091447278689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267107905448300617541945365 12520683067889091447278689)
        ·
          refine ⟨9390512300916818585459017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12520683067889091447278689 9390512300916818585459017)
          ·
            refine ⟨7042884225687613939094263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9390512300916818585459017 7042884225687613939094263)
            ·
              refine ⟨10564326338531420908641395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7042884225687613939094263 10564326338531420908641395)
              ·
                refine ⟨15846489507797131362962093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10564326338531420908641395 15846489507797131362962093)
                ·
                  refine ⟨5942433565423924261110785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15846489507797131362962093 5942433565423924261110785)
                  ·
                    refine ⟨4456825174067943195833089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5942433565423924261110785 4456825174067943195833089)
                    ·
                      refine ⟨3342618880550957396874817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456825174067943195833089 3342618880550957396874817)
                      ·
                        rfl

theorem cell23_6509727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6509727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509727 prefixEnd_6509727 := by exact prefixLift 6509727
  have htrace : WordTrace (prefixWord ++ tailWord_6509727) baseStart_6509727 baseEnd_6509727 := by
    simpa [prefixWord, tailWord_6509727, baseEnd_6509727] using wordTrace_append hprefix tailTrace_6509727
  have hstable : (prefixWord ++ tailWord_6509727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509727).length < 2 ^ (prefixWord ++ tailWord_6509727).sum := by decide
  have hdescent : baseEnd_6509727 < baseStart_6509727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509729 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_6509729 : Nat := 118140960795 + 6509729 * 2 ^ 59
def prefixEnd_6509729 : Nat := 4983230072969 + 3 ^ 40 * 6509729 * 2
def baseEnd_6509729 : Nat := 1114206635837422129683269

theorem tailTrace_6509729 : CollatzResearch.WordTrace tailWord_6509729 prefixEnd_6509729 1114206635837422129683269 := by
  unfold tailWord_6509729
  simp only [CollatzResearch.WordTrace]
  refine ⟨237429322233371081045524241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158286214822247387363682827 237429322233371081045524241)
  ·
    refine ⟨178071991675028310784143181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237429322233371081045524241 178071991675028310784143181)
    ·
      refine ⟨66776996878135616544053693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178071991675028310784143181 66776996878135616544053693)
      ·
        refine ⟨25041373829300856204020135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66776996878135616544053693 25041373829300856204020135)
        ·
          refine ⟨37562060743951284306030203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25041373829300856204020135 37562060743951284306030203)
          ·
            refine ⟨56343091115926926459045305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37562060743951284306030203 56343091115926926459045305)
            ·
              refine ⟨42257318336945194844283979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56343091115926926459045305 42257318336945194844283979)
              ·
                refine ⟨63385977505417792266425969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42257318336945194844283979 63385977505417792266425969)
                ·
                  refine ⟨47539483129063344199819477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63385977505417792266425969 47539483129063344199819477)
                  ·
                    refine ⟨1114206635837422129683269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47539483129063344199819477 1114206635837422129683269)
                    ·
                      rfl

theorem cell23_6509729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_6509729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509729 prefixEnd_6509729 := by exact prefixLift 6509729
  have htrace : WordTrace (prefixWord ++ tailWord_6509729) baseStart_6509729 baseEnd_6509729 := by
    simpa [prefixWord, tailWord_6509729, baseEnd_6509729] using wordTrace_append hprefix tailTrace_6509729
  have hstable : (prefixWord ++ tailWord_6509729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509729).length < 2 ^ (prefixWord ++ tailWord_6509729).sum := by decide
  have hdescent : baseEnd_6509729 < baseStart_6509729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509753 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6509753 : Nat := 118140960795 + 6509753 * 2 ^ 59
def prefixEnd_6509753 : Nat := 4983230072969 + 3 ^ 40 * 6509753 * 2
def baseEnd_6509753 : Nat := 3342632231047974295149697

theorem tailTrace_6509753 : CollatzResearch.WordTrace tailWord_6509753 prefixEnd_6509753 3342632231047974295149697 := by
  unfold tailWord_6509753
  simp only [CollatzResearch.WordTrace]
  refine ⟨237430197585284133144397913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158286798390189422096265275 237430197585284133144397913)
  ·
    refine ⟨178072648188963099858298435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237430197585284133144397913 178072648188963099858298435)
    ·
      refine ⟨267108972283444649787447653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178072648188963099858298435 267108972283444649787447653)
      ·
        refine ⟨50082932303145871835146435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267108972283444649787447653 50082932303145871835146435)
        ·
          refine ⟨75124398454718807752719653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50082932303145871835146435 75124398454718807752719653)
          ·
            refine ⟨14085824710259776453634935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75124398454718807752719653 14085824710259776453634935)
            ·
              refine ⟨21128737065389664680452403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14085824710259776453634935 21128737065389664680452403)
              ·
                refine ⟨31693105598084497020678605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21128737065389664680452403 31693105598084497020678605)
                ·
                  refine ⟨11884914599281686382754477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31693105598084497020678605 11884914599281686382754477)
                  ·
                    refine ⟨4456842974730632393532929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11884914599281686382754477 4456842974730632393532929)
                    ·
                      refine ⟨3342632231047974295149697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456842974730632393532929 3342632231047974295149697)
                      ·
                        rfl

theorem cell23_6509753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6509753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509753 prefixEnd_6509753 := by exact prefixLift 6509753
  have htrace : WordTrace (prefixWord ++ tailWord_6509753) baseStart_6509753 baseEnd_6509753 := by
    simpa [prefixWord, tailWord_6509753, baseEnd_6509753] using wordTrace_append hprefix tailTrace_6509753
  have hstable : (prefixWord ++ tailWord_6509753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509753).length < 2 ^ (prefixWord ++ tailWord_6509753).sum := by decide
  have hdescent : baseEnd_6509753 < baseStart_6509753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509779 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4]
def baseStart_6509779 : Nat := 118140960795 + 6509779 * 2 ^ 59
def prefixEnd_6509779 : Nat := 4983230072969 + 3 ^ 40 * 6509779 * 2
def baseEnd_6509779 : Nat := 3342645581544991193424577

theorem tailTrace_6509779 : CollatzResearch.WordTrace tailWord_6509779 prefixEnd_6509779 3342645581544991193424577 := by
  unfold tailWord_6509779
  simp only [CollatzResearch.WordTrace]
  refine ⟨237431145883189939584844391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158287430588793293056562927 237431145883189939584844391)
  ·
    refine ⟨356146718824784909377266587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237431145883189939584844391 356146718824784909377266587)
    ·
      refine ⟨534220078237177364065899881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356146718824784909377266587 534220078237177364065899881)
      ·
        refine ⟨400665058677883023049424911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534220078237177364065899881 400665058677883023049424911)
        ·
          refine ⟨600997588016824534574137367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400665058677883023049424911 600997588016824534574137367)
          ·
            refine ⟨901496382025236801861206051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600997588016824534574137367 901496382025236801861206051)
            ·
              refine ⟨1352244573037855202791809077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901496382025236801861206051 1352244573037855202791809077)
              ·
                refine ⟨126772928722298925261732101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1352244573037855202791809077 126772928722298925261732101)
                ·
                  refine ⟨23769924135431048486574769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126772928722298925261732101 23769924135431048486574769)
                  ·
                    refine ⟨17827443101573286364931077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23769924135431048486574769 17827443101573286364931077)
                    ·
                      refine ⟨3342645581544991193424577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17827443101573286364931077 3342645581544991193424577)
                      ·
                        rfl

theorem cell23_6509779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_6509779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509779 prefixEnd_6509779 := by exact prefixLift 6509779
  have htrace : WordTrace (prefixWord ++ tailWord_6509779) baseStart_6509779 baseEnd_6509779 := by
    simpa [prefixWord, tailWord_6509779, baseEnd_6509779] using wordTrace_append hprefix tailTrace_6509779
  have hstable : (prefixWord ++ tailWord_6509779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509779).length < 2 ^ (prefixWord ++ tailWord_6509779).sum := by decide
  have hdescent : baseEnd_6509779 < baseStart_6509779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509783 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 4, 2, 2]
def baseStart_6509783 : Nat := 118140960795 + 6509783 * 2 ^ 59
def prefixEnd_6509783 : Nat := 4983230072969 + 3 ^ 40 * 6509783 * 2
def baseEnd_6509783 : Nat := 3342647635467609177774559

theorem tailTrace_6509783 : CollatzResearch.WordTrace tailWord_6509783 prefixEnd_6509783 3342647635467609177774559 := by
  unfold tailWord_6509783
  simp only [CollatzResearch.WordTrace]
  refine ⟨237431291775175448267990003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158287527850116965511993335 237431291775175448267990003)
  ·
    refine ⟨356146937662763172401985005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237431291775175448267990003 356146937662763172401985005)
    ·
      refine ⟨133555101623536189650744377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356146937662763172401985005 133555101623536189650744377)
      ·
        refine ⟨100166326217652142238058283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133555101623536189650744377 100166326217652142238058283)
        ·
          refine ⟨150249489326478213357087425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100166326217652142238058283 150249489326478213357087425)
          ·
            refine ⟨112687116994858660017815569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150249489326478213357087425 112687116994858660017815569)
            ·
              refine ⟨84515337746143995013361677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112687116994858660017815569 84515337746143995013361677)
              ·
                refine ⟨31693251654803998130010629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84515337746143995013361677 31693251654803998130010629)
                ·
                  refine ⟨5942484685275749649376993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31693251654803998130010629 5942484685275749649376993)
                  ·
                    refine ⟨4456863513956812237032745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5942484685275749649376993 4456863513956812237032745)
                    ·
                      refine ⟨3342647635467609177774559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456863513956812237032745 3342647635467609177774559)
                      ·
                        rfl

theorem cell23_6509783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_6509783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509783 prefixEnd_6509783 := by exact prefixLift 6509783
  have htrace : WordTrace (prefixWord ++ tailWord_6509783) baseStart_6509783 baseEnd_6509783 := by
    simpa [prefixWord, tailWord_6509783, baseEnd_6509783] using wordTrace_append hprefix tailTrace_6509783
  have hstable : (prefixWord ++ tailWord_6509783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509783).length < 2 ^ (prefixWord ++ tailWord_6509783).sum := by decide
  have hdescent : baseEnd_6509783 < baseStart_6509783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509800 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_6509800 : Nat := 118140960795 + 6509800 * 2 ^ 59
def prefixEnd_6509800 : Nat := 4983230072969 + 3 ^ 40 * 6509800 * 2
def baseEnd_6509800 : Nat := 3342656364638735611261981

theorem tailTrace_6509800 : CollatzResearch.WordTrace tailWord_6509800 prefixEnd_6509800 3342656364638735611261981 := by
  unfold tailWord_6509800
  simp only [CollatzResearch.WordTrace]
  refine ⟨118715955908056930085679427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158287941210742573447572569 118715955908056930085679427)
  ·
    refine ⟨178073933862085395128519141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118715955908056930085679427 178073933862085395128519141)
    ·
      refine ⟨33388862599141011586597339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178073933862085395128519141 33388862599141011586597339)
      ·
        refine ⟨50083293898711517379896009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33388862599141011586597339 50083293898711517379896009)
        ·
          refine ⟨37562470424033638034922007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50083293898711517379896009 37562470424033638034922007)
          ·
            refine ⟨56343705636050457052383011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37562470424033638034922007 56343705636050457052383011)
            ·
              refine ⟨84515558454075685578574517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56343705636050457052383011 84515558454075685578574517)
              ·
                refine ⟨7923333605069595522991361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84515558454075685578574517 7923333605069595522991361)
                ·
                  refine ⟨5942500203802196642243521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7923333605069595522991361 5942500203802196642243521)
                  ·
                    refine ⟨4456875152851647481682641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5942500203802196642243521 4456875152851647481682641)
                    ·
                      refine ⟨3342656364638735611261981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4456875152851647481682641 3342656364638735611261981)
                      ·
                        rfl

theorem cell23_6509800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_6509800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509800 prefixEnd_6509800 := by exact prefixLift 6509800
  have htrace : WordTrace (prefixWord ++ tailWord_6509800) baseStart_6509800 baseEnd_6509800 := by
    simpa [prefixWord, tailWord_6509800, baseEnd_6509800] using wordTrace_append hprefix tailTrace_6509800
  have hstable : (prefixWord ++ tailWord_6509800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509800).length < 2 ^ (prefixWord ++ tailWord_6509800).sum := by decide
  have hdescent : baseEnd_6509800 < baseStart_6509800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509823 : List Nat := [1, 1, 2, 2, 1, 6, 2, 3, 5]
def baseStart_6509823 : Nat := 118140960795 + 6509823 * 2 ^ 59
def prefixEnd_6509823 : Nat := 4983230072969 + 3 ^ 40 * 6509823 * 2
def baseEnd_6509823 : Nat := 371407574965976557919375

theorem tailTrace_6509823 : CollatzResearch.WordTrace tailWord_6509823 prefixEnd_6509823 371407574965976557919375 := by
  unfold tailWord_6509823
  simp only [CollatzResearch.WordTrace]
  refine ⟨237432750695030535099446123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158288500463353690066297415 237432750695030535099446123)
  ·
    refine ⟨356149126042545802649169185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237432750695030535099446123 356149126042545802649169185)
    ·
      refine ⟨267111844531909351986876889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356149126042545802649169185 267111844531909351986876889)
      ·
        refine ⟨200333883398932013990157667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267111844531909351986876889 200333883398932013990157667)
        ·
          refine ⟨300500825098398020985236501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200333883398932013990157667 300500825098398020985236501)
          ·
            refine ⟨14085976176487407233682961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 300500825098398020985236501 14085976176487407233682961)
            ·
              refine ⟨10564482132365555425262221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14085976176487407233682961 10564482132365555425262221)
              ·
                refine ⟨3961680799637083284473333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10564482132365555425262221 3961680799637083284473333)
                ·
                  refine ⟨371407574965976557919375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3961680799637083284473333 371407574965976557919375)
                  ·
                    rfl

theorem cell23_6509823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 5].length) (baseStart_6509823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509823 prefixEnd_6509823 := by exact prefixLift 6509823
  have htrace : WordTrace (prefixWord ++ tailWord_6509823) baseStart_6509823 baseEnd_6509823 := by
    simpa [prefixWord, tailWord_6509823, baseEnd_6509823] using wordTrace_append hprefix tailTrace_6509823
  have hstable : (prefixWord ++ tailWord_6509823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509823).length < 2 ^ (prefixWord ++ tailWord_6509823).sum := by decide
  have hdescent : baseEnd_6509823 < baseStart_6509823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509896 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 6]
def baseStart_6509896 : Nat := 118140960795 + 6509896 * 2 ^ 59
def prefixEnd_6509896 : Nat := 4983230072969 + 3 ^ 40 * 6509896 * 2
def baseEnd_6509896 : Nat := 371411739864618581740171

theorem tailTrace_6509896 : CollatzResearch.WordTrace tailWord_6509896 prefixEnd_6509896 371411739864618581740171 := by
  unfold tailWord_6509896
  simp only [CollatzResearch.WordTrace]
  refine ⟨118717706611883034283426771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158290275482510712377902361 118717706611883034283426771)
  ·
    refine ⟨178076559917824551425140157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118717706611883034283426771 178076559917824551425140157)
    ·
      refine ⟨66778709969184206784427559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178076559917824551425140157 66778709969184206784427559)
      ·
        refine ⟨100168064953776310176641339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66778709969184206784427559 100168064953776310176641339)
        ·
          refine ⟨150252097430664465264962009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100168064953776310176641339 150252097430664465264962009)
          ·
            refine ⟨112689073072998348948721507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150252097430664465264962009 112689073072998348948721507)
            ·
              refine ⟨169033609609497523423082261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112689073072998348948721507 169033609609497523423082261)
              ·
                refine ⟨7923450450445196410456981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169033609609497523423082261 7923450450445196410456981)
                ·
                  refine ⟨371411739864618581740171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7923450450445196410456981 371411739864618581740171)
                  ·
                    rfl

theorem cell23_6509896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 6].length) (baseStart_6509896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509896 prefixEnd_6509896 := by exact prefixLift 6509896
  have htrace : WordTrace (prefixWord ++ tailWord_6509896) baseStart_6509896 baseEnd_6509896 := by
    simpa [prefixWord, tailWord_6509896, baseEnd_6509896] using wordTrace_append hprefix tailTrace_6509896
  have hstable : (prefixWord ++ tailWord_6509896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509896).length < 2 ^ (prefixWord ++ tailWord_6509896).sum := by decide
  have hdescent : baseEnd_6509896 < baseStart_6509896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509900 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_6509900 : Nat := 118140960795 + 6509900 * 2 ^ 59
def prefixEnd_6509900 : Nat := 4983230072969 + 3 ^ 40 * 6509900 * 2
def baseEnd_6509900 : Nat := 1114235904234728406670507

theorem tailTrace_6509900 : CollatzResearch.WordTrace tailWord_6509900 prefixEnd_6509900 1114235904234728406670507 := by
  unfold tailWord_6509900
  simp only [CollatzResearch.WordTrace]
  refine ⟨118717779557875788624999577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158290372743834384833332769 118717779557875788624999577)
  ·
    refine ⟨89038334668406841468749683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118717779557875788624999577 89038334668406841468749683)
    ·
      refine ⟨133557502002610262203124525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89038334668406841468749683 133557502002610262203124525)
      ·
        refine ⟨50084063250978848326171697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133557502002610262203124525 50084063250978848326171697)
        ·
          refine ⟨37563047438234136244628773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50084063250978848326171697 37563047438234136244628773)
          ·
            refine ⟨7043071394668900545867895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37563047438234136244628773 7043071394668900545867895)
            ·
              refine ⟨10564607092003350818801843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043071394668900545867895 10564607092003350818801843)
              ·
                refine ⟨15846910638005026228202765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10564607092003350818801843 15846910638005026228202765)
                ·
                  refine ⟨5942591489251884835576037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15846910638005026228202765 5942591489251884835576037)
                  ·
                    refine ⟨1114235904234728406670507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5942591489251884835576037 1114235904234728406670507)
                    ·
                      rfl

theorem cell23_6509900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_6509900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509900 prefixEnd_6509900 := by exact prefixLift 6509900
  have htrace : WordTrace (prefixWord ++ tailWord_6509900) baseStart_6509900 baseEnd_6509900 := by
    simpa [prefixWord, tailWord_6509900, baseEnd_6509900] using wordTrace_append hprefix tailTrace_6509900
  have hstable : (prefixWord ++ tailWord_6509900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509900).length < 2 ^ (prefixWord ++ tailWord_6509900).sum := by decide
  have hdescent : baseEnd_6509900 < baseStart_6509900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509913 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 6]
def baseStart_6509913 : Nat := 118140960795 + 6509913 * 2 ^ 59
def prefixEnd_6509913 : Nat := 4983230072969 + 3 ^ 40 * 6509913 * 2
def baseEnd_6509913 : Nat := 371412709772521518794329

theorem tailTrace_6509913 : CollatzResearch.WordTrace tailWord_6509913 prefixEnd_6509913 371412709772521518794329 := by
  unfold tailWord_6509913
  simp only [CollatzResearch.WordTrace]
  refine ⟨237436033264704480470222393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158290688843136320313481595 237436033264704480470222393)
  ·
    refine ⟨178077024948528360352666795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237436033264704480470222393 178077024948528360352666795)
    ·
      refine ⟨267115537422792540529000193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178077024948528360352666795 267115537422792540529000193)
      ·
        refine ⟨200336653067094405396750145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267115537422792540529000193 200336653067094405396750145)
        ·
          refine ⟨150252489800320804047562609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200336653067094405396750145 150252489800320804047562609)
          ·
            refine ⟨112689367350240603035671957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150252489800320804047562609 112689367350240603035671957)
            ·
              refine ⟨5282314094542528267297123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112689367350240603035671957 5282314094542528267297123)
              ·
                refine ⟨7923471141813792400945685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282314094542528267297123 7923471141813792400945685)
                ·
                  refine ⟨371412709772521518794329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7923471141813792400945685 371412709772521518794329)
                  ·
                    rfl

theorem cell23_6509913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 6].length) (baseStart_6509913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509913 prefixEnd_6509913 := by exact prefixLift 6509913
  have htrace : WordTrace (prefixWord ++ tailWord_6509913) baseStart_6509913 baseEnd_6509913 := by
    simpa [prefixWord, tailWord_6509913, baseEnd_6509913] using wordTrace_append hprefix tailTrace_6509913
  have hstable : (prefixWord ++ tailWord_6509913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509913).length < 2 ^ (prefixWord ++ tailWord_6509913).sum := by decide
  have hdescent : baseEnd_6509913 < baseStart_6509913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6509997 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6509997 : Nat := 118140960795 + 6509997 * 2 ^ 59
def prefixEnd_6509997 : Nat := 4983230072969 + 3 ^ 40 * 6509997 * 2
def baseEnd_6509997 : Nat := 3342757520327671340498575

theorem tailTrace_6509997 : CollatzResearch.WordTrace tailWord_6509997 prefixEnd_6509997 3342757520327671340498575 := by
  unfold tailWord_6509997
  simp only [CollatzResearch.WordTrace]
  refine ⟨237439096996400162816280245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158292731330933441877520163 237439096996400162816280245)
  ·
    refine ⟨22259915343412515264026273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237439096996400162816280245 22259915343412515264026273)
    ·
      refine ⟨16694936507559386448019705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22259915343412515264026273 16694936507559386448019705)
      ·
        refine ⟨12521202380669539836014779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16694936507559386448019705 12521202380669539836014779)
        ·
          refine ⟨18781803571004309754022169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12521202380669539836014779 18781803571004309754022169)
          ·
            refine ⟨14086352678253232315516627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18781803571004309754022169 14086352678253232315516627)
            ·
              refine ⟨21129529017379848473274941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14086352678253232315516627 21129529017379848473274941)
              ·
                refine ⟨7923573381517443177478103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21129529017379848473274941 7923573381517443177478103)
                ·
                  refine ⟨11885360072276164766217155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7923573381517443177478103 11885360072276164766217155)
                  ·
                    refine ⟨17828040108414247149325733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11885360072276164766217155 17828040108414247149325733)
                    ·
                      refine ⟨3342757520327671340498575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17828040108414247149325733 3342757520327671340498575)
                      ·
                        rfl

theorem cell23_6509997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6509997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6509997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6509997 prefixEnd_6509997 := by exact prefixLift 6509997
  have htrace : WordTrace (prefixWord ++ tailWord_6509997) baseStart_6509997 baseEnd_6509997 := by
    simpa [prefixWord, tailWord_6509997, baseEnd_6509997] using wordTrace_append hprefix tailTrace_6509997
  have hstable : (prefixWord ++ tailWord_6509997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6509997).length < 2 ^ (prefixWord ++ tailWord_6509997).sum := by decide
  have hdescent : baseEnd_6509997 < baseStart_6509997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6509997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510016 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 9]
def baseStart_6510016 : Nat := 118140960795 + 6510016 * 2 ^ 59
def prefixEnd_6510016 : Nat := 4983230072969 + 3 ^ 40 * 6510016 * 2
def baseEnd_6510016 : Nat := 1114255758820035588720329

theorem tailTrace_6510016 : CollatzResearch.WordTrace tailWord_6510016 prefixEnd_6510016 1114255758820035588720329 := by
  unfold tailWord_6510016
  simp only [CollatzResearch.WordTrace]
  refine ⟨118719894991665664530610951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158293193322220886040814601 118719894991665664530610951)
  ·
    refine ⟨178079842487498496795916427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118719894991665664530610951 178079842487498496795916427)
    ·
      refine ⟨267119763731247745193874641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178079842487498496795916427 267119763731247745193874641)
      ·
        refine ⟨200339822798435808895405981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267119763731247745193874641 200339822798435808895405981)
        ·
          refine ⟨75127433549413428335777243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200339822798435808895405981 75127433549413428335777243)
          ·
            refine ⟨112691150324120142503665865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75127433549413428335777243 112691150324120142503665865)
            ·
              refine ⟨84518362743090106877749399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112691150324120142503665865 84518362743090106877749399)
              ·
                refine ⟨126777544114635160316624099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84518362743090106877749399 126777544114635160316624099)
                ·
                  refine ⟨190166316171952740474936149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126777544114635160316624099 190166316171952740474936149)
                  ·
                    refine ⟨1114255758820035588720329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 190166316171952740474936149 1114255758820035588720329)
                    ·
                      rfl

theorem cell23_6510016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_6510016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510016 prefixEnd_6510016 := by exact prefixLift 6510016
  have htrace : WordTrace (prefixWord ++ tailWord_6510016) baseStart_6510016 baseEnd_6510016 := by
    simpa [prefixWord, tailWord_6510016, baseEnd_6510016] using wordTrace_append hprefix tailTrace_6510016
  have hstable : (prefixWord ++ tailWord_6510016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510016).length < 2 ^ (prefixWord ++ tailWord_6510016).sum := by decide
  have hdescent : baseEnd_6510016 < baseStart_6510016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510030 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_6510030 : Nat := 118140960795 + 6510030 * 2 ^ 59
def prefixEnd_6510030 : Nat := 4983230072969 + 3 ^ 40 * 6510030 * 2
def baseEnd_6510030 : Nat := 3342774465189269711385923

theorem tailTrace_6510030 : CollatzResearch.WordTrace tailWord_6510030 prefixEnd_6510030 3342774465189269711385923 := by
  unfold tailWord_6510030
  simp only [CollatzResearch.WordTrace]
  refine ⟨29680037575660076181528943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158293533736853739634821029 29680037575660076181528943)
  ·
    refine ⟨44520056363490114272293415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29680037575660076181528943 44520056363490114272293415)
    ·
      refine ⟨66780084545235171408440123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44520056363490114272293415 66780084545235171408440123)
      ·
        refine ⟨100170126817852757112660185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66780084545235171408440123 100170126817852757112660185)
        ·
          refine ⟨75127595113389567834495139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100170126817852757112660185 75127595113389567834495139)
          ·
            refine ⟨112691392670084351751742709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75127595113389567834495139 112691392670084351751742709)
            ·
              refine ⟨10564818062820407976725879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112691392670084351751742709 10564818062820407976725879)
              ·
                refine ⟨15847227094230611965088819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10564818062820407976725879 15847227094230611965088819)
                ·
                  refine ⟨23770840641345917947633229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15847227094230611965088819 23770840641345917947633229)
                  ·
                    refine ⟨8914065240504719230362461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23770840641345917947633229 8914065240504719230362461)
                    ·
                      refine ⟨3342774465189269711385923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914065240504719230362461 3342774465189269711385923)
                      ·
                        rfl

theorem cell23_6510030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_6510030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510030 prefixEnd_6510030 := by exact prefixLift 6510030
  have htrace : WordTrace (prefixWord ++ tailWord_6510030) baseStart_6510030 baseEnd_6510030 := by
    simpa [prefixWord, tailWord_6510030, baseEnd_6510030] using wordTrace_append hprefix tailTrace_6510030
  have hstable : (prefixWord ++ tailWord_6510030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510030).length < 2 ^ (prefixWord ++ tailWord_6510030).sum := by decide
  have hdescent : baseEnd_6510030 < baseStart_6510030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510040 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 3, 3, 2]
def baseStart_6510040 : Nat := 118140960795 + 6510040 * 2 ^ 59
def prefixEnd_6510040 : Nat := 4983230072969 + 3 ^ 40 * 6510040 * 2
def baseEnd_6510040 : Nat := 3342779599995814672260877

theorem tailTrace_6510040 : CollatzResearch.WordTrace tailWord_6510040 prefixEnd_6510040 3342779599995814672260877 := by
  unfold tailWord_6510040
  simp only [CollatzResearch.WordTrace]
  refine ⟨118720332667622190580047787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158293776890162920773397049 118720332667622190580047787)
  ·
    refine ⟨178080499001433285870071681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118720332667622190580047787 178080499001433285870071681)
    ·
      refine ⟨133560374251074964402553761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178080499001433285870071681 133560374251074964402553761)
      ·
        refine ⟨100170280688306223301915321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133560374251074964402553761 100170280688306223301915321)
        ·
          refine ⟨75127710516229667476436491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100170280688306223301915321 75127710516229667476436491)
          ·
            refine ⟨112691565774344501214654737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75127710516229667476436491 112691565774344501214654737)
            ·
              refine ⟨84518674330758375910991053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112691565774344501214654737 84518674330758375910991053)
              ·
                refine ⟨31694502874034390966621645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84518674330758375910991053 31694502874034390966621645)
                ·
                  refine ⟨11885438577762896612483117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31694502874034390966621645 11885438577762896612483117)
                  ·
                    refine ⟨4457039466661086229681169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11885438577762896612483117 4457039466661086229681169)
                    ·
                      refine ⟨3342779599995814672260877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457039466661086229681169 3342779599995814672260877)
                      ·
                        rfl

theorem cell23_6510040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_6510040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510040 prefixEnd_6510040 := by exact prefixLift 6510040
  have htrace : WordTrace (prefixWord ++ tailWord_6510040) baseStart_6510040 baseEnd_6510040 := by
    simpa [prefixWord, tailWord_6510040, baseEnd_6510040] using wordTrace_append hprefix tailTrace_6510040
  have hstable : (prefixWord ++ tailWord_6510040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510040).length < 2 ^ (prefixWord ++ tailWord_6510040).sum := by decide
  have hdescent : baseEnd_6510040 < baseStart_6510040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510073 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_6510073 : Nat := 118140960795 + 6510073 * 2 ^ 59
def prefixEnd_6510073 : Nat := 4983230072969 + 3 ^ 40 * 6510073 * 2
def baseEnd_6510073 : Nat := 3342796544857413043148225

theorem tailTrace_6510073 : CollatzResearch.WordTrace tailWord_6510073 prefixEnd_6510073 3342796544857413043148225 := by
  unfold tailWord_6510073
  simp only [CollatzResearch.WordTrace]
  refine ⟨237441868944124827796046873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158294579296083218530697915 237441868944124827796046873)
  ·
    refine ⟨178081401708093620847035155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237441868944124827796046873 178081401708093620847035155)
    ·
      refine ⟨267122102562140431270552733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178081401708093620847035155 267122102562140431270552733)
      ·
        refine ⟨100170788460802661726457275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267122102562140431270552733 100170788460802661726457275)
        ·
          refine ⟨150256182691203992589685913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100170788460802661726457275 150256182691203992589685913)
          ·
            refine ⟨112692137018402994442264435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150256182691203992589685913 112692137018402994442264435)
            ·
              refine ⟨169038205527604491663396653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112692137018402994442264435 169038205527604491663396653)
              ·
                refine ⟨63389327072851684373773745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169038205527604491663396653 63389327072851684373773745)
                ·
                  refine ⟨47541995304638763280330309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63389327072851684373773745 47541995304638763280330309)
                  ·
                    refine ⟨8914124119619768115061933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47541995304638763280330309 8914124119619768115061933)
                    ·
                      refine ⟨3342796544857413043148225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914124119619768115061933 3342796544857413043148225)
                      ·
                        rfl

theorem cell23_6510073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_6510073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510073 prefixEnd_6510073 := by exact prefixLift 6510073
  have htrace : WordTrace (prefixWord ++ tailWord_6510073) baseStart_6510073 baseEnd_6510073 := by
    simpa [prefixWord, tailWord_6510073, baseEnd_6510073] using wordTrace_append hprefix tailTrace_6510073
  have hstable : (prefixWord ++ tailWord_6510073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510073).length < 2 ^ (prefixWord ++ tailWord_6510073).sum := by decide
  have hdescent : baseEnd_6510073 < baseStart_6510073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510081 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_6510081 : Nat := 118140960795 + 6510081 * 2 ^ 59
def prefixEnd_6510081 : Nat := 4983230072969 + 3 ^ 40 * 6510081 * 2
def baseEnd_6510081 : Nat := 3342800652702649011848189

theorem tailTrace_6510081 : CollatzResearch.WordTrace tailWord_6510081 prefixEnd_6510081 3342800652702649011848189 := by
  unfold tailWord_6510081
  simp only [CollatzResearch.WordTrace]
  refine ⟨237442160728095845162338097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158294773818730563441558731 237442160728095845162338097)
  ·
    refine ⟨178081620546071883871753573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237442160728095845162338097 178081620546071883871753573)
    ·
      refine ⟨33390303852388478225953795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178081620546071883871753573 33390303852388478225953795)
      ·
        refine ⟨50085455778582717338930693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33390303852388478225953795 50085455778582717338930693)
        ·
          refine ⟨9391022958484259501049505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50085455778582717338930693 9391022958484259501049505)
          ·
            refine ⟨7043267218863194625787129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9391022958484259501049505 7043267218863194625787129)
            ·
              refine ⟨5282450414147395969340347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7043267218863194625787129 5282450414147395969340347)
              ·
                refine ⟨7923675621221093954010521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282450414147395969340347 7923675621221093954010521)
                ·
                  refine ⟨5942756715915820465507891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7923675621221093954010521 5942756715915820465507891)
                  ·
                    refine ⟨8914135073873730698261837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5942756715915820465507891 8914135073873730698261837)
                    ·
                      refine ⟨3342800652702649011848189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914135073873730698261837 3342800652702649011848189)
                      ·
                        rfl

theorem cell23_6510081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_6510081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510081 prefixEnd_6510081 := by exact prefixLift 6510081
  have htrace : WordTrace (prefixWord ++ tailWord_6510081) baseStart_6510081 baseEnd_6510081 := by
    simpa [prefixWord, tailWord_6510081, baseEnd_6510081] using wordTrace_append hprefix tailTrace_6510081
  have hstable : (prefixWord ++ tailWord_6510081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510081).length < 2 ^ (prefixWord ++ tailWord_6510081).sum := by decide
  have hdescent : baseEnd_6510081 < baseStart_6510081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510091 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 1, 3, 2]
def baseStart_6510091 : Nat := 118140960795 + 6510091 * 2 ^ 59
def prefixEnd_6510091 : Nat := 4983230072969 + 3 ^ 40 * 6510091 * 2
def baseEnd_6510091 : Nat := 3342805787509193972723143

theorem tailTrace_6510091 : CollatzResearch.WordTrace tailWord_6510091 prefixEnd_6510091 3342805787509193972723143 := by
  unfold tailWord_6510091
  simp only [CollatzResearch.WordTrace]
  refine ⟨237442525458059616870202127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158295016972039744580134751 237442525458059616870202127)
  ·
    refine ⟨356163788187089425305303191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237442525458059616870202127 356163788187089425305303191)
    ·
      refine ⟨534245682280634137957954787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356163788187089425305303191 534245682280634137957954787)
      ·
        refine ⟨801368523420951206936932181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534245682280634137957954787 801368523420951206936932181)
        ·
          refine ⟨4695518691919635978146087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 801368523420951206936932181 4695518691919635978146087)
          ·
            refine ⟨7043278037879453967219131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695518691919635978146087 7043278037879453967219131)
            ·
              refine ⟨10564917056819180950828697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043278037879453967219131 10564917056819180950828697)
              ·
                refine ⟨7923687792614385713121523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10564917056819180950828697 7923687792614385713121523)
                ·
                  refine ⟨11885531688921578569682285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7923687792614385713121523 11885531688921578569682285)
                  ·
                    refine ⟨4457074383345591963630857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11885531688921578569682285 4457074383345591963630857)
                    ·
                      refine ⟨3342805787509193972723143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457074383345591963630857 3342805787509193972723143)
                      ·
                        rfl

theorem cell23_6510091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 3, 2].length) (baseStart_6510091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510091 prefixEnd_6510091 := by exact prefixLift 6510091
  have htrace : WordTrace (prefixWord ++ tailWord_6510091) baseStart_6510091 baseEnd_6510091 := by
    simpa [prefixWord, tailWord_6510091, baseEnd_6510091] using wordTrace_append hprefix tailTrace_6510091
  have hstable : (prefixWord ++ tailWord_6510091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510091).length < 2 ^ (prefixWord ++ tailWord_6510091).sum := by decide
  have hdescent : baseEnd_6510091 < baseStart_6510091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510157 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6510157 : Nat := 118140960795 + 6510157 * 2 ^ 59
def prefixEnd_6510157 : Nat := 4983230072969 + 3 ^ 40 * 6510157 * 2
def baseEnd_6510157 : Nat := 1114279892410796904832613

theorem tailTrace_6510157 : CollatzResearch.WordTrace tailWord_6510157 prefixEnd_6510157 1114279892410796904832613 := by
  unfold tailWord_6510157
  simp only [CollatzResearch.WordTrace]
  refine ⟨237444932675820510142104725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158296621783880340094736483 237444932675820510142104725)
  ·
    refine ⟨11130231219179086412911159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237444932675820510142104725 11130231219179086412911159)
    ·
      refine ⟨16695346828768629619366739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11130231219179086412911159 16695346828768629619366739)
      ·
        refine ⟨25043020243152944429050109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16695346828768629619366739 25043020243152944429050109)
        ·
          refine ⟨9391132591182354160893791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25043020243152944429050109 9391132591182354160893791)
          ·
            refine ⟨14086698886773531241340687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9391132591182354160893791 14086698886773531241340687)
            ·
              refine ⟨21130048330160296862011031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14086698886773531241340687 21130048330160296862011031)
              ·
                refine ⟨31695072495240445293016547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21130048330160296862011031 31695072495240445293016547)
                ·
                  refine ⟨47542608742860667939524821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31695072495240445293016547 47542608742860667939524821)
                  ·
                    refine ⟨1114279892410796904832613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47542608742860667939524821 1114279892410796904832613)
                    ·
                      rfl

theorem cell23_6510157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6510157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510157 prefixEnd_6510157 := by exact prefixLift 6510157
  have htrace : WordTrace (prefixWord ++ tailWord_6510157) baseStart_6510157 baseEnd_6510157 := by
    simpa [prefixWord, tailWord_6510157, baseEnd_6510157] using wordTrace_append hprefix tailTrace_6510157
  have hstable : (prefixWord ++ tailWord_6510157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510157).length < 2 ^ (prefixWord ++ tailWord_6510157).sum := by decide
  have hdescent : baseEnd_6510157 < baseStart_6510157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510160 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 6, 2]
def baseStart_6510160 : Nat := 118140960795 + 6510160 * 2 ^ 59
def prefixEnd_6510160 : Nat := 4983230072969 + 3 ^ 40 * 6510160 * 2
def baseEnd_6510160 : Nat := 3342841217674354202760325

theorem tailTrace_6510160 : CollatzResearch.WordTrace tailWord_6510160 prefixEnd_6510160 3342841217674354202760325 := by
  unfold tailWord_6510160
  simp only [CollatzResearch.WordTrace]
  refine ⟨118722521047404820827231967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158296694729873094436309289 118722521047404820827231967)
  ·
    refine ⟨178083781571107231240847951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118722521047404820827231967 178083781571107231240847951)
    ·
      refine ⟨267125672356660846861271927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178083781571107231240847951 267125672356660846861271927)
      ·
        refine ⟨400688508534991270291907891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267125672356660846861271927 400688508534991270291907891)
        ·
          refine ⟨601032762802486905437861837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400688508534991270291907891 601032762802486905437861837)
          ·
            refine ⟨225387286050932589539198189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601032762802486905437861837 225387286050932589539198189)
            ·
              refine ⟨84520232269099721077199321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225387286050932589539198189 84520232269099721077199321)
              ·
                refine ⟨63390174201824790807899491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84520232269099721077199321 63390174201824790807899491)
                ·
                  refine ⟨95085261302737186211849237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63390174201824790807899491 95085261302737186211849237)
                  ·
                    refine ⟨4457121623565805603680433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95085261302737186211849237 4457121623565805603680433)
                    ·
                      refine ⟨3342841217674354202760325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457121623565805603680433 3342841217674354202760325)
                      ·
                        rfl

theorem cell23_6510160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 6, 2].length) (baseStart_6510160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510160 prefixEnd_6510160 := by exact prefixLift 6510160
  have htrace : WordTrace (prefixWord ++ tailWord_6510160) baseStart_6510160 baseEnd_6510160 := by
    simpa [prefixWord, tailWord_6510160, baseEnd_6510160] using wordTrace_append hprefix tailTrace_6510160
  have hstable : (prefixWord ++ tailWord_6510160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510160).length < 2 ^ (prefixWord ++ tailWord_6510160).sum := by decide
  have hdescent : baseEnd_6510160 < baseStart_6510160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510197 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6510197 : Nat := 118140960795 + 6510197 * 2 ^ 59
def prefixEnd_6510197 : Nat := 4983230072969 + 3 ^ 40 * 6510197 * 2
def baseEnd_6510197 : Nat := 3342860216458570557997655

theorem tailTrace_6510197 : CollatzResearch.WordTrace tailWord_6510197 prefixEnd_6510197 3342860216458570557997655 := by
  unfold tailWord_6510197
  simp only [CollatzResearch.WordTrace]
  refine ⟨237446391595675596973560845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158297594397117064649040563 237446391595675596973560845)
  ·
    refine ⟨89042396848378348865085317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237446391595675596973560845 89042396848378348865085317)
    ·
      refine ⟨16695449409070940412203497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89042396848378348865085317 16695449409070940412203497)
      ·
        refine ⟨12521587056803205309152623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16695449409070940412203497 12521587056803205309152623)
        ·
          refine ⟨18782380585204807963728935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12521587056803205309152623 18782380585204807963728935)
          ·
            refine ⟨28173570877807211945593403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18782380585204807963728935 28173570877807211945593403)
            ·
              refine ⟨42260356316710817918390105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28173570877807211945593403 42260356316710817918390105)
              ·
                refine ⟨31695267237533113438792579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42260356316710817918390105 31695267237533113438792579)
                ·
                  refine ⟨47542900856299670158188869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31695267237533113438792579 47542900856299670158188869)
                  ·
                    refine ⟨8914293910556188154660413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47542900856299670158188869 8914293910556188154660413)
                    ·
                      refine ⟨3342860216458570557997655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914293910556188154660413 3342860216458570557997655)
                      ·
                        rfl

theorem cell23_6510197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6510197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510197 prefixEnd_6510197 := by exact prefixLift 6510197
  have htrace : WordTrace (prefixWord ++ tailWord_6510197) baseStart_6510197 baseEnd_6510197 := by
    simpa [prefixWord, tailWord_6510197, baseEnd_6510197] using wordTrace_append hprefix tailTrace_6510197
  have hstable : (prefixWord ++ tailWord_6510197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510197).length < 2 ^ (prefixWord ++ tailWord_6510197).sum := by decide
  have hdescent : baseEnd_6510197 < baseStart_6510197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510203 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_6510203 : Nat := 118140960795 + 6510203 * 2 ^ 59
def prefixEnd_6510203 : Nat := 4983230072969 + 3 ^ 40 * 6510203 * 2
def baseEnd_6510203 : Nat := 3342863297342497534522627

theorem tailTrace_6510203 : CollatzResearch.WordTrace tailWord_6510203 prefixEnd_6510203 3342863297342497534522627 := by
  unfold tailWord_6510203
  simp only [CollatzResearch.WordTrace]
  refine ⟨237446610433653859998279263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158297740289102573332186175 237446610433653859998279263)
  ·
    refine ⟨356169915650480789997418895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237446610433653859998279263 356169915650480789997418895)
    ·
      refine ⟨534254873475721184996128343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356169915650480789997418895 534254873475721184996128343)
      ·
        refine ⟨801382310213581777494192515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534254873475721184996128343 801382310213581777494192515)
        ·
          refine ⟨1202073465320372666241288773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801382310213581777494192515 1202073465320372666241288773)
          ·
            refine ⟨225388774747569874920241645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1202073465320372666241288773 225388774747569874920241645)
            ·
              refine ⟨84520790530338703095090617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225388774747569874920241645 84520790530338703095090617)
              ·
                refine ⟨63390592897754027321317963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84520790530338703095090617 63390592897754027321317963)
                ·
                  refine ⟨95085889346631040981976945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63390592897754027321317963 95085889346631040981976945)
                  ·
                    refine ⟨71314417009973280736482709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95085889346631040981976945 71314417009973280736482709)
                    ·
                      refine ⟨3342863297342497534522627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71314417009973280736482709 3342863297342497534522627)
                      ·
                        rfl

theorem cell23_6510203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_6510203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510203 prefixEnd_6510203 := by exact prefixLift 6510203
  have htrace : WordTrace (prefixWord ++ tailWord_6510203) baseStart_6510203 baseEnd_6510203 := by
    simpa [prefixWord, tailWord_6510203, baseEnd_6510203] using wordTrace_append hprefix tailTrace_6510203
  have hstable : (prefixWord ++ tailWord_6510203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510203).length < 2 ^ (prefixWord ++ tailWord_6510203).sum := by decide
  have hdescent : baseEnd_6510203 < baseStart_6510203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510223 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_6510223 : Nat := 118140960795 + 6510223 * 2 ^ 59
def prefixEnd_6510223 : Nat := 4983230072969 + 3 ^ 40 * 6510223 * 2
def baseEnd_6510223 : Nat := 3342873566955587456272535

theorem tailTrace_6510223 : CollatzResearch.WordTrace tailWord_6510223 prefixEnd_6510223 3342873566955587456272535 := by
  unfold tailWord_6510223
  simp only [CollatzResearch.WordTrace]
  refine ⟨237447339893581403414007323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158298226595720935609338215 237447339893581403414007323)
  ·
    refine ⟨356171009840372105121010985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237447339893581403414007323 356171009840372105121010985)
    ·
      refine ⟨267128257380279078840758239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356171009840372105121010985 267128257380279078840758239)
      ·
        refine ⟨400692386070418618261137359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267128257380279078840758239 400692386070418618261137359)
        ·
          refine ⟨601038579105627927391706039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400692386070418618261137359 601038579105627927391706039)
          ·
            refine ⟨901557868658441891087559059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601038579105627927391706039 901557868658441891087559059)
            ·
              refine ⟨1352336802987662836631338589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901557868658441891087559059 1352336802987662836631338589)
              ·
                refine ⟨507126301120373563736751971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352336802987662836631338589 507126301120373563736751971)
                ·
                  refine ⟨760689451680560345605127957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507126301120373563736751971 760689451680560345605127957)
                  ·
                    refine ⟨35657318047526266200240373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 760689451680560345605127957 35657318047526266200240373)
                    ·
                      refine ⟨3342873566955587456272535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35657318047526266200240373 3342873566955587456272535)
                      ·
                        rfl

theorem cell23_6510223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_6510223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510223 prefixEnd_6510223 := by exact prefixLift 6510223
  have htrace : WordTrace (prefixWord ++ tailWord_6510223) baseStart_6510223 baseEnd_6510223 := by
    simpa [prefixWord, tailWord_6510223, baseEnd_6510223] using wordTrace_append hprefix tailTrace_6510223
  have hstable : (prefixWord ++ tailWord_6510223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510223).length < 2 ^ (prefixWord ++ tailWord_6510223).sum := by decide
  have hdescent : baseEnd_6510223 < baseStart_6510223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510238 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6510238 : Nat := 118140960795 + 6510238 * 2 ^ 59
def prefixEnd_6510238 : Nat := 4983230072969 + 3 ^ 40 * 6510238 * 2
def baseEnd_6510238 : Nat := 1114293756388468299194989

theorem tailTrace_6510238 : CollatzResearch.WordTrace tailWord_6510238 prefixEnd_6510238 1114293756388468299194989 := by
  unfold tailWord_6510238
  simp only [CollatzResearch.WordTrace]
  refine ⟨29680985873565882621975421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158298591325684707317202245 29680985873565882621975421)
  ·
    refine ⟨11130369702587205983240783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29680985873565882621975421 11130369702587205983240783)
    ·
      refine ⟨16695554553880808974861175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11130369702587205983240783 16695554553880808974861175)
      ·
        refine ⟨25043331830821213462291763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16695554553880808974861175 25043331830821213462291763)
        ·
          refine ⟨37564997746231820193437645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25043331830821213462291763 37564997746231820193437645)
          ·
            refine ⟨14086874154836932572539117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37564997746231820193437645 14086874154836932572539117)
            ·
              refine ⟨5282577808063849714702169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14086874154836932572539117 5282577808063849714702169)
              ·
                refine ⟨3961933356047887286026627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5282577808063849714702169 3961933356047887286026627)
                ·
                  refine ⟨5942900034071830929039941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3961933356047887286026627 5942900034071830929039941)
                  ·
                    refine ⟨1114293756388468299194989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5942900034071830929039941 1114293756388468299194989)
                    ·
                      rfl

theorem cell23_6510238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6510238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510238 prefixEnd_6510238 := by exact prefixLift 6510238
  have htrace : WordTrace (prefixWord ++ tailWord_6510238) baseStart_6510238 baseEnd_6510238 := by
    simpa [prefixWord, tailWord_6510238, baseEnd_6510238] using wordTrace_append hprefix tailTrace_6510238
  have hstable : (prefixWord ++ tailWord_6510238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510238).length < 2 ^ (prefixWord ++ tailWord_6510238).sum := by decide
  have hdescent : baseEnd_6510238 < baseStart_6510238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510244 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_6510244 : Nat := 118140960795 + 6510244 * 2 ^ 59
def prefixEnd_6510244 : Nat := 4983230072969 + 3 ^ 40 * 6510244 * 2
def baseEnd_6510244 : Nat := 3342884350049331874109939

theorem tailTrace_6510244 : CollatzResearch.WordTrace tailWord_6510244 prefixEnd_6510244 3342884350049331874109939 := by
  unfold tailWord_6510244
  simp only [CollatzResearch.WordTrace]
  refine ⟨118724052913252662000260893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158298737217670216000347857 118724052913252662000260893)
  ·
    refine ⟨44521519842469748250097835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118724052913252662000260893 44521519842469748250097835)
    ·
      refine ⟨66782279763704622375146753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44521519842469748250097835 66782279763704622375146753)
      ·
        refine ⟨50086709822778466781360065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66782279763704622375146753 50086709822778466781360065)
        ·
          refine ⟨37565032367083850086020049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50086709822778466781360065 37565032367083850086020049)
          ·
            refine ⟨28173774275312887564515037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37565032367083850086020049 28173774275312887564515037)
            ·
              refine ⟨10565165353242332836693139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28173774275312887564515037 10565165353242332836693139)
              ·
                refine ⟨15847748029863499255039709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565165353242332836693139 15847748029863499255039709)
                ·
                  refine ⟨5942905511198812220639891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15847748029863499255039709 5942905511198812220639891)
                  ·
                    refine ⟨8914358266798218330959837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5942905511198812220639891 8914358266798218330959837)
                    ·
                      refine ⟨3342884350049331874109939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914358266798218330959837 3342884350049331874109939)
                      ·
                        rfl

theorem cell23_6510244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_6510244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510244 prefixEnd_6510244 := by exact prefixLift 6510244
  have htrace : WordTrace (prefixWord ++ tailWord_6510244) baseStart_6510244 baseEnd_6510244 := by
    simpa [prefixWord, tailWord_6510244, baseEnd_6510244] using wordTrace_append hprefix tailTrace_6510244
  have hstable : (prefixWord ++ tailWord_6510244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510244).length < 2 ^ (prefixWord ++ tailWord_6510244).sum := by decide
  have hdescent : baseEnd_6510244 < baseStart_6510244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510287 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 3]
def baseStart_6510287 : Nat := 118140960795 + 6510287 * 2 ^ 59
def prefixEnd_6510287 : Nat := 4983230072969 + 3 ^ 40 * 6510287 * 2
def baseEnd_6510287 : Nat := 3342906429717475205872241

theorem tailTrace_6510287 : CollatzResearch.WordTrace tailWord_6510287 prefixEnd_6510287 3342906429717475205872241 := by
  unfold tailWord_6510287
  simp only [CollatzResearch.WordTrace]
  refine ⟨237449674165349542344337115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158299782776899694896224743 237449674165349542344337115)
  ·
    refine ⟨356174511248024313516505673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237449674165349542344337115 356174511248024313516505673)
    ·
      refine ⟨267130883436018235137379255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356174511248024313516505673 267130883436018235137379255)
      ·
        refine ⟨400696325154027352706068883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267130883436018235137379255 400696325154027352706068883)
        ·
          refine ⟨601044487731041029059103325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400696325154027352706068883 601044487731041029059103325)
          ·
            refine ⟨225391682899140385897163747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601044487731041029059103325 225391682899140385897163747)
            ·
              refine ⟨338087524348710578845745621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225391682899140385897163747 338087524348710578845745621)
              ·
                refine ⟨7923926351922904191697163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 338087524348710578845745621 7923926351922904191697163)
                ·
                  refine ⟨11885889527884356287545745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7923926351922904191697163 11885889527884356287545745)
                  ·
                    refine ⟨8914417145913267215659309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11885889527884356287545745 8914417145913267215659309)
                    ·
                      refine ⟨3342906429717475205872241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914417145913267215659309 3342906429717475205872241)
                      ·
                        rfl

theorem cell23_6510287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_6510287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510287 prefixEnd_6510287 := by exact prefixLift 6510287
  have htrace : WordTrace (prefixWord ++ tailWord_6510287) baseStart_6510287 baseEnd_6510287 := by
    simpa [prefixWord, tailWord_6510287, baseEnd_6510287] using wordTrace_append hprefix tailTrace_6510287
  have hstable : (prefixWord ++ tailWord_6510287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510287).length < 2 ^ (prefixWord ++ tailWord_6510287).sum := by decide
  have hdescent : baseEnd_6510287 < baseStart_6510287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510290 : List Nat := [3, 2, 2, 2, 2, 12]
def baseStart_6510290 : Nat := 118140960795 + 6510290 * 2 ^ 59
def prefixEnd_6510290 : Nat := 4983230072969 + 3 ^ 40 * 6510290 * 2
def baseEnd_6510290 : Nat := 13756822922466825901789

theorem tailTrace_6510290 : CollatzResearch.WordTrace tailWord_6510290 prefixEnd_6510290 13756822922466825901789 := by
  unfold tailWord_6510290
  simp only [CollatzResearch.WordTrace]
  refine ⟨59362445896084668464174081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158299855722892449237797549 59362445896084668464174081)
  ·
    refine ⟨44521834422063501348130561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59362445896084668464174081 44521834422063501348130561)
    ·
      refine ⟨33391375816547626011097921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44521834422063501348130561 33391375816547626011097921)
      ·
        refine ⟨25043531862410719508323441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33391375816547626011097921 25043531862410719508323441)
        ·
          refine ⟨18782648896808039631242581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25043531862410719508323441 18782648896808039631242581)
          ·
            refine ⟨13756822922466825901789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18782648896808039631242581 13756822922466825901789)
            ·
              rfl

theorem cell23_6510290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 12].length) (baseStart_6510290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510290 prefixEnd_6510290 := by exact prefixLift 6510290
  have htrace : WordTrace (prefixWord ++ tailWord_6510290) baseStart_6510290 baseEnd_6510290 := by
    simpa [prefixWord, tailWord_6510290, baseEnd_6510290] using wordTrace_append hprefix tailTrace_6510290
  have hstable : (prefixWord ++ tailWord_6510290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510290).length < 2 ^ (prefixWord ++ tailWord_6510290).sum := by decide
  have hdescent : baseEnd_6510290 < baseStart_6510290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510330 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_6510330 : Nat := 118140960795 + 6510330 * 2 ^ 59
def prefixEnd_6510330 : Nat := 4983230072969 + 3 ^ 40 * 6510330 * 2
def baseEnd_6510330 : Nat := 3342928509385618537634543

theorem tailTrace_6510330 : CollatzResearch.WordTrace tailWord_6510330 prefixEnd_6510330 3342928509385618537634543 := by
  unfold tailWord_6510330
  simp only [CollatzResearch.WordTrace]
  refine ⟨59362810626048440172038111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158300828336129173792101629 59362810626048440172038111)
  ·
    refine ⟨89044215939072660258057167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59362810626048440172038111 89044215939072660258057167)
    ·
      refine ⟨133566323908608990387085751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89044215939072660258057167 133566323908608990387085751)
      ·
        refine ⟨200349485862913485580628627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133566323908608990387085751 200349485862913485580628627)
        ·
          refine ⟨300524228794370228370942941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200349485862913485580628627 300524228794370228370942941)
          ·
            refine ⟨112696585797888835639103603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300524228794370228370942941 112696585797888835639103603)
            ·
              refine ⟨169044878696833253458655405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112696585797888835639103603 169044878696833253458655405)
              ·
                refine ⟨63391829511312470046995777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169044878696833253458655405 63391829511312470046995777)
                ·
                  refine ⟨47543872133484352535246833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63391829511312470046995777 47543872133484352535246833)
                  ·
                    refine ⟨35657904100113264401435125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47543872133484352535246833 35657904100113264401435125)
                    ·
                      refine ⟨3342928509385618537634543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35657904100113264401435125 3342928509385618537634543)
                      ·
                        rfl

theorem cell23_6510330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_6510330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510330 prefixEnd_6510330 := by exact prefixLift 6510330
  have htrace : WordTrace (prefixWord ++ tailWord_6510330) baseStart_6510330 baseEnd_6510330 := by
    simpa [prefixWord, tailWord_6510330, baseEnd_6510330] using wordTrace_append hprefix tailTrace_6510330
  have hstable : (prefixWord ++ tailWord_6510330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510330).length < 2 ^ (prefixWord ++ tailWord_6510330).sum := by decide
  have hdescent : baseEnd_6510330 < baseStart_6510330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510400 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_6510400 : Nat := 118140960795 + 6510400 * 2 ^ 59
def prefixEnd_6510400 : Nat := 4983230072969 + 3 ^ 40 * 6510400 * 2
def baseEnd_6510400 : Nat := 3342964453031433263759221

theorem tailTrace_6510400 : CollatzResearch.WordTrace tailWord_6510400 prefixEnd_6510400 3342964453031433263759221 := by
  unfold tailWord_6510400
  simp only [CollatzResearch.WordTrace]
  refine ⟨118726897806970081321600327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158302530409293441762133769 118726897806970081321600327)
  ·
    refine ⟨178090346710455121982400491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118726897806970081321600327 178090346710455121982400491)
    ·
      refine ⟨267135520065682682973600737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178090346710455121982400491 267135520065682682973600737)
      ·
        refine ⟨200351640049262012230200553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267135520065682682973600737 200351640049262012230200553)
        ·
          refine ⟨150263730036946509172650415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200351640049262012230200553 150263730036946509172650415)
          ·
            refine ⟨225395595055419763758975623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150263730036946509172650415 225395595055419763758975623)
            ·
              refine ⟨338093392583129645638463435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225395595055419763758975623 338093392583129645638463435)
              ·
                refine ⟨507140088874694468457695153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338093392583129645638463435 507140088874694468457695153)
                ·
                  refine ⟨380355066656020851343271365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507140088874694468457695153 380355066656020851343271365)
                  ·
                    refine ⟨71316574998003909626863381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380355066656020851343271365 71316574998003909626863381)
                    ·
                      refine ⟨3342964453031433263759221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71316574998003909626863381 3342964453031433263759221)
                      ·
                        rfl

theorem cell23_6510400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_6510400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510400 prefixEnd_6510400 := by exact prefixLift 6510400
  have htrace : WordTrace (prefixWord ++ tailWord_6510400) baseStart_6510400 baseEnd_6510400 := by
    simpa [prefixWord, tailWord_6510400, baseEnd_6510400] using wordTrace_append hprefix tailTrace_6510400
  have hstable : (prefixWord ++ tailWord_6510400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510400).length < 2 ^ (prefixWord ++ tailWord_6510400).sum := by decide
  have hdescent : baseEnd_6510400 < baseStart_6510400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510407 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_6510407 : Nat := 118140960795 + 6510407 * 2 ^ 59
def prefixEnd_6510407 : Nat := 4983230072969 + 3 ^ 40 * 6510407 * 2
def baseEnd_6510407 : Nat := 3342968047396014736371689

theorem tailTrace_6510407 : CollatzResearch.WordTrace tailWord_6510407 prefixEnd_6510407 3342968047396014736371689 := by
  unfold tailWord_6510407
  simp only [CollatzResearch.WordTrace]
  refine ⟨237454050924914802838705475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158302700616609868559136983 237454050924914802838705475)
  ·
    refine ⟨356181076387372204258058213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237454050924914802838705475 356181076387372204258058213)
    ·
      refine ⟨66783951822632288298385915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356181076387372204258058213 66783951822632288298385915)
      ·
        refine ⟨100175927733948432447578873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66783951822632288298385915 100175927733948432447578873)
        ·
          refine ⟨75131945800461324335684155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100175927733948432447578873 75131945800461324335684155)
          ·
            refine ⟨112697918700691986503526233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75131945800461324335684155 112697918700691986503526233)
            ·
              refine ⟨84523439025518989877644675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112697918700691986503526233 84523439025518989877644675)
              ·
                refine ⟨126785158538278484816467013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84523439025518989877644675 126785158538278484816467013)
                ·
                  refine ⟨23772217225927215903087565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126785158538278484816467013 23772217225927215903087565)
                  ·
                    refine ⟨8914581459722705963657837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23772217225927215903087565 8914581459722705963657837)
                    ·
                      refine ⟨3342968047396014736371689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914581459722705963657837 3342968047396014736371689)
                      ·
                        rfl

theorem cell23_6510407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_6510407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510407 prefixEnd_6510407 := by exact prefixLift 6510407
  have htrace : WordTrace (prefixWord ++ tailWord_6510407) baseStart_6510407 baseEnd_6510407 := by
    simpa [prefixWord, tailWord_6510407, baseEnd_6510407] using wordTrace_append hprefix tailTrace_6510407
  have hstable : (prefixWord ++ tailWord_6510407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510407).length < 2 ^ (prefixWord ++ tailWord_6510407).sum := by decide
  have hdescent : baseEnd_6510407 < baseStart_6510407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510444 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_6510444 : Nat := 118140960795 + 6510444 * 2 ^ 59
def prefixEnd_6510444 : Nat := 4983230072969 + 3 ^ 40 * 6510444 * 2
def baseEnd_6510444 : Nat := 1114329015393410363869673

theorem tailTrace_6510444 : CollatzResearch.WordTrace tailWord_6510444 prefixEnd_6510444 1114329015393410363869673 := by
  unfold tailWord_6510444
  simp only [CollatzResearch.WordTrace]
  refine ⟨118727700212890379078901193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158303600283853838771868257 118727700212890379078901193)
  ·
    refine ⟨89045775159667784309175895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118727700212890379078901193 89045775159667784309175895)
    ·
      refine ⟨133568662739501676463763843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89045775159667784309175895 133568662739501676463763843)
      ·
        refine ⟨200352994109252514695645765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133568662739501676463763843 200352994109252514695645765)
        ·
          refine ⟨37566186395484846505433581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200352994109252514695645765 37566186395484846505433581)
          ·
            refine ⟨14087319898306817439537593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37566186395484846505433581 14087319898306817439537593)
            ·
              refine ⟨10565489923730113079653195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14087319898306817439537593 10565489923730113079653195)
              ·
                refine ⟨15848234885595169619479793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565489923730113079653195 15848234885595169619479793)
                ·
                  refine ⟨11886176164196377214609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15848234885595169619479793 11886176164196377214609845)
                  ·
                    refine ⟨1114329015393410363869673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11886176164196377214609845 1114329015393410363869673)
                    ·
                      rfl

theorem cell23_6510444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_6510444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510444 prefixEnd_6510444 := by exact prefixLift 6510444
  have htrace : WordTrace (prefixWord ++ tailWord_6510444) baseStart_6510444 baseEnd_6510444 := by
    simpa [prefixWord, tailWord_6510444, baseEnd_6510444] using wordTrace_append hprefix tailTrace_6510444
  have hstable : (prefixWord ++ tailWord_6510444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510444).length < 2 ^ (prefixWord ++ tailWord_6510444).sum := by decide
  have hdescent : baseEnd_6510444 < baseStart_6510444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510464 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 2, 4, 2]
def baseStart_6510464 : Nat := 118140960795 + 6510464 * 2 ^ 59
def prefixEnd_6510464 : Nat := 4983230072969 + 3 ^ 40 * 6510464 * 2
def baseEnd_6510464 : Nat := 3342997315793321013358927

theorem tailTrace_6510464 : CollatzResearch.WordTrace tailWord_6510464 prefixEnd_6510464 3342997315793321013358927 := by
  unfold tailWord_6510464
  simp only [CollatzResearch.WordTrace]
  refine ⟨118728064942854150786765223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158304086590472201049020297 118728064942854150786765223)
  ·
    refine ⟨178092097414281226180147835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118728064942854150786765223 178092097414281226180147835)
    ·
      refine ⟨267138146121421839270221753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178092097414281226180147835 267138146121421839270221753)
      ·
        refine ⟨200353609591066379452666315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267138146121421839270221753 200353609591066379452666315)
        ·
          refine ⟨300530414386599569178999473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200353609591066379452666315 300530414386599569178999473)
          ·
            refine ⟨225397810789949676884249605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300530414386599569178999473 225397810789949676884249605)
            ·
              refine ⟨42262089523115564415796801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225397810789949676884249605 42262089523115564415796801)
              ·
                refine ⟨31696567142336673311847601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42262089523115564415796801 31696567142336673311847601)
                ·
                  refine ⟨23772425356752504983885701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31696567142336673311847601 23772425356752504983885701)
                  ·
                    refine ⟨4457329754391094684478569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23772425356752504983885701 4457329754391094684478569)
                    ·
                      refine ⟨3342997315793321013358927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457329754391094684478569 3342997315793321013358927)
                      ·
                        rfl

theorem cell23_6510464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_6510464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510464 prefixEnd_6510464 := by exact prefixLift 6510464
  have htrace : WordTrace (prefixWord ++ tailWord_6510464) baseStart_6510464 baseEnd_6510464 := by
    simpa [prefixWord, tailWord_6510464, baseEnd_6510464] using wordTrace_append hprefix tailTrace_6510464
  have hstable : (prefixWord ++ tailWord_6510464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510464).length < 2 ^ (prefixWord ++ tailWord_6510464).sum := by decide
  have hdescent : baseEnd_6510464 < baseStart_6510464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510465 : List Nat := [1, 2, 4, 4, 1, 2, 2, 2, 5]
def baseStart_6510465 : Nat := 118140960795 + 6510465 * 2 ^ 59
def prefixEnd_6510465 : Nat := 4983230072969 + 3 ^ 40 * 6510465 * 2
def baseEnd_6510465 : Nat := 371444203252663945494047

theorem tailTrace_6510465 : CollatzResearch.WordTrace tailWord_6510465 prefixEnd_6510465 371444203252663945494047 := by
  unfold tailWord_6510465
  simp only [CollatzResearch.WordTrace]
  refine ⟨237456166358704678744316849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158304110905803119162877899 237456166358704678744316849)
  ·
    refine ⟨178092124769028509058237637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237456166358704678744316849 178092124769028509058237637)
    ·
      refine ⟨33392273394192845448419557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178092124769028509058237637 33392273394192845448419557)
      ·
        refine ⟨6261051261411158521578667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33392273394192845448419557 6261051261411158521578667)
        ·
          refine ⟨9391576892116737782368001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261051261411158521578667 9391576892116737782368001)
          ·
            refine ⟨7043682669087553336776001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9391576892116737782368001 7043682669087553336776001)
            ·
              refine ⟨5282762001815665002582001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7043682669087553336776001 5282762001815665002582001)
              ·
                refine ⟨3962071501361748751936501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5282762001815665002582001 3962071501361748751936501)
                ·
                  refine ⟨371444203252663945494047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3962071501361748751936501 371444203252663945494047)
                  ·
                    rfl

theorem cell23_6510465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 5].length) (baseStart_6510465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510465 prefixEnd_6510465 := by exact prefixLift 6510465
  have htrace : WordTrace (prefixWord ++ tailWord_6510465) baseStart_6510465 baseEnd_6510465 := by
    simpa [prefixWord, tailWord_6510465, baseEnd_6510465] using wordTrace_append hprefix tailTrace_6510465
  have hstable : (prefixWord ++ tailWord_6510465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510465).length < 2 ^ (prefixWord ++ tailWord_6510465).sum := by decide
  have hdescent : baseEnd_6510465 < baseStart_6510465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510498 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_6510498 : Nat := 118140960795 + 6510498 * 2 ^ 59
def prefixEnd_6510498 : Nat := 4983230072969 + 3 ^ 40 * 6510498 * 2
def baseEnd_6510498 : Nat := 3343014774135573880333771

theorem tailTrace_6510498 : CollatzResearch.WordTrace tailWord_6510498 prefixEnd_6510498 3343014774135573880333771 := by
  unfold tailWord_6510498
  simp only [CollatzResearch.WordTrace]
  refine ⟨59364342491896281345067037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158304913311723416920178765 59364342491896281345067037)
  ·
    refine ⟨22261628434461105504400139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59364342491896281345067037 22261628434461105504400139)
    ·
      refine ⟨33392442651691658256600209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22261628434461105504400139 33392442651691658256600209)
      ·
        refine ⟨25044331988768743692450157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33392442651691658256600209 25044331988768743692450157)
        ·
          refine ⟨9391624495788278884668809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25044331988768743692450157 9391624495788278884668809)
          ·
            refine ⟨7043718371841209163501607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9391624495788278884668809 7043718371841209163501607)
            ·
              refine ⟨10565577557761813745252411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043718371841209163501607 10565577557761813745252411)
              ·
                refine ⟨15848366336642720617878617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565577557761813745252411 15848366336642720617878617)
                ·
                  refine ⟨11886274752482040463408963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15848366336642720617878617 11886274752482040463408963)
                  ·
                    refine ⟨17829412128723060695113445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11886274752482040463408963 17829412128723060695113445)
                    ·
                      refine ⟨3343014774135573880333771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17829412128723060695113445 3343014774135573880333771)
                      ·
                        rfl

theorem cell23_6510498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_6510498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510498 prefixEnd_6510498 := by exact prefixLift 6510498
  have htrace : WordTrace (prefixWord ++ tailWord_6510498) baseStart_6510498 baseEnd_6510498 := by
    simpa [prefixWord, tailWord_6510498, baseEnd_6510498] using wordTrace_append hprefix tailTrace_6510498
  have hstable : (prefixWord ++ tailWord_6510498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510498).length < 2 ^ (prefixWord ++ tailWord_6510498).sum := by decide
  have hdescent : baseEnd_6510498 < baseStart_6510498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510564 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_6510564 : Nat := 118140960795 + 6510564 * 2 ^ 59
def prefixEnd_6510564 : Nat := 4983230072969 + 3 ^ 40 * 6510564 * 2
def baseEnd_6510564 : Nat := 1114349554619590207369489

theorem tailTrace_6510564 : CollatzResearch.WordTrace tailWord_6510564 prefixEnd_6510564 1114349554619590207369489 := by
  unfold tailWord_6510564
  simp only [CollatzResearch.WordTrace]
  refine ⟨118729888592673009326085373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158306518123564012434780497 118729888592673009326085373)
  ·
    refine ⟨44523708222252378497282015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118729888592673009326085373 44523708222252378497282015)
    ·
      refine ⟨66785562333378567745923023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44523708222252378497282015 66785562333378567745923023)
      ·
        refine ⟨100178343500067851618884535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66785562333378567745923023 100178343500067851618884535)
        ·
          refine ⟨150267515250101777428326803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100178343500067851618884535 150267515250101777428326803)
          ·
            refine ⟨225401272875152666142490205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150267515250101777428326803 225401272875152666142490205)
            ·
              refine ⟨84525477328182249803433827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225401272875152666142490205 84525477328182249803433827)
              ·
                refine ⟨126788215992273374705150741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84525477328182249803433827 126788215992273374705150741)
                ·
                  refine ⟨5943197624637814439303941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126788215992273374705150741 5943197624637814439303941)
                  ·
                    refine ⟨1114349554619590207369489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943197624637814439303941 1114349554619590207369489)
                    ·
                      rfl

theorem cell23_6510564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_6510564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510564 prefixEnd_6510564 := by exact prefixLift 6510564
  have htrace : WordTrace (prefixWord ++ tailWord_6510564) baseStart_6510564 baseEnd_6510564 := by
    simpa [prefixWord, tailWord_6510564, baseEnd_6510564] using wordTrace_append hprefix tailTrace_6510564
  have hstable : (prefixWord ++ tailWord_6510564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510564).length < 2 ^ (prefixWord ++ tailWord_6510564).sum := by decide
  have hdescent : baseEnd_6510564 < baseStart_6510564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510571 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 5, 2, 2]
def baseStart_6510571 : Nat := 118140960795 + 6510571 * 2 ^ 59
def prefixEnd_6510571 : Nat := 4983230072969 + 3 ^ 40 * 6510571 * 2
def baseEnd_6510571 : Nat := 3343052258223352094720935

theorem tailTrace_6510571 : CollatzResearch.WordTrace tailWord_6510571 prefixEnd_6510571 3343052258223352094720935 := by
  unfold tailWord_6510571
  simp only [CollatzResearch.WordTrace]
  refine ⟨237460032496320658847675567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158306688330880439231783711 237460032496320658847675567)
  ·
    refine ⟨356190048744480988271513351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237460032496320658847675567 356190048744480988271513351)
    ·
      refine ⟨534285073116721482407270027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356190048744480988271513351 534285073116721482407270027)
      ·
        refine ⟨801427609675082223610905041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534285073116721482407270027 801427609675082223610905041)
        ·
          refine ⟨601070707256311667708178781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 801427609675082223610905041 601070707256311667708178781)
          ·
            refine ⟨225401515221116875390567043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601070707256311667708178781 225401515221116875390567043)
            ·
              refine ⟨338102272831675313085850565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225401515221116875390567043 338102272831675313085850565)
              ·
                refine ⟨63394176155939121203596981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 338102272831675313085850565 63394176155939121203596981)
                ·
                  refine ⟨5943204014619292612837217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63394176155939121203596981 5943204014619292612837217)
                  ·
                    refine ⟨4457403010964469459627913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5943204014619292612837217 4457403010964469459627913)
                    ·
                      refine ⟨3343052258223352094720935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457403010964469459627913 3343052258223352094720935)
                      ·
                        rfl

theorem cell23_6510571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 2, 2].length) (baseStart_6510571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510571 prefixEnd_6510571 := by exact prefixLift 6510571
  have htrace : WordTrace (prefixWord ++ tailWord_6510571) baseStart_6510571 baseEnd_6510571 := by
    simpa [prefixWord, tailWord_6510571, baseEnd_6510571] using wordTrace_append hprefix tailTrace_6510571
  have hstable : (prefixWord ++ tailWord_6510571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510571).length < 2 ^ (prefixWord ++ tailWord_6510571).sum := by decide
  have hdescent : baseEnd_6510571 < baseStart_6510571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510582 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6510582 : Nat := 118140960795 + 6510582 * 2 ^ 59
def prefixEnd_6510582 : Nat := 4983230072969 + 3 ^ 40 * 6510582 * 2
def baseEnd_6510582 : Nat := 3343057906510551551683385

theorem tailTrace_6510582 : CollatzResearch.WordTrace tailWord_6510582 prefixEnd_6510582 3343057906510551551683385 := by
  unfold tailWord_6510582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841277106205050482895375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158306955799520538484217333 14841277106205050482895375)
  ·
    refine ⟨22261915659307575724343063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841277106205050482895375 22261915659307575724343063)
    ·
      refine ⟨33392873488961363586514595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22261915659307575724343063 33392873488961363586514595)
      ·
        refine ⟨50089310233442045379771893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33392873488961363586514595 50089310233442045379771893)
        ·
          refine ⟨4695872834385191754353615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50089310233442045379771893 4695872834385191754353615)
          ·
            refine ⟨7043809251577787631530423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4695872834385191754353615 7043809251577787631530423)
            ·
              refine ⟨10565713877366681447295635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7043809251577787631530423 10565713877366681447295635)
              ·
                refine ⟨15848570816050022170943453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565713877366681447295635 15848570816050022170943453)
                ·
                  refine ⟨5943214056018758314103795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15848570816050022170943453 5943214056018758314103795)
                  ·
                    refine ⟨8914821084028137471155693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5943214056018758314103795 8914821084028137471155693)
                    ·
                      refine ⟨3343057906510551551683385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914821084028137471155693 3343057906510551551683385)
                      ·
                        rfl

theorem cell23_6510582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6510582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510582 prefixEnd_6510582 := by exact prefixLift 6510582
  have htrace : WordTrace (prefixWord ++ tailWord_6510582) baseStart_6510582 baseEnd_6510582 := by
    simpa [prefixWord, tailWord_6510582, baseEnd_6510582] using wordTrace_append hprefix tailTrace_6510582
  have hstable : (prefixWord ++ tailWord_6510582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510582).length < 2 ^ (prefixWord ++ tailWord_6510582).sum := by decide
  have hdescent : baseEnd_6510582 < baseStart_6510582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510621 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_6510621 : Nat := 118140960795 + 6510621 * 2 ^ 59
def prefixEnd_6510621 : Nat := 4983230072969 + 3 ^ 40 * 6510621 * 2
def baseEnd_6510621 : Nat := 3343077932256076899095705

theorem tailTrace_6510621 : CollatzResearch.WordTrace tailWord_6510621 prefixEnd_6510621 3343077932256076899095705 := by
  unfold tailWord_6510621
  simp only [CollatzResearch.WordTrace]
  refine ⟨237461856146139517386995717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158307904097426344924663811 237461856146139517386995717)
  ·
    refine ⟨44524098027401159510061697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237461856146139517386995717 44524098027401159510061697)
    ·
      refine ⟨33393073520550869632546273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44524098027401159510061697 33393073520550869632546273)
      ·
        refine ⟨25044805140413152224409705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33393073520550869632546273 25044805140413152224409705)
        ·
          refine ⟨18783603855309864168307279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25044805140413152224409705 18783603855309864168307279)
          ·
            refine ⟨28175405782964796252460919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18783603855309864168307279 28175405782964796252460919)
            ·
              refine ⟨42263108674447194378691379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28175405782964796252460919 42263108674447194378691379)
              ·
                refine ⟨63394663011670791568037069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42263108674447194378691379 63394663011670791568037069)
                ·
                  refine ⟨23772998629376546838013901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63394663011670791568037069 23772998629376546838013901)
                  ·
                    refine ⟨8914874486016205064255213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23772998629376546838013901 8914874486016205064255213)
                    ·
                      refine ⟨3343077932256076899095705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914874486016205064255213 3343077932256076899095705)
                      ·
                        rfl

theorem cell23_6510621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_6510621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510621 prefixEnd_6510621 := by exact prefixLift 6510621
  have htrace : WordTrace (prefixWord ++ tailWord_6510621) baseStart_6510621 baseEnd_6510621 := by
    simpa [prefixWord, tailWord_6510621, baseEnd_6510621] using wordTrace_append hprefix tailTrace_6510621
  have hstable : (prefixWord ++ tailWord_6510621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510621).length < 2 ^ (prefixWord ++ tailWord_6510621).sum := by decide
  have hdescent : baseEnd_6510621 < baseStart_6510621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510625 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_6510625 : Nat := 118140960795 + 6510625 * 2 ^ 59
def prefixEnd_6510625 : Nat := 4983230072969 + 3 ^ 40 * 6510625 * 2
def baseEnd_6510625 : Nat := 3343079986178694883445687

theorem tailTrace_6510625 : CollatzResearch.WordTrace tailWord_6510625 prefixEnd_6510625 3343079986178694883445687 := by
  unfold tailWord_6510625
  simp only [CollatzResearch.WordTrace]
  refine ⟨237462002038125026070141329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158308001358750017380094219 237462002038125026070141329)
  ·
    refine ⟨178096501528593769552605997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237462002038125026070141329 178096501528593769552605997)
    ·
      refine ⟨66786188073222663582227249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178096501528593769552605997 66786188073222663582227249)
      ·
        refine ⟨50089641054916997686670437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66786188073222663582227249 50089641054916997686670437)
        ·
          refine ⟨9391807697796937066250707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50089641054916997686670437 9391807697796937066250707)
          ·
            refine ⟨14087711546695405599376061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9391807697796937066250707 14087711546695405599376061)
            ·
              refine ⟨5282891830010777099766023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14087711546695405599376061 5282891830010777099766023)
              ·
                refine ⟨7924337745016165649649035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5282891830010777099766023 7924337745016165649649035)
                ·
                  refine ⟨11886506617524248474473553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7924337745016165649649035 11886506617524248474473553)
                  ·
                    refine ⟨8914879963143186355855165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11886506617524248474473553 8914879963143186355855165)
                    ·
                      refine ⟨3343079986178694883445687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914879963143186355855165 3343079986178694883445687)
                      ·
                        rfl

theorem cell23_6510625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_6510625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510625 prefixEnd_6510625 := by exact prefixLift 6510625
  have htrace : WordTrace (prefixWord ++ tailWord_6510625) baseStart_6510625 baseEnd_6510625 := by
    simpa [prefixWord, tailWord_6510625, baseEnd_6510625] using wordTrace_append hprefix tailTrace_6510625
  have hstable : (prefixWord ++ tailWord_6510625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510625).length < 2 ^ (prefixWord ++ tailWord_6510625).sum := by decide
  have hdescent : baseEnd_6510625 < baseStart_6510625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510664 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_6510664 : Nat := 118140960795 + 6510664 * 2 ^ 59
def prefixEnd_6510664 : Nat := 4983230072969 + 3 ^ 40 * 6510664 * 2
def baseEnd_6510664 : Nat := 3343100011924220230858007

theorem tailTrace_6510664 : CollatzResearch.WordTrace tailWord_6510664 prefixEnd_6510664 3343100011924220230858007 := by
  unfold tailWord_6510664
  simp only [CollatzResearch.WordTrace]
  refine ⟨118731712242491867865405523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158308949656655823820540697 118731712242491867865405523)
  ·
    refine ⟨178097568363737801798108285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118731712242491867865405523 178097568363737801798108285)
    ·
      refine ⟨66786588136401675674290607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178097568363737801798108285 66786588136401675674290607)
      ·
        refine ⟨100179882204602513511435911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66786588136401675674290607 100179882204602513511435911)
        ·
          refine ⟨150269823306903770267153867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100179882204602513511435911 150269823306903770267153867)
          ·
            refine ⟨225404734960355655400730801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150269823306903770267153867 225404734960355655400730801)
            ·
              refine ⟨169053551220266741550548101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225404734960355655400730801 169053551220266741550548101)
              ·
                refine ⟨31697540853800014040727769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169053551220266741550548101 31697540853800014040727769)
                ·
                  refine ⟨23773155640350010530545827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31697540853800014040727769 23773155640350010530545827)
                  ·
                    refine ⟨35659733460525015795818741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23773155640350010530545827 35659733460525015795818741)
                    ·
                      refine ⟨3343100011924220230858007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35659733460525015795818741 3343100011924220230858007)
                      ·
                        rfl

theorem cell23_6510664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_6510664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510664 prefixEnd_6510664 := by exact prefixLift 6510664
  have htrace : WordTrace (prefixWord ++ tailWord_6510664) baseStart_6510664 baseEnd_6510664 := by
    simpa [prefixWord, tailWord_6510664, baseEnd_6510664] using wordTrace_append hprefix tailTrace_6510664
  have hstable : (prefixWord ++ tailWord_6510664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510664).length < 2 ^ (prefixWord ++ tailWord_6510664).sum := by decide
  have hdescent : baseEnd_6510664 < baseStart_6510664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510701 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 7]
def baseStart_6510701 : Nat := 118140960795 + 6510701 * 2 ^ 59
def prefixEnd_6510701 : Nat := 4983230072969 + 3 ^ 40 * 6510701 * 2
def baseEnd_6510701 : Nat := 371457667856492954010593

theorem tailTrace_6510701 : CollatzResearch.WordTrace tailWord_6510701 prefixEnd_6510701 371457667856492954010593 := by
  unfold tailWord_6510701
  simp only [CollatzResearch.WordTrace]
  refine ⟨237464773985849691049907957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158309849323899794033271971 237464773985849691049907957)
  ·
    refine ⟨22262322561173408535928871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237464773985849691049907957 22262322561173408535928871)
    ·
      refine ⟨33393483841760112803893307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22262322561173408535928871 33393483841760112803893307)
      ·
        refine ⟨50090225762640169205839961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33393483841760112803893307 50090225762640169205839961)
        ·
          refine ⟨37567669321980126904379971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50090225762640169205839961 37567669321980126904379971)
          ·
            refine ⟨56351503982970190356569957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37567669321980126904379971 56351503982970190356569957)
            ·
              refine ⟨10565906996806910691856867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56351503982970190356569957 10565906996806910691856867)
              ·
                refine ⟨15848860495210366037785301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10565906996806910691856867 15848860495210366037785301)
                ·
                  refine ⟨371457667856492954010593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15848860495210366037785301 371457667856492954010593)
                  ·
                    rfl

theorem cell23_6510701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_6510701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510701 prefixEnd_6510701 := by exact prefixLift 6510701
  have htrace : WordTrace (prefixWord ++ tailWord_6510701) baseStart_6510701 baseEnd_6510701 := by
    simpa [prefixWord, tailWord_6510701, baseEnd_6510701] using wordTrace_append hprefix tailTrace_6510701
  have hstable : (prefixWord ++ tailWord_6510701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510701).length < 2 ^ (prefixWord ++ tailWord_6510701).sum := by decide
  have hdescent : baseEnd_6510701 < baseStart_6510701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510711 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_6510711 : Nat := 118140960795 + 6510711 * 2 ^ 59
def prefixEnd_6510711 : Nat := 4983230072969 + 3 ^ 40 * 6510711 * 2
def baseEnd_6510711 : Nat := 3343124145514981546970291

theorem tailTrace_6510711 : CollatzResearch.WordTrace tailWord_6510711 prefixEnd_6510711 3343124145514981546970291 := by
  unfold tailWord_6510711
  simp only [CollatzResearch.WordTrace]
  refine ⟨237465138715813462757771987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158310092477208975171847991 237465138715813462757771987)
  ·
    refine ⟨356197708073720194136657981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237465138715813462757771987 356197708073720194136657981)
    ·
      refine ⟨133574140527645072801246743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356197708073720194136657981 133574140527645072801246743)
      ·
        refine ⟨200361210791467609201870115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133574140527645072801246743 200361210791467609201870115)
        ·
          refine ⟨300541816187201413802805173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200361210791467609201870115 300541816187201413802805173)
          ·
            refine ⟨28175795267550132544012985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300541816187201413802805173 28175795267550132544012985)
            ·
              refine ⟨21131846450662599408009739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28175795267550132544012985 21131846450662599408009739)
              ·
                refine ⟨31697769675993899112014609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21131846450662599408009739 31697769675993899112014609)
                ·
                  refine ⟨23773327256995424334010957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31697769675993899112014609 23773327256995424334010957)
                  ·
                    refine ⟨8914997721373284125254109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23773327256995424334010957 8914997721373284125254109)
                    ·
                      refine ⟨3343124145514981546970291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8914997721373284125254109 3343124145514981546970291)
                      ·
                        rfl

theorem cell23_6510711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_6510711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510711 prefixEnd_6510711 := by exact prefixLift 6510711
  have htrace : WordTrace (prefixWord ++ tailWord_6510711) baseStart_6510711 baseEnd_6510711 := by
    simpa [prefixWord, tailWord_6510711, baseEnd_6510711] using wordTrace_append hprefix tailTrace_6510711
  have hstable : (prefixWord ++ tailWord_6510711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510711).length < 2 ^ (prefixWord ++ tailWord_6510711).sum := by decide
  have hdescent : baseEnd_6510711 < baseStart_6510711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510764 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_6510764 : Nat := 118140960795 + 6510764 * 2 ^ 59
def prefixEnd_6510764 : Nat := 4983230072969 + 3 ^ 40 * 6510764 * 2
def baseEnd_6510764 : Nat := 3343151359989669839607547

theorem tailTrace_6510764 : CollatzResearch.WordTrace tailWord_6510764 prefixEnd_6510764 3343151359989669839607547 := by
  unfold tailWord_6510764
  simp only [CollatzResearch.WordTrace]
  refine ⟨118733535892310726404725673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158311381189747635206300897 118733535892310726404725673)
  ·
    refine ⟨89050151919233044803544255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118733535892310726404725673 89050151919233044803544255)
    ·
      refine ⟨133575227878849567205316383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89050151919233044803544255 133575227878849567205316383)
      ·
        refine ⟨200362841818274350807974575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133575227878849567205316383 200362841818274350807974575)
        ·
          refine ⟨300544262727411526211961863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200362841818274350807974575 300544262727411526211961863)
          ·
            refine ⟨450816394091117289317942795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300544262727411526211961863 450816394091117289317942795)
            ·
              refine ⟨676224591136675933976914193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450816394091117289317942795 676224591136675933976914193)
              ·
                refine ⟨507168443352506950482685645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676224591136675933976914193 507168443352506950482685645)
                ·
                  refine ⟨190188166257190106431007117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507168443352506950482685645 190188166257190106431007117)
                  ·
                    refine ⟨71320562346446289911627669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190188166257190106431007117 71320562346446289911627669)
                    ·
                      refine ⟨3343151359989669839607547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71320562346446289911627669 3343151359989669839607547)
                      ·
                        rfl

theorem cell23_6510764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_6510764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510764 prefixEnd_6510764 := by exact prefixLift 6510764
  have htrace : WordTrace (prefixWord ++ tailWord_6510764) baseStart_6510764 baseEnd_6510764 := by
    simpa [prefixWord, tailWord_6510764, baseEnd_6510764] using wordTrace_append hprefix tailTrace_6510764
  have hstable : (prefixWord ++ tailWord_6510764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510764).length < 2 ^ (prefixWord ++ tailWord_6510764).sum := by decide
  have hdescent : baseEnd_6510764 < baseStart_6510764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510771 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 3]
def baseStart_6510771 : Nat := 118140960795 + 6510771 * 2 ^ 59
def prefixEnd_6510771 : Nat := 4983230072969 + 3 ^ 40 * 6510771 * 2
def baseEnd_6510771 : Nat := 3343154954354251312220015

theorem tailTrace_6510771 : CollatzResearch.WordTrace tailWord_6510771 prefixEnd_6510771 3343154954354251312220015 := by
  unfold tailWord_6510771
  simp only [CollatzResearch.WordTrace]
  refine ⟨237467327095596093004956167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158311551397064062003304111 237467327095596093004956167)
  ·
    refine ⟨356200990643394139507434251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237467327095596093004956167 356200990643394139507434251)
    ·
      refine ⟨534301485965091209261151377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356200990643394139507434251 534301485965091209261151377)
      ·
        refine ⟨400726114473818406945863533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534301485965091209261151377 400726114473818406945863533)
        ·
          refine ⟨150272292927681902604698825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400726114473818406945863533 150272292927681902604698825)
          ·
            refine ⟨112704219695761426953524119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150272292927681902604698825 112704219695761426953524119)
            ·
              refine ⟨169056329543642140430286179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112704219695761426953524119 169056329543642140430286179)
              ·
                refine ⟨253584494315463210645429269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169056329543642140430286179 253584494315463210645429269)
                ·
                  refine ⟨11886773171037337999004497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 253584494315463210645429269 11886773171037337999004497)
                  ·
                    refine ⟨8915079878278003499253373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11886773171037337999004497 8915079878278003499253373)
                    ·
                      refine ⟨3343154954354251312220015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8915079878278003499253373 3343154954354251312220015)
                      ·
                        rfl

theorem cell23_6510771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_6510771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510771 prefixEnd_6510771 := by exact prefixLift 6510771
  have htrace : WordTrace (prefixWord ++ tailWord_6510771) baseStart_6510771 baseEnd_6510771 := by
    simpa [prefixWord, tailWord_6510771, baseEnd_6510771] using wordTrace_append hprefix tailTrace_6510771
  have hstable : (prefixWord ++ tailWord_6510771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510771).length < 2 ^ (prefixWord ++ tailWord_6510771).sum := by decide
  have hdescent : baseEnd_6510771 < baseStart_6510771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510808 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 6]
def baseStart_6510808 : Nat := 118140960795 + 6510808 * 2 ^ 59
def prefixEnd_6510808 : Nat := 4983230072969 + 3 ^ 40 * 6510808 * 2
def baseEnd_6510808 : Nat := 371463772570940851939705

theorem tailTrace_6510808 : CollatzResearch.WordTrace tailWord_6510808 prefixEnd_6510808 371463772570940851939705 := by
  unfold tailWord_6510808
  simp only [CollatzResearch.WordTrace]
  refine ⟨118734338298231024162026539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158312451064308032216035385 118734338298231024162026539)
  ·
    refine ⟨178101507447346536243039809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118734338298231024162026539 178101507447346536243039809)
    ·
      refine ⟨133576130585509902182279857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178101507447346536243039809 133576130585509902182279857)
      ·
        refine ⟨100182097939132426636709893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133576130585509902182279857 100182097939132426636709893)
        ·
          refine ⟨18784143363587329994383105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100182097939132426636709893 18784143363587329994383105)
          ·
            refine ⟨14088107522690497495787329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18784143363587329994383105 14088107522690497495787329)
            ·
              refine ⟨10566080642017873121840497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14088107522690497495787329 10566080642017873121840497)
              ·
                refine ⟨7924560481513404841380373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10566080642017873121840497 7924560481513404841380373)
                ·
                  refine ⟨371463772570940851939705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7924560481513404841380373 371463772570940851939705)
                  ·
                    rfl

theorem cell23_6510808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 6].length) (baseStart_6510808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510808 prefixEnd_6510808 := by exact prefixLift 6510808
  have htrace : WordTrace (prefixWord ++ tailWord_6510808) baseStart_6510808 baseEnd_6510808 := by
    simpa [prefixWord, tailWord_6510808, baseEnd_6510808] using wordTrace_append hprefix tailTrace_6510808
  have hstable : (prefixWord ++ tailWord_6510808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510808).length < 2 ^ (prefixWord ++ tailWord_6510808).sum := by decide
  have hdescent : baseEnd_6510808 < baseStart_6510808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510828 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 1, 5, 2]
def baseStart_6510828 : Nat := 118140960795 + 6510828 * 2 ^ 59
def prefixEnd_6510828 : Nat := 4983230072969 + 3 ^ 40 * 6510828 * 2
def baseEnd_6510828 : Nat := 3343184222751557589207253

theorem tailTrace_6510828 : CollatzResearch.WordTrace tailWord_6510828 prefixEnd_6510828 3343184222751557589207253 := by
  unfold tailWord_6510828
  simp only [CollatzResearch.WordTrace]
  refine ⟨118734703028194795869890569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158312937370926394493187425 118734703028194795869890569)
  ·
    refine ⟨89051027271146096902417927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118734703028194795869890569 89051027271146096902417927)
    ·
      refine ⟨133576540906719145353626891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89051027271146096902417927 133576540906719145353626891)
      ·
        refine ⟨200364811360078718030440337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133576540906719145353626891 200364811360078718030440337)
        ·
          refine ⟨150273608520059038522830253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200364811360078718030440337 150273608520059038522830253)
          ·
            refine ⟨56352603195022139446061345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150273608520059038522830253 56352603195022139446061345)
            ·
              refine ⟨42264452396266604584546009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56352603195022139446061345 42264452396266604584546009)
              ·
                refine ⟨31698339297199953438409507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42264452396266604584546009 31698339297199953438409507)
                ·
                  refine ⟨47547508945799930157614261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31698339297199953438409507 47547508945799930157614261)
                  ·
                    refine ⟨4457578963668743452276337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47547508945799930157614261 4457578963668743452276337)
                    ·
                      refine ⟨3343184222751557589207253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457578963668743452276337 3343184222751557589207253)
                      ·
                        rfl

theorem cell23_6510828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_6510828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510828 prefixEnd_6510828 := by exact prefixLift 6510828
  have htrace : WordTrace (prefixWord ++ tailWord_6510828) baseStart_6510828 baseEnd_6510828 := by
    simpa [prefixWord, tailWord_6510828, baseEnd_6510828] using wordTrace_append hprefix tailTrace_6510828
  have hstable : (prefixWord ++ tailWord_6510828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510828).length < 2 ^ (prefixWord ++ tailWord_6510828).sum := by decide
  have hdescent : baseEnd_6510828 < baseStart_6510828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510838 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_6510838 : Nat := 118140960795 + 6510838 * 2 ^ 59
def prefixEnd_6510838 : Nat := 4983230072969 + 3 ^ 40 * 6510838 * 2
def baseEnd_6510838 : Nat := 1114396452519367516694069

theorem tailTrace_6510838 : CollatzResearch.WordTrace tailWord_6510838 prefixEnd_6510838 1114396452519367516694069 := by
  unfold tailWord_6510838
  simp only [CollatzResearch.WordTrace]
  refine ⟨14841860674147085215477823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158313180524235575631763445 14841860674147085215477823)
  ·
    refine ⟨22262791011220627823216735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14841860674147085215477823 22262791011220627823216735)
    ·
      refine ⟨33394186516830941734825103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22262791011220627823216735 33394186516830941734825103)
      ·
        refine ⟨50091279775246412602237655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33394186516830941734825103 50091279775246412602237655)
        ·
          refine ⟨75136919662869618903356483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50091279775246412602237655 75136919662869618903356483)
          ·
            refine ⟨112705379494304428355034725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75136919662869618903356483 112705379494304428355034725)
            ·
              refine ⟨21132258655182080316569011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112705379494304428355034725 21132258655182080316569011)
              ·
                refine ⟨31698387982773120474853517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21132258655182080316569011 31698387982773120474853517)
                ·
                  refine ⟨11886895493539920178070069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31698387982773120474853517 11886895493539920178070069)
                  ·
                    refine ⟨1114396452519367516694069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11886895493539920178070069 1114396452519367516694069)
                    ·
                      rfl

theorem cell23_6510838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_6510838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510838 prefixEnd_6510838 := by exact prefixLift 6510838
  have htrace : WordTrace (prefixWord ++ tailWord_6510838) baseStart_6510838 baseEnd_6510838 := by
    simpa [prefixWord, tailWord_6510838, baseEnd_6510838] using wordTrace_append hprefix tailTrace_6510838
  have hstable : (prefixWord ++ tailWord_6510838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510838).length < 2 ^ (prefixWord ++ tailWord_6510838).sum := by decide
  have hdescent : baseEnd_6510838 < baseStart_6510838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510851 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 1, 6]
def baseStart_6510851 : Nat := 118140960795 + 6510851 * 2 ^ 59
def prefixEnd_6510851 : Nat := 4983230072969 + 3 ^ 40 * 6510851 * 2
def baseEnd_6510851 : Nat := 1114398677602203666406549

theorem tailTrace_6510851 : CollatzResearch.WordTrace tailWord_6510851 prefixEnd_6510851 1114398677602203666406549 := by
  unfold tailWord_6510851
  simp only [CollatzResearch.WordTrace]
  refine ⟨237470244935306266667868407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158313496623537511111912271 237470244935306266667868407)
  ·
    refine ⟨356205367402959400001802611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237470244935306266667868407 356205367402959400001802611)
    ·
      refine ⟨534308051104439100002703917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356205367402959400001802611 534308051104439100002703917)
      ·
        refine ⟨200365519164164662501013969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534308051104439100002703917 200365519164164662501013969)
        ·
          refine ⟨150274139373123496875760477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200365519164164662501013969 150274139373123496875760477)
          ·
            refine ⟨56352802264921311328410179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150274139373123496875760477 56352802264921311328410179)
            ·
              refine ⟨84529203397381966992615269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56352802264921311328410179 84529203397381966992615269)
              ·
                refine ⟨15849225637009118811115363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84529203397381966992615269 15849225637009118811115363)
                ·
                  refine ⟨23773838455513678216673045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15849225637009118811115363 23773838455513678216673045)
                  ·
                    refine ⟨1114398677602203666406549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23773838455513678216673045 1114398677602203666406549)
                    ·
                      rfl

theorem cell23_6510851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 6].length) (baseStart_6510851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510851 prefixEnd_6510851 := by exact prefixLift 6510851
  have htrace : WordTrace (prefixWord ++ tailWord_6510851) baseStart_6510851 baseEnd_6510851 := by
    simpa [prefixWord, tailWord_6510851, baseEnd_6510851] using wordTrace_append hprefix tailTrace_6510851
  have hstable : (prefixWord ++ tailWord_6510851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510851).length < 2 ^ (prefixWord ++ tailWord_6510851).sum := by decide
  have hdescent : baseEnd_6510851 < baseStart_6510851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510875 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 3, 2, 2]
def baseStart_6510875 : Nat := 118140960795 + 6510875 * 2 ^ 59
def prefixEnd_6510875 : Nat := 4983230072969 + 3 ^ 40 * 6510875 * 2
def baseEnd_6510875 : Nat := 3343208356342318905319537

theorem tailTrace_6510875 : CollatzResearch.WordTrace tailWord_6510875 prefixEnd_6510875 3343208356342318905319537 := by
  unfold tailWord_6510875
  simp only [CollatzResearch.WordTrace]
  refine ⟨237471120287219318766742079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158314080191479545844494719 237471120287219318766742079)
  ·
    refine ⟨356206680430828978150113119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237471120287219318766742079 356206680430828978150113119)
    ·
      refine ⟨534310020646243467225169679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356206680430828978150113119 534310020646243467225169679)
      ·
        refine ⟨801465030969365200837754519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534310020646243467225169679 801465030969365200837754519)
        ·
          refine ⟨1202197546454047801256631779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801465030969365200837754519 1202197546454047801256631779)
          ·
            refine ⟨1803296319681071701884947669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202197546454047801256631779 1803296319681071701884947669)
            ·
              refine ⟨42264757492525118012928461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1803296319681071701884947669 42264757492525118012928461)
              ·
                refine ⟨15849284059696919254848173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42264757492525118012928461 15849284059696919254848173)
                ·
                  refine ⟨5943481522386344720568065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15849284059696919254848173 5943481522386344720568065)
                  ·
                    refine ⟨4457611141789758540426049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5943481522386344720568065 4457611141789758540426049)
                    ·
                      refine ⟨3343208356342318905319537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457611141789758540426049 3343208356342318905319537)
                      ·
                        rfl

theorem cell23_6510875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 2, 2].length) (baseStart_6510875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510875 prefixEnd_6510875 := by exact prefixLift 6510875
  have htrace : WordTrace (prefixWord ++ tailWord_6510875) baseStart_6510875 baseEnd_6510875 := by
    simpa [prefixWord, tailWord_6510875, baseEnd_6510875] using wordTrace_append hprefix tailTrace_6510875
  have hstable : (prefixWord ++ tailWord_6510875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510875).length < 2 ^ (prefixWord ++ tailWord_6510875).sum := by decide
  have hdescent : baseEnd_6510875 < baseStart_6510875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510885 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_6510885 : Nat := 118140960795 + 6510885 * 2 ^ 59
def prefixEnd_6510885 : Nat := 4983230072969 + 3 ^ 40 * 6510885 * 2
def baseEnd_6510885 : Nat := 1114404497049621288731497

theorem tailTrace_6510885 : CollatzResearch.WordTrace tailWord_6510885 prefixEnd_6510885 1114404497049621288731497 := by
  unfold tailWord_6510885
  simp only [CollatzResearch.WordTrace]
  refine ⟨237471485017183090474606109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158314323344788726983070739 237471485017183090474606109)
  ·
    refine ⟨89051806881443658927977291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237471485017183090474606109 89051806881443658927977291)
    ·
      refine ⟨133577710322165488391965937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89051806881443658927977291 133577710322165488391965937)
      ·
        refine ⟨100183282741624116293974453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133577710322165488391965937 100183282741624116293974453)
        ·
          refine ⟨9392182757027260902560105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100183282741624116293974453 9392182757027260902560105)
          ·
            refine ⟨7044137067770445676920079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9392182757027260902560105 7044137067770445676920079)
            ·
              refine ⟨10566205601655668515380119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7044137067770445676920079 10566205601655668515380119)
              ·
                refine ⟨15849308402483502773070179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10566205601655668515380119 15849308402483502773070179)
                ·
                  refine ⟨23773962603725254159605269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15849308402483502773070179 23773962603725254159605269)
                  ·
                    refine ⟨1114404497049621288731497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23773962603725254159605269 1114404497049621288731497)
                    ·
                      rfl

theorem cell23_6510885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_6510885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510885 prefixEnd_6510885 := by exact prefixLift 6510885
  have htrace : WordTrace (prefixWord ++ tailWord_6510885) baseStart_6510885 baseEnd_6510885 := by
    simpa [prefixWord, tailWord_6510885, baseEnd_6510885] using wordTrace_append hprefix tailTrace_6510885
  have hstable : (prefixWord ++ tailWord_6510885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510885).length < 2 ^ (prefixWord ++ tailWord_6510885).sum := by decide
  have hdescent : baseEnd_6510885 < baseStart_6510885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510898 : List Nat := [3, 2, 1, 1, 5, 1, 1, 9]
def baseStart_6510898 : Nat := 118140960795 + 6510898 * 2 ^ 59
def prefixEnd_6510898 : Nat := 4983230072969 + 3 ^ 40 * 6510898 * 2
def baseEnd_6510898 : Nat := 123822969125828604271553

theorem tailTrace_6510898 : CollatzResearch.WordTrace tailWord_6510898 prefixEnd_6510898 123822969125828604271553 := by
  unfold tailWord_6510898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59367989791533998423707337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158314639444090662463219565 59367989791533998423707337)
  ·
    refine ⟨44525992343650498817780503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59367989791533998423707337 44525992343650498817780503)
    ·
      refine ⟨66788988515475748226670755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44525992343650498817780503 66788988515475748226670755)
      ·
        refine ⟨100183482773213622340006133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66788988515475748226670755 100183482773213622340006133)
        ·
          refine ⟨9392201509988777094375575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100183482773213622340006133 9392201509988777094375575)
          ·
            refine ⟨14088302264983165641563363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392201509988777094375575 14088302264983165641563363)
            ·
              refine ⟨21132453397474748462345045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14088302264983165641563363 21132453397474748462345045)
              ·
                refine ⟨123822969125828604271553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21132453397474748462345045 123822969125828604271553)
                ·
                  rfl

theorem cell23_6510898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_6510898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510898 prefixEnd_6510898 := by exact prefixLift 6510898
  have htrace : WordTrace (prefixWord ++ tailWord_6510898) baseStart_6510898 baseEnd_6510898 := by
    simpa [prefixWord, tailWord_6510898, baseEnd_6510898] using wordTrace_append hprefix tailTrace_6510898
  have hstable : (prefixWord ++ tailWord_6510898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510898).length < 2 ^ (prefixWord ++ tailWord_6510898).sum := by decide
  have hdescent : baseEnd_6510898 < baseStart_6510898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510908 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_6510908 : Nat := 118140960795 + 6510908 * 2 ^ 59
def prefixEnd_6510908 : Nat := 4983230072969 + 3 ^ 40 * 6510908 * 2
def baseEnd_6510908 : Nat := 3343225301203917276206885

theorem tailTrace_6510908 : CollatzResearch.WordTrace tailWord_6510908 prefixEnd_6510908 3343225301203917276206885 := by
  unfold tailWord_6510908
  simp only [CollatzResearch.WordTrace]
  refine ⟨118736161948049882701346689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158314882597399843601795585 118736161948049882701346689)
  ·
    refine ⟨89052121461037412026010017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118736161948049882701346689 89052121461037412026010017)
    ·
      refine ⟨66789091095778059019507513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89052121461037412026010017 66789091095778059019507513)
      ·
        refine ⟨50091818321833544264630635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66789091095778059019507513 50091818321833544264630635)
        ·
          refine ⟨75137727482750316396945953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50091818321833544264630635 75137727482750316396945953)
          ·
            refine ⟨56353295612062737297709465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75137727482750316396945953 56353295612062737297709465)
            ·
              refine ⟨42264971709047052973282099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56353295612062737297709465 42264971709047052973282099)
              ·
                refine ⟨63397457563570579459923149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42264971709047052973282099 63397457563570579459923149)
                ·
                  refine ⟨23774046586338967297471181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63397457563570579459923149 23774046586338967297471181)
                  ·
                    refine ⟨8915267469877112736551693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23774046586338967297471181 8915267469877112736551693)
                    ·
                      refine ⟨3343225301203917276206885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8915267469877112736551693 3343225301203917276206885)
                      ·
                        rfl

theorem cell23_6510908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_6510908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510908 prefixEnd_6510908 := by exact prefixLift 6510908
  have htrace : WordTrace (prefixWord ++ tailWord_6510908) baseStart_6510908 baseEnd_6510908 := by
    simpa [prefixWord, tailWord_6510908, baseEnd_6510908] using wordTrace_append hprefix tailTrace_6510908
  have hstable : (prefixWord ++ tailWord_6510908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510908).length < 2 ^ (prefixWord ++ tailWord_6510908).sum := by decide
  have hdescent : baseEnd_6510908 < baseStart_6510908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510921 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_6510921 : Nat := 118140960795 + 6510921 * 2 ^ 59
def prefixEnd_6510921 : Nat := 4983230072969 + 3 ^ 40 * 6510921 * 2
def baseEnd_6510921 : Nat := 3343231976452425725344325

theorem tailTrace_6510921 : CollatzResearch.WordTrace tailWord_6510921 prefixEnd_6510921 3343231976452425725344325 := by
  unfold tailWord_6510921
  simp only [CollatzResearch.WordTrace]
  refine ⟨237472798045052668622916617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158315198696701779081944411 237472798045052668622916617)
  ·
    refine ⟨178104598533789501467187463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237472798045052668622916617 178104598533789501467187463)
    ·
      refine ⟨267156897800684252200781195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178104598533789501467187463 267156897800684252200781195)
      ·
        refine ⟨400735346701026378301171793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267156897800684252200781195 400735346701026378301171793)
        ·
          refine ⟨300551510025769783725878845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400735346701026378301171793 300551510025769783725878845)
          ·
            refine ⟨112706816259663668897204567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300551510025769783725878845 112706816259663668897204567)
            ·
              refine ⟨169060224389495503345806851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112706816259663668897204567 169060224389495503345806851)
              ·
                refine ⟨253590336584243255018710277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169060224389495503345806851 253590336584243255018710277)
                ·
                  refine ⟨47548188109545610316008177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253590336584243255018710277 47548188109545610316008177)
                  ·
                    refine ⟨35661141082159207737006133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47548188109545610316008177 35661141082159207737006133)
                    ·
                      refine ⟨3343231976452425725344325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35661141082159207737006133 3343231976452425725344325)
                      ·
                        rfl

theorem cell23_6510921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_6510921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510921 prefixEnd_6510921 := by exact prefixLift 6510921
  have htrace : WordTrace (prefixWord ++ tailWord_6510921) baseStart_6510921 baseEnd_6510921 := by
    simpa [prefixWord, tailWord_6510921, baseEnd_6510921] using wordTrace_append hprefix tailTrace_6510921
  have hstable : (prefixWord ++ tailWord_6510921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510921).length < 2 ^ (prefixWord ++ tailWord_6510921).sum := by decide
  have hdescent : baseEnd_6510921 < baseStart_6510921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510935 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 3, 3, 2]
def baseStart_6510935 : Nat := 118140960795 + 6510935 * 2 ^ 59
def prefixEnd_6510935 : Nat := 4983230072969 + 3 ^ 40 * 6510935 * 2
def baseEnd_6510935 : Nat := 3343239165181588670569261

theorem tailTrace_6510935 : CollatzResearch.WordTrace tailWord_6510935 prefixEnd_6510935 3343239165181588670569261 := by
  unfold tailWord_6510935
  simp only [CollatzResearch.WordTrace]
  refine ⟨237473308667001949013926259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158315539111334632675950839 237473308667001949013926259)
  ·
    refine ⟨356209963000502923520889389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237473308667001949013926259 356209963000502923520889389)
    ·
      refine ⟨133578736125188596320333521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356209963000502923520889389 133578736125188596320333521)
      ·
        refine ⟨100184052093891447240250141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133578736125188596320333521 100184052093891447240250141)
        ·
          refine ⟨37569019535209292715093803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100184052093891447240250141 37569019535209292715093803)
          ·
            refine ⟨56353529302813939072640705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37569019535209292715093803 56353529302813939072640705)
            ·
              refine ⟨42265146977110454304480529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56353529302813939072640705 42265146977110454304480529)
              ·
                refine ⟨31698860232832840728360397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42265146977110454304480529 31698860232832840728360397)
                ·
                  refine ⟨11887072587312315273135149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31698860232832840728360397 11887072587312315273135149)
                  ·
                    refine ⟨4457652220242118227425681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11887072587312315273135149 4457652220242118227425681)
                    ·
                      refine ⟨3343239165181588670569261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457652220242118227425681 3343239165181588670569261)
                      ·
                        rfl

theorem cell23_6510935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_6510935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510935 prefixEnd_6510935 := by exact prefixLift 6510935
  have htrace : WordTrace (prefixWord ++ tailWord_6510935) baseStart_6510935 baseEnd_6510935 := by
    simpa [prefixWord, tailWord_6510935, baseEnd_6510935] using wordTrace_append hprefix tailTrace_6510935
  have hstable : (prefixWord ++ tailWord_6510935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510935).length < 2 ^ (prefixWord ++ tailWord_6510935).sum := by decide
  have hdescent : baseEnd_6510935 < baseStart_6510935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6510952 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6510952 : Nat := 118140960795 + 6510952 * 2 ^ 59
def prefixEnd_6510952 : Nat := 4983230072969 + 3 ^ 40 * 6510952 * 2
def baseEnd_6510952 : Nat := 3343247894352715104056683

theorem tailTrace_6510952 : CollatzResearch.WordTrace tailWord_6510952 prefixEnd_6510952 3343247894352715104056683 := by
  unfold tailWord_6510952
  simp only [CollatzResearch.WordTrace]
  refine ⟨118736964353970180458647555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158315952471960240611530073 118736964353970180458647555)
  ·
    refine ⟨178105446530955270687971333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118736964353970180458647555 178105446530955270687971333)
    ·
      refine ⟨33394771224554113253994625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178105446530955270687971333 33394771224554113253994625)
      ·
        refine ⟨25046078418415584940495969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33394771224554113253994625 25046078418415584940495969)
        ·
          refine ⟨18784558813811688705371977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25046078418415584940495969 18784558813811688705371977)
          ·
            refine ⟨14088419110358766529028983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18784558813811688705371977 14088419110358766529028983)
            ·
              refine ⟨21132628665538149793543475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14088419110358766529028983 21132628665538149793543475)
              ·
                refine ⟨31698942998307224690315213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21132628665538149793543475 31698942998307224690315213)
                ·
                  refine ⟨11887103624365209258868205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31698942998307224690315213 11887103624365209258868205)
                  ·
                    refine ⟨4457663859136953472075577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11887103624365209258868205 4457663859136953472075577)
                    ·
                      refine ⟨3343247894352715104056683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457663859136953472075577 3343247894352715104056683)
                      ·
                        rfl

theorem cell23_6510952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6510952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6510952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6510952 prefixEnd_6510952 := by exact prefixLift 6510952
  have htrace : WordTrace (prefixWord ++ tailWord_6510952) baseStart_6510952 baseEnd_6510952 := by
    simpa [prefixWord, tailWord_6510952, baseEnd_6510952] using wordTrace_append hprefix tailTrace_6510952
  have hstable : (prefixWord ++ tailWord_6510952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6510952).length < 2 ^ (prefixWord ++ tailWord_6510952).sum := by decide
  have hdescent : baseEnd_6510952 < baseStart_6510952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6510952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511005 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 7]
def baseStart_6511005 : Nat := 118140960795 + 6511005 * 2 ^ 59
def prefixEnd_6511005 : Nat := 4983230072969 + 3 ^ 40 * 6511005 * 2
def baseEnd_6511005 : Nat := 371475012091933710743771

theorem tailTrace_6511005 : CollatzResearch.WordTrace tailWord_6511005 prefixEnd_6511005 371475012091933710743771 := by
  unfold tailWord_6511005
  simp only [CollatzResearch.WordTrace]
  refine ⟨237475861776748350968974469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158317241184498900645982979 237475861776748350968974469)
  ·
    refine ⟨44526724083140315806682713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237475861776748350968974469 44526724083140315806682713)
    ·
      refine ⟨33395043062355236855012035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44526724083140315806682713 33395043062355236855012035)
      ·
        refine ⟨50092564593532855282518053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33395043062355236855012035 50092564593532855282518053)
        ·
          refine ⟨9392355861287410365472135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50092564593532855282518053 9392355861287410365472135)
          ·
            refine ⟨14088533791931115548208203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392355861287410365472135 14088533791931115548208203)
            ·
              refine ⟨21132800687896673322312305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14088533791931115548208203 21132800687896673322312305)
              ·
                refine ⟨15849600515922504991734229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21132800687896673322312305 15849600515922504991734229)
                ·
                  refine ⟨371475012091933710743771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15849600515922504991734229 371475012091933710743771)
                  ·
                    rfl

theorem cell23_6511005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_6511005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511005 prefixEnd_6511005 := by exact prefixLift 6511005
  have htrace : WordTrace (prefixWord ++ tailWord_6511005) baseStart_6511005 baseEnd_6511005 := by
    simpa [prefixWord, tailWord_6511005, baseEnd_6511005] using wordTrace_append hprefix tailTrace_6511005
  have hstable : (prefixWord ++ tailWord_6511005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511005).length < 2 ^ (prefixWord ++ tailWord_6511005).sum := by decide
  have hdescent : baseEnd_6511005 < baseStart_6511005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511065 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 3, 4]
def baseStart_6511065 : Nat := 118140960795 + 6511065 * 2 ^ 59
def prefixEnd_6511065 : Nat := 4983230072969 + 3 ^ 40 * 6511065 * 2
def baseEnd_6511065 : Nat := 1114435305888891053981221

theorem tailTrace_6511065 : CollatzResearch.WordTrace tailWord_6511065 prefixEnd_6511065 1114435305888891053981221 := by
  unfold tailWord_6511065
  simp only [CollatzResearch.WordTrace]
  refine ⟨237478050156530981216158649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158318700104353987477439099 237478050156530981216158649)
  ·
    refine ⟨178108537617398235912118987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237478050156530981216158649 178108537617398235912118987)
    ·
      refine ⟨267162806426097353868178481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178108537617398235912118987 267162806426097353868178481)
      ·
        refine ⟨200372104819573015401133861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267162806426097353868178481 200372104819573015401133861)
        ·
          refine ⟨37569769653669940387712599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200372104819573015401133861 37569769653669940387712599)
          ·
            refine ⟨56354654480504910581568899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37569769653669940387712599 56354654480504910581568899)
            ·
              refine ⟨84531981720757365872353349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56354654480504910581568899 84531981720757365872353349)
              ·
                refine ⟨15849746572642006101066253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84531981720757365872353349 15849746572642006101066253)
                ·
                  refine ⟨5943654964740752287899845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15849746572642006101066253 5943654964740752287899845)
                  ·
                    refine ⟨1114435305888891053981221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943654964740752287899845 1114435305888891053981221)
                    ·
                      rfl

theorem cell23_6511065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_6511065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511065 prefixEnd_6511065 := by exact prefixLift 6511065
  have htrace : WordTrace (prefixWord ++ tailWord_6511065) baseStart_6511065 baseEnd_6511065 := by
    simpa [prefixWord, tailWord_6511065, baseEnd_6511065] using wordTrace_append hprefix tailTrace_6511065
  have hstable : (prefixWord ++ tailWord_6511065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511065).length < 2 ^ (prefixWord ++ tailWord_6511065).sum := by decide
  have hdescent : baseEnd_6511065 < baseStart_6511065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511098 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_6511098 : Nat := 118140960795 + 6511098 * 2 ^ 59
def prefixEnd_6511098 : Nat := 4983230072969 + 3 ^ 40 * 6511098 * 2
def baseEnd_6511098 : Nat := 3343322862528271532831011

theorem tailTrace_6511098 : CollatzResearch.WordTrace tailWord_6511098 prefixEnd_6511098 3343322862528271532831011 := by
  unfold tailWord_6511098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59369813441352856963027487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158319502510274285234739965 59369813441352856963027487)
  ·
    refine ⟨89054720162029285444541231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59369813441352856963027487 89054720162029285444541231)
    ·
      refine ⟨133582080243043928166811847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89054720162029285444541231 133582080243043928166811847)
      ·
        refine ⟨200373120364565892250217771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133582080243043928166811847 200373120364565892250217771)
        ·
          refine ⟨300559680546848838375326657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200373120364565892250217771 300559680546848838375326657)
          ·
            refine ⟨225419760410136628781494993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300559680546848838375326657 225419760410136628781494993)
            ·
              refine ⟨169064820307602471586121245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225419760410136628781494993 169064820307602471586121245)
              ·
                refine ⟨63399307615350926844795467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169064820307602471586121245 63399307615350926844795467)
                ·
                  refine ⟨95098961423026390267193201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63399307615350926844795467 95098961423026390267193201)
                  ·
                    refine ⟨71324221067269792700394901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95098961423026390267193201 71324221067269792700394901)
                    ·
                      refine ⟨3343322862528271532831011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71324221067269792700394901 3343322862528271532831011)
                      ·
                        rfl

theorem cell23_6511098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_6511098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511098 prefixEnd_6511098 := by exact prefixLift 6511098
  have htrace : WordTrace (prefixWord ++ tailWord_6511098) baseStart_6511098 baseEnd_6511098 := by
    simpa [prefixWord, tailWord_6511098, baseEnd_6511098] using wordTrace_append hprefix tailTrace_6511098
  have hstable : (prefixWord ++ tailWord_6511098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511098).length < 2 ^ (prefixWord ++ tailWord_6511098).sum := by decide
  have hdescent : baseEnd_6511098 < baseStart_6511098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511125 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_6511125 : Nat := 118140960795 + 6511125 * 2 ^ 59
def prefixEnd_6511125 : Nat := 4983230072969 + 3 ^ 40 * 6511125 * 2
def baseEnd_6511125 : Nat := 1114445575501980975731129

theorem tailTrace_6511125 : CollatzResearch.WordTrace tailWord_6511125 prefixEnd_6511125 1114445575501980975731129 := by
  unfold tailWord_6511125
  simp only [CollatzResearch.WordTrace]
  refine ⟨237480238536313611463342829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158320159024209074308895219 237480238536313611463342829)
  ·
    refine ⟨89055089451117604298753561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237480238536313611463342829 89055089451117604298753561)
    ·
      refine ⟨66791317088338203224065171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89055089451117604298753561 66791317088338203224065171)
      ·
        refine ⟨100186975632507304836097757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66791317088338203224065171 100186975632507304836097757)
        ·
          refine ⟨37570115862190239313536659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100186975632507304836097757 37570115862190239313536659)
          ·
            refine ⟨56355173793285358970304989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37570115862190239313536659 56355173793285358970304989)
            ·
              refine ⟨21133190172482009613864371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56355173793285358970304989 21133190172482009613864371)
              ·
                refine ⟨31699785258723014420796557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21133190172482009613864371 31699785258723014420796557)
                ·
                  refine ⟨11887419472021130407798709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31699785258723014420796557 11887419472021130407798709)
                  ·
                    refine ⟨1114445575501980975731129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11887419472021130407798709 1114445575501980975731129)
                    ·
                      rfl

theorem cell23_6511125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_6511125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511125 prefixEnd_6511125 := by exact prefixLift 6511125
  have htrace : WordTrace (prefixWord ++ tailWord_6511125) baseStart_6511125 baseEnd_6511125 := by
    simpa [prefixWord, tailWord_6511125, baseEnd_6511125] using wordTrace_append hprefix tailTrace_6511125
  have hstable : (prefixWord ++ tailWord_6511125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511125).length < 2 ^ (prefixWord ++ tailWord_6511125).sum := by decide
  have hdescent : baseEnd_6511125 < baseStart_6511125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511150 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6511150 : Nat := 118140960795 + 6511150 * 2 ^ 59
def prefixEnd_6511150 : Nat := 4983230072969 + 3 ^ 40 * 6511150 * 2
def baseEnd_6511150 : Nat := 1114449854507435109793591

theorem tailTrace_6511150 : CollatzResearch.WordTrace tailWord_6511150 prefixEnd_6511150 1114449854507435109793591 := by
  unfold tailWord_6511150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29685143795152880091625363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158320766907482027155335269 29685143795152880091625363)
  ·
    refine ⟨44527715692729320137438045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29685143795152880091625363 44527715692729320137438045)
    ·
      refine ⟨16697893384773495051539267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44527715692729320137438045 16697893384773495051539267)
      ·
        refine ⟨25046840077160242577308901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16697893384773495051539267 25046840077160242577308901)
        ·
          refine ⟨4696282514467545483245419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25046840077160242577308901 4696282514467545483245419)
          ·
            refine ⟨7044423771701318224868129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696282514467545483245419 7044423771701318224868129)
            ·
              refine ⟨5283317828775988668651097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7044423771701318224868129 5283317828775988668651097)
              ·
                refine ⟨3962488371581991501488323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5283317828775988668651097 3962488371581991501488323)
                ·
                  refine ⟨5943732557372987252232485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962488371581991501488323 5943732557372987252232485)
                  ·
                    refine ⟨1114449854507435109793591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943732557372987252232485 1114449854507435109793591)
                    ·
                      rfl

theorem cell23_6511150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6511150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511150 prefixEnd_6511150 := by exact prefixLift 6511150
  have htrace : WordTrace (prefixWord ++ tailWord_6511150) baseStart_6511150 baseEnd_6511150 := by
    simpa [prefixWord, tailWord_6511150, baseEnd_6511150] using wordTrace_append hprefix tailTrace_6511150
  have hstable : (prefixWord ++ tailWord_6511150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511150).length < 2 ^ (prefixWord ++ tailWord_6511150).sum := by decide
  have hdescent : baseEnd_6511150 < baseStart_6511150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511182 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_6511182 : Nat := 118140960795 + 6511182 * 2 ^ 59
def prefixEnd_6511182 : Nat := 4983230072969 + 3 ^ 40 * 6511182 * 2
def baseEnd_6511182 : Nat := 3343365994903249204180625

theorem tailTrace_6511182 : CollatzResearch.WordTrace tailWord_6511182 prefixEnd_6511182 3343365994903249204180625 := by
  unfold tailWord_6511182
  simp only [CollatzResearch.WordTrace]
  refine ⟨29685289687138388774770975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158321544998071406798778533 29685289687138388774770975)
  ·
    refine ⟨44527934530707583162156463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29685289687138388774770975 44527934530707583162156463)
    ·
      refine ⟨66791901796061374743234695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44527934530707583162156463 66791901796061374743234695)
      ·
        refine ⟨100187852694092062114852043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66791901796061374743234695 100187852694092062114852043)
        ·
          refine ⟨150281779041138093172278065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100187852694092062114852043 150281779041138093172278065)
          ·
            refine ⟨112711334280853569879208549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150281779041138093172278065 112711334280853569879208549)
            ·
              refine ⟨21133375177660044352351603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112711334280853569879208549 21133375177660044352351603)
              ·
                refine ⟨31700062766490066528527405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21133375177660044352351603 31700062766490066528527405)
                ·
                  refine ⟨11887523537433774948197777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31700062766490066528527405 11887523537433774948197777)
                  ·
                    refine ⟨8915642653075331211148333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11887523537433774948197777 8915642653075331211148333)
                    ·
                      refine ⟨3343365994903249204180625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8915642653075331211148333 3343365994903249204180625)
                      ·
                        rfl

theorem cell23_6511182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_6511182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511182 prefixEnd_6511182 := by exact prefixLift 6511182
  have htrace : WordTrace (prefixWord ++ tailWord_6511182) baseStart_6511182 baseEnd_6511182 := by
    simpa [prefixWord, tailWord_6511182, baseEnd_6511182] using wordTrace_append hprefix tailTrace_6511182
  have hstable : (prefixWord ++ tailWord_6511182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511182).length < 2 ^ (prefixWord ++ tailWord_6511182).sum := by decide
  have hdescent : baseEnd_6511182 < baseStart_6511182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511213 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_6511213 : Nat := 118140960795 + 6511213 * 2 ^ 59
def prefixEnd_6511213 : Nat := 4983230072969 + 3 ^ 40 * 6511213 * 2
def baseEnd_6511213 : Nat := 3343381912803538582892983

theorem tailTrace_6511213 : CollatzResearch.WordTrace tailWord_6511213 prefixEnd_6511213 3343381912803538582892983 := by
  unfold tailWord_6511213
  simp only [CollatzResearch.WordTrace]
  refine ⟨237483448159994802492546293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158322298773329868328364195 237483448159994802492546293)
  ·
    refine ⟨22264073264999512733676215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237483448159994802492546293 22264073264999512733676215)
    ·
      refine ⟨33396109897499269100514323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22264073264999512733676215 33396109897499269100514323)
      ·
        refine ⟨50094164846248903650771485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33396109897499269100514323 50094164846248903650771485)
        ·
          refine ⟨18785311817343338869039307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50094164846248903650771485 18785311817343338869039307)
          ·
            refine ⟨28177967726015008303558961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18785311817343338869039307 28177967726015008303558961)
            ·
              refine ⟨21133475794511256227669221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28177967726015008303558961 21133475794511256227669221)
              ·
                refine ⟨3962526711470860542687979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21133475794511256227669221 3962526711470860542687979)
                ·
                  refine ⟨5943790067206290814031969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962526711470860542687979 5943790067206290814031969)
                  ·
                    refine ⟨4457842550404718110523977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5943790067206290814031969 4457842550404718110523977)
                    ·
                      refine ⟨3343381912803538582892983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457842550404718110523977 3343381912803538582892983)
                      ·
                        rfl

theorem cell23_6511213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_6511213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511213 prefixEnd_6511213 := by exact prefixLift 6511213
  have htrace : WordTrace (prefixWord ++ tailWord_6511213) baseStart_6511213 baseEnd_6511213 := by
    simpa [prefixWord, tailWord_6511213, baseEnd_6511213] using wordTrace_append hprefix tailTrace_6511213
  have hstable : (prefixWord ++ tailWord_6511213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511213).length < 2 ^ (prefixWord ++ tailWord_6511213).sum := by decide
  have hdescent : baseEnd_6511213 < baseStart_6511213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511235 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4]
def baseStart_6511235 : Nat := 118140960795 + 6511235 * 2 ^ 59
def prefixEnd_6511235 : Nat := 4983230072969 + 3 ^ 40 * 6511235 * 2
def baseEnd_6511235 : Nat := 3343393209377937496817881

theorem tailTrace_6511235 : CollatzResearch.WordTrace tailWord_6511235 prefixEnd_6511235 3343393209377937496817881 := by
  unfold tailWord_6511235
  simp only [CollatzResearch.WordTrace]
  refine ⟨237484250565915100249847159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158322833710610066833231439 237484250565915100249847159)
  ·
    refine ⟨356226375848872650374770739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237484250565915100249847159 356226375848872650374770739)
    ·
      refine ⟨534339563773308975562156109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356226375848872650374770739 534339563773308975562156109)
      ·
        refine ⟨200377336414990865835808541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534339563773308975562156109 200377336414990865835808541)
        ·
          refine ⟨75141501155621574688428203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200377336414990865835808541 75141501155621574688428203)
          ·
            refine ⟨112712251733432362032642305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75141501155621574688428203 112712251733432362032642305)
            ·
              refine ⟨84534188800074271524481729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112712251733432362032642305 84534188800074271524481729)
              ·
                refine ⟨63400641600055703643361297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84534188800074271524481729 63400641600055703643361297)
                ·
                  refine ⟨47550481200041777732520973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63400641600055703643361297 47550481200041777732520973)
                  ·
                    refine ⟨17831430450015666649695365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47550481200041777732520973 17831430450015666649695365)
                    ·
                      refine ⟨3343393209377937496817881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17831430450015666649695365 3343393209377937496817881)
                      ·
                        rfl

theorem cell23_6511235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_6511235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511235 prefixEnd_6511235 := by exact prefixLift 6511235
  have htrace : WordTrace (prefixWord ++ tailWord_6511235) baseStart_6511235 baseEnd_6511235 := by
    simpa [prefixWord, tailWord_6511235, baseEnd_6511235] using wordTrace_append hprefix tailTrace_6511235
  have hstable : (prefixWord ++ tailWord_6511235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511235).length < 2 ^ (prefixWord ++ tailWord_6511235).sum := by decide
  have hdescent : baseEnd_6511235 < baseStart_6511235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511322 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_6511322 : Nat := 118140960795 + 6511322 * 2 ^ 59
def prefixEnd_6511322 : Nat := 4983230072969 + 3 ^ 40 * 6511322 * 2
def baseEnd_6511322 : Nat := 1114479294064959552143327

theorem tailTrace_6511322 : CollatzResearch.WordTrace tailWord_6511322 prefixEnd_6511322 1114479294064959552143327 := by
  unfold tailWord_6511322
  simp only [CollatzResearch.WordTrace]
  refine ⟨59371855929149978527066055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158324949144399942738842813 59371855929149978527066055)
  ·
    refine ⟨89057783893724967790599083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59371855929149978527066055 89057783893724967790599083)
    ·
      refine ⟨133586675840587451685898625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89057783893724967790599083 133586675840587451685898625)
      ·
        refine ⟨100190006880440588764423969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133586675840587451685898625 100190006880440588764423969)
        ·
          refine ⟨75142505160330441573317977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100190006880440588764423969 75142505160330441573317977)
          ·
            refine ⟨56356878870247831179988483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75142505160330441573317977 56356878870247831179988483)
            ·
              refine ⟨84535318305371746769982725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56356878870247831179988483 84535318305371746769982725)
              ·
                refine ⟨15850372182257202519371761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84535318305371746769982725 15850372182257202519371761)
                ·
                  refine ⟨11887779136692901889528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15850372182257202519371761 11887779136692901889528821)
                  ·
                    refine ⟨1114479294064959552143327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11887779136692901889528821 1114479294064959552143327)
                    ·
                      rfl

theorem cell23_6511322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_6511322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511322 prefixEnd_6511322 := by exact prefixLift 6511322
  have htrace : WordTrace (prefixWord ++ tailWord_6511322) baseStart_6511322 baseEnd_6511322 := by
    simpa [prefixWord, tailWord_6511322, baseEnd_6511322] using wordTrace_append hprefix tailTrace_6511322
  have hstable : (prefixWord ++ tailWord_6511322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511322).length < 2 ^ (prefixWord ++ tailWord_6511322).sum := by decide
  have hdescent : baseEnd_6511322 < baseStart_6511322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511329 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_6511329 : Nat := 118140960795 + 6511329 * 2 ^ 59
def prefixEnd_6511329 : Nat := 4983230072969 + 3 ^ 40 * 6511329 * 2
def baseEnd_6511329 : Nat := 3343441476559460129042449

theorem tailTrace_6511329 : CollatzResearch.WordTrace tailWord_6511329 prefixEnd_6511329 3343441476559460129042449 := by
  unfold tailWord_6511329
  simp only [CollatzResearch.WordTrace]
  refine ⟨237487679027574554303769041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158325119351716369535846027 237487679027574554303769041)
  ·
    refine ⟨178115759270680915727826781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237487679027574554303769041 178115759270680915727826781)
    ·
      refine ⟨66793409726505343397935043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178115759270680915727826781 66793409726505343397935043)
      ·
        refine ⟨100190114589758015096902565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66793409726505343397935043 100190114589758015096902565)
        ·
          refine ⟨18785646485579627830669231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100190114589758015096902565 18785646485579627830669231)
          ·
            refine ⟨28178469728369441746003847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18785646485579627830669231 28178469728369441746003847)
            ·
              refine ⟨42267704592554162619005771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28178469728369441746003847 42267704592554162619005771)
              ·
                refine ⟨63401556888831243928508657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42267704592554162619005771 63401556888831243928508657)
                ·
                  refine ⟨47551167666623432946381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63401556888831243928508657 47551167666623432946381493)
                  ·
                    refine ⟨4457921968745946838723265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47551167666623432946381493 4457921968745946838723265)
                    ·
                      refine ⟨3343441476559460129042449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457921968745946838723265 3343441476559460129042449)
                      ·
                        rfl

theorem cell23_6511329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_6511329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511329 prefixEnd_6511329 := by exact prefixLift 6511329
  have htrace : WordTrace (prefixWord ++ tailWord_6511329) baseStart_6511329 baseEnd_6511329 := by
    simpa [prefixWord, tailWord_6511329, baseEnd_6511329] using wordTrace_append hprefix tailTrace_6511329
  have hstable : (prefixWord ++ tailWord_6511329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511329).length < 2 ^ (prefixWord ++ tailWord_6511329).sum := by decide
  have hdescent : baseEnd_6511329 < baseStart_6511329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511332 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_6511332 : Nat := 118140960795 + 6511332 * 2 ^ 59
def prefixEnd_6511332 : Nat := 4983230072969 + 3 ^ 40 * 6511332 * 2
def baseEnd_6511332 : Nat := 3343443017001423617304935

theorem tailTrace_6511332 : CollatzResearch.WordTrace tailWord_6511332 prefixEnd_6511332 3343443017001423617304935 := by
  unfold tailWord_6511332
  simp only [CollatzResearch.WordTrace]
  refine ⟨118743894223281842908064125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158325192297709123877418833 118743894223281842908064125)
  ·
    refine ⟨44528960333730691090524047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118743894223281842908064125 44528960333730691090524047)
    ·
      refine ⟨66793440500596036635786071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44528960333730691090524047 66793440500596036635786071)
      ·
        refine ⟨100190160750894054953679107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66793440500596036635786071 100190160750894054953679107)
        ·
          refine ⟨150285241126341082430518661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100190160750894054953679107 150285241126341082430518661)
          ·
            refine ⟨28178482711188952955722249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150285241126341082430518661 28178482711188952955722249)
            ·
              refine ⟨21133862033391714716791687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28178482711188952955722249 21133862033391714716791687)
              ·
                refine ⟨31700793050087572075187531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21133862033391714716791687 31700793050087572075187531)
                ·
                  refine ⟨47551189575131358112781297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31700793050087572075187531 47551189575131358112781297)
                  ·
                    refine ⟨35663392181348518584585973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47551189575131358112781297 35663392181348518584585973)
                    ·
                      refine ⟨3343443017001423617304935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35663392181348518584585973 3343443017001423617304935)
                      ·
                        rfl

theorem cell23_6511332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_6511332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511332 prefixEnd_6511332 := by exact prefixLift 6511332
  have htrace : WordTrace (prefixWord ++ tailWord_6511332) baseStart_6511332 baseEnd_6511332 := by
    simpa [prefixWord, tailWord_6511332, baseEnd_6511332] using wordTrace_append hprefix tailTrace_6511332
  have hstable : (prefixWord ++ tailWord_6511332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511332).length < 2 ^ (prefixWord ++ tailWord_6511332).sum := by decide
  have hdescent : baseEnd_6511332 < baseStart_6511332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511386 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_6511386 : Nat := 118140960795 + 6511386 * 2 ^ 59
def prefixEnd_6511386 : Nat := 4983230072969 + 3 ^ 40 * 6511386 * 2
def baseEnd_6511386 : Nat := 1114490248318922135343229

theorem tailTrace_6511386 : CollatzResearch.WordTrace tailWord_6511386 prefixEnd_6511386 1114490248318922135343229 := by
  unfold tailWord_6511386
  simp only [CollatzResearch.WordTrace]
  refine ⟨59372439497092013259648503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158326505325578702025729341 59372439497092013259648503)
  ·
    refine ⟨89058659245638019889472755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59372439497092013259648503 89058659245638019889472755)
    ·
      refine ⟨133587988868457029834209133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89058659245638019889472755 133587988868457029834209133)
      ·
        refine ⟨50095495825671386187828425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133587988868457029834209133 50095495825671386187828425)
        ·
          refine ⟨37571621869253539640871319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50095495825671386187828425 37571621869253539640871319)
          ·
            refine ⟨56357432803880309461306979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37571621869253539640871319 56357432803880309461306979)
            ·
              refine ⟨84536149205820464191960469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56357432803880309461306979 84536149205820464191960469)
              ·
                refine ⟨3962631994022834258998147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84536149205820464191960469 3962631994022834258998147)
                ·
                  refine ⟨5943947991034251388497221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962631994022834258998147 5943947991034251388497221)
                  ·
                    refine ⟨1114490248318922135343229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943947991034251388497221 1114490248318922135343229)
                    ·
                      rfl

theorem cell23_6511386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_6511386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511386 prefixEnd_6511386 := by exact prefixLift 6511386
  have htrace : WordTrace (prefixWord ++ tailWord_6511386) baseStart_6511386 baseEnd_6511386 := by
    simpa [prefixWord, tailWord_6511386, baseEnd_6511386] using wordTrace_append hprefix tailTrace_6511386
  have hstable : (prefixWord ++ tailWord_6511386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511386).length < 2 ^ (prefixWord ++ tailWord_6511386).sum := by decide
  have hdescent : baseEnd_6511386 < baseStart_6511386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511430 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6511430 : Nat := 118140960795 + 6511430 * 2 ^ 59
def prefixEnd_6511430 : Nat := 4983230072969 + 3 ^ 40 * 6511430 * 2
def baseEnd_6511430 : Nat := 3343493338105564233879485

theorem tailTrace_6511430 : CollatzResearch.WordTrace tailWord_6511430 prefixEnd_6511430 3343493338105564233879485 := by
  unfold tailWord_6511430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421605087506520267287367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158327575200139099035463829 7421605087506520267287367)
  ·
    refine ⟨11132407631259780400931051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7421605087506520267287367 11132407631259780400931051)
    ·
      refine ⟨16698611446889670601396577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11132407631259780400931051 16698611446889670601396577)
      ·
        refine ⟨12523958585167252951047433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16698611446889670601396577 12523958585167252951047433)
        ·
          refine ⟨9392968938875439713285575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12523958585167252951047433 9392968938875439713285575)
          ·
            refine ⟨14089453408313159569928363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392968938875439713285575 14089453408313159569928363)
            ·
              refine ⟨21134180112469739354892545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14089453408313159569928363 21134180112469739354892545)
              ·
                refine ⟨15850635084352304516169409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21134180112469739354892545 15850635084352304516169409)
                ·
                  refine ⟨11887976313264228387127057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15850635084352304516169409 11887976313264228387127057)
                  ·
                    refine ⟨8915982234948171290345293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11887976313264228387127057 8915982234948171290345293)
                    ·
                      refine ⟨3343493338105564233879485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8915982234948171290345293 3343493338105564233879485)
                      ·
                        rfl

theorem cell23_6511430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6511430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511430 prefixEnd_6511430 := by exact prefixLift 6511430
  have htrace : WordTrace (prefixWord ++ tailWord_6511430) baseStart_6511430 baseEnd_6511430 := by
    simpa [prefixWord, tailWord_6511430, baseEnd_6511430] using wordTrace_append hprefix tailTrace_6511430
  have hstable : (prefixWord ++ tailWord_6511430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511430).length < 2 ^ (prefixWord ++ tailWord_6511430).sum := by decide
  have hdescent : baseEnd_6511430 < baseStart_6511430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511436 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 4, 3, 2]
def baseStart_6511436 : Nat := 118140960795 + 6511436 * 2 ^ 59
def prefixEnd_6511436 : Nat := 4983230072969 + 3 ^ 40 * 6511436 * 2
def baseEnd_6511436 : Nat := 3343496418989491210404457

theorem tailTrace_6511436 : CollatzResearch.WordTrace tailWord_6511436 prefixEnd_6511436 3343496418989491210404457 := by
  unfold tailWord_6511436
  simp only [CollatzResearch.WordTrace]
  refine ⟨118745790819093455788957081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158327721092124607718609441 118745790819093455788957081)
  ·
    refine ⟨89059343114320091841717811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118745790819093455788957081 89059343114320091841717811)
    ·
      refine ⟨133589014671480137762576717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89059343114320091841717811 133589014671480137762576717)
      ·
        refine ⟨50095880501805051660966269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133589014671480137762576717 50095880501805051660966269)
        ·
          refine ⟨18785955188176894372862351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50095880501805051660966269 18785955188176894372862351)
          ·
            refine ⟨28178932782265341559293527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18785955188176894372862351 28178932782265341559293527)
            ·
              refine ⟨42268399173398012338940291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28178932782265341559293527 42268399173398012338940291)
              ·
                refine ⟨63402598760097018508410437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42268399173398012338940291 63402598760097018508410437)
                ·
                  refine ⟨11887987267518190970326957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63402598760097018508410437 11887987267518190970326957)
                  ·
                    refine ⟨4457995225319321613872609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11887987267518190970326957 4457995225319321613872609)
                    ·
                      refine ⟨3343496418989491210404457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4457995225319321613872609 3343496418989491210404457)
                      ·
                        rfl

theorem cell23_6511436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_6511436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511436 prefixEnd_6511436 := by exact prefixLift 6511436
  have htrace : WordTrace (prefixWord ++ tailWord_6511436) baseStart_6511436 baseEnd_6511436 := by
    simpa [prefixWord, tailWord_6511436, baseEnd_6511436] using wordTrace_append hprefix tailTrace_6511436
  have hstable : (prefixWord ++ tailWord_6511436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511436).length < 2 ^ (prefixWord ++ tailWord_6511436).sum := by decide
  have hdescent : baseEnd_6511436 < baseStart_6511436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511437 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6511437 : Nat := 118140960795 + 6511437 * 2 ^ 59
def prefixEnd_6511437 : Nat := 4983230072969 + 3 ^ 40 * 6511437 * 2
def baseEnd_6511437 : Nat := 1114498977490048568830651

theorem tailTrace_6511437 : CollatzResearch.WordTrace tailWord_6511437 prefixEnd_6511437 1114498977490048568830651 := by
  unfold tailWord_6511437
  simp only [CollatzResearch.WordTrace]
  refine ⟨237491618111183288748700565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158327745407455525832467043 237491618111183288748700565)
  ·
    refine ⟨11132419598961716660095339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237491618111183288748700565 11132419598961716660095339)
    ·
      refine ⟨16698629398442574990143009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11132419598961716660095339 16698629398442574990143009)
      ·
        refine ⟨12523972048831931242607257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16698629398442574990143009 12523972048831931242607257)
        ·
          refine ⟨9392979036623948431955443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12523972048831931242607257 9392979036623948431955443)
          ·
            refine ⟨14089468554935922647933165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9392979036623948431955443 14089468554935922647933165)
            ·
              refine ⟨5283550708100970992974937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14089468554935922647933165 5283550708100970992974937)
              ·
                refine ⟨3962663031075728244731203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5283550708100970992974937 3962663031075728244731203)
                ·
                  refine ⟨5943994546613592367096805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3962663031075728244731203 5943994546613592367096805)
                  ·
                    refine ⟨1114498977490048568830651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5943994546613592367096805 1114498977490048568830651)
                    ·
                      rfl

theorem cell23_6511437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6511437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511437 prefixEnd_6511437 := by exact prefixLift 6511437
  have htrace : WordTrace (prefixWord ++ tailWord_6511437) baseStart_6511437 baseEnd_6511437 := by
    simpa [prefixWord, tailWord_6511437, baseEnd_6511437] using wordTrace_append hprefix tailTrace_6511437
  have hstable : (prefixWord ++ tailWord_6511437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511437).length < 2 ^ (prefixWord ++ tailWord_6511437).sum := by decide
  have hdescent : baseEnd_6511437 < baseStart_6511437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511470 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_6511470 : Nat := 118140960795 + 6511470 * 2 ^ 59
def prefixEnd_6511470 : Nat := 4983230072969 + 3 ^ 40 * 6511470 * 2
def baseEnd_6511470 : Nat := 3343513877331744077379301

theorem tailTrace_6511470 : CollatzResearch.WordTrace tailWord_6511470 prefixEnd_6511470 3343513877331744077379301 := by
  unfold tailWord_6511470
  simp only [CollatzResearch.WordTrace]
  refine ⟨29686602715007966923081483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158328547813375823589767909 29686602715007966923081483)
  ·
    refine ⟨44529904072511950384622225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29686602715007966923081483 44529904072511950384622225)
    ·
      refine ⟨33397428054383962788466669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44529904072511950384622225 33397428054383962788466669)
      ·
        refine ⟨12524035520393986045675001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33397428054383962788466669 12524035520393986045675001)
        ·
          refine ⟨9393026640295489534256251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12524035520393986045675001 9393026640295489534256251)
          ·
            refine ⟨14089539960443234301384377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393026640295489534256251 14089539960443234301384377)
            ·
              refine ⟨10567154970332425726038283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14089539960443234301384377 10567154970332425726038283)
              ·
                refine ⟨15850732455498638589057425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10567154970332425726038283 15850732455498638589057425)
                ·
                  refine ⟨11888049341623978941793069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15850732455498638589057425 11888049341623978941793069)
                  ·
                    refine ⟨4458018503108992103172401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11888049341623978941793069 4458018503108992103172401)
                    ·
                      refine ⟨3343513877331744077379301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458018503108992103172401 3343513877331744077379301)
                      ·
                        rfl

theorem cell23_6511470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_6511470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511470 prefixEnd_6511470 := by exact prefixLift 6511470
  have htrace : WordTrace (prefixWord ++ tailWord_6511470) baseStart_6511470 baseEnd_6511470 := by
    simpa [prefixWord, tailWord_6511470, baseEnd_6511470] using wordTrace_append hprefix tailTrace_6511470
  have hstable : (prefixWord ++ tailWord_6511470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511470).length < 2 ^ (prefixWord ++ tailWord_6511470).sum := by decide
  have hdescent : baseEnd_6511470 < baseStart_6511470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511472 : List Nat := [2, 1, 1, 1, 4, 1, 4, 9]
def baseStart_6511472 : Nat := 118140960795 + 6511472 * 2 ^ 59
def prefixEnd_6511472 : Nat := 4983230072969 + 3 ^ 40 * 6511472 * 2
def baseEnd_6511472 : Nat := 123833885344187150724233

theorem tailTrace_6511472 : CollatzResearch.WordTrace tailWord_6511472 prefixEnd_6511472 123833885344187150724233 := by
  unfold tailWord_6511472
  simp only [CollatzResearch.WordTrace]
  refine ⟨118746447333028244863112335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158328596444037659817483113 118746447333028244863112335)
  ·
    refine ⟨178119670999542367294668503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118746447333028244863112335 178119670999542367294668503)
    ·
      refine ⟨267179506499313550942002755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178119670999542367294668503 267179506499313550942002755)
      ·
        refine ⟨400769259748970326413004133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267179506499313550942002755 400769259748970326413004133)
        ·
          refine ⟨75144236202931936202438275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400769259748970326413004133 75144236202931936202438275)
          ·
            refine ⟨112716354304397904303657413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75144236202931936202438275 112716354304397904303657413)
            ·
              refine ⟨21134316432074607056935765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112716354304397904303657413 21134316432074607056935765)
              ·
                refine ⟨123833885344187150724233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21134316432074607056935765 123833885344187150724233)
                ·
                  rfl

theorem cell23_6511472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 9].length) (baseStart_6511472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511472 prefixEnd_6511472 := by exact prefixLift 6511472
  have htrace : WordTrace (prefixWord ++ tailWord_6511472) baseStart_6511472 baseEnd_6511472 := by
    simpa [prefixWord, tailWord_6511472, baseEnd_6511472] using wordTrace_append hprefix tailTrace_6511472
  have hstable : (prefixWord ++ tailWord_6511472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511472).length < 2 ^ (prefixWord ++ tailWord_6511472).sum := by decide
  have hdescent : baseEnd_6511472 < baseStart_6511472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511510 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6511510 : Nat := 118140960795 + 6511510 * 2 ^ 59
def prefixEnd_6511510 : Nat := 4983230072969 + 3 ^ 40 * 6511510 * 2
def baseEnd_6511510 : Nat := 1114511472185974640293039

theorem tailTrace_6511510 : CollatzResearch.WordTrace tailWord_6511510 prefixEnd_6511510 1114511472185974640293039 := by
  unfold tailWord_6511510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14843392539994926388506749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158329520426612548144071989 14843392539994926388506749)
  ·
    refine ⟨5566272202498097395690031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14843392539994926388506749 5566272202498097395690031)
    ·
      refine ⟨8349408303747146093535047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5566272202498097395690031 8349408303747146093535047)
      ·
        refine ⟨12524112455620719140302571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8349408303747146093535047 12524112455620719140302571)
        ·
          refine ⟨18786168683431078710453857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524112455620719140302571 18786168683431078710453857)
          ·
            refine ⟨14089626512573309032840393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18786168683431078710453857 14089626512573309032840393)
            ·
              refine ⟨10567219884429981774630295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14089626512573309032840393 10567219884429981774630295)
              ·
                refine ⟨15850829826644972661945443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10567219884429981774630295 15850829826644972661945443)
                ·
                  refine ⟨23776244739967458992918165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15850829826644972661945443 23776244739967458992918165)
                  ·
                    refine ⟨1114511472185974640293039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23776244739967458992918165 1114511472185974640293039)
                    ·
                      rfl

theorem cell23_6511510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6511510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511510 prefixEnd_6511510 := by exact prefixLift 6511510
  have htrace : WordTrace (prefixWord ++ tailWord_6511510) baseStart_6511510 baseEnd_6511510 := by
    simpa [prefixWord, tailWord_6511510, baseEnd_6511510] using wordTrace_append hprefix tailTrace_6511510
  have hstable : (prefixWord ++ tailWord_6511510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511510).length < 2 ^ (prefixWord ++ tailWord_6511510).sum := by decide
  have hdescent : baseEnd_6511510 < baseStart_6511510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511537 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 1, 2, 3]
def baseStart_6511537 : Nat := 118140960795 + 6511537 * 2 ^ 59
def prefixEnd_6511537 : Nat := 4983230072969 + 3 ^ 40 * 6511537 * 2
def baseEnd_6511537 : Nat := 3343548280535595315241493

theorem tailTrace_6511537 : CollatzResearch.WordTrace tailWord_6511537 prefixEnd_6511537 3343548280535595315241493 := by
  unfold tailWord_6511537
  simp only [CollatzResearch.WordTrace]
  refine ⟨237495265410821005827340865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158330176940547337218227243 237495265410821005827340865)
  ·
    refine ⟨178121449058115754370505649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237495265410821005827340865 178121449058115754370505649)
    ·
      refine ⟨133591086793586815777879237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178121449058115754370505649 133591086793586815777879237)
      ·
        refine ⟨25048328773797527958352357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133591086793586815777879237 25048328773797527958352357)
        ·
          refine ⟨4696561645087036492191067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25048328773797527958352357 4696561645087036492191067)
          ·
            refine ⟨7044842467630554738286601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696561645087036492191067 7044842467630554738286601)
            ·
              refine ⟨5283631850722916053714951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7044842467630554738286601 5283631850722916053714951)
              ·
                refine ⟨7925447776084374080572427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5283631850722916053714951 7925447776084374080572427)
                ·
                  refine ⟨11888171664126561120858641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925447776084374080572427 11888171664126561120858641)
                  ·
                    refine ⟨8916128748094920840643981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11888171664126561120858641 8916128748094920840643981)
                    ·
                      refine ⟨3343548280535595315241493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8916128748094920840643981 3343548280535595315241493)
                      ·
                        rfl

theorem cell23_6511537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_6511537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511537 prefixEnd_6511537 := by exact prefixLift 6511537
  have htrace : WordTrace (prefixWord ++ tailWord_6511537) baseStart_6511537 baseEnd_6511537 := by
    simpa [prefixWord, tailWord_6511537, baseEnd_6511537] using wordTrace_append hprefix tailTrace_6511537
  have hstable : (prefixWord ++ tailWord_6511537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511537).length < 2 ^ (prefixWord ++ tailWord_6511537).sum := by decide
  have hdescent : baseEnd_6511537 < baseStart_6511537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511559 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_6511559 : Nat := 118140960795 + 6511559 * 2 ^ 59
def prefixEnd_6511559 : Nat := 4983230072969 + 3 ^ 40 * 6511559 * 2
def baseEnd_6511559 : Nat := 3343559577109994229166391

theorem tailTrace_6511559 : CollatzResearch.WordTrace tailWord_6511559 prefixEnd_6511559 3343559577109994229166391 := by
  unfold tailWord_6511559
  simp only [CollatzResearch.WordTrace]
  refine ⟨237496067816741303584641731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158330711877827535723094487 237496067816741303584641731)
  ·
    refine ⟨356244101725111955376962597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237496067816741303584641731 356244101725111955376962597)
    ·
      refine ⟨66795769073458491633180487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356244101725111955376962597 66795769073458491633180487)
      ·
        refine ⟨100193653610187737449770731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66795769073458491633180487 100193653610187737449770731)
        ·
          refine ⟨150290480415281606174656097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100193653610187737449770731 150290480415281606174656097)
          ·
            refine ⟨112717860311461204630992073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150290480415281606174656097 112717860311461204630992073)
            ·
              refine ⟨84538395233595903473244055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112717860311461204630992073 84538395233595903473244055)
              ·
                refine ⟨126807592850393855209866083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84538395233595903473244055 126807592850393855209866083)
                ·
                  refine ⟨190211389275590782814799125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126807592850393855209866083 190211389275590782814799125)
                  ·
                    refine ⟨8916158872293317944443709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 190211389275590782814799125 8916158872293317944443709)
                    ·
                      refine ⟨3343559577109994229166391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8916158872293317944443709 3343559577109994229166391)
                      ·
                        rfl

theorem cell23_6511559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_6511559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511559 prefixEnd_6511559 := by exact prefixLift 6511559
  have htrace : WordTrace (prefixWord ++ tailWord_6511559) baseStart_6511559 baseEnd_6511559 := by
    simpa [prefixWord, tailWord_6511559, baseEnd_6511559] using wordTrace_append hprefix tailTrace_6511559
  have hstable : (prefixWord ++ tailWord_6511559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511559).length < 2 ^ (prefixWord ++ tailWord_6511559).sum := by decide
  have hdescent : baseEnd_6511559 < baseStart_6511559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511569 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_6511569 : Nat := 118140960795 + 6511569 * 2 ^ 59
def prefixEnd_6511569 : Nat := 4983230072969 + 3 ^ 40 * 6511569 * 2
def baseEnd_6511569 : Nat := 3343564711916539190041345

theorem tailTrace_6511569 : CollatzResearch.WordTrace tailWord_6511569 prefixEnd_6511569 3343564711916539190041345 := by
  unfold tailWord_6511569
  simp only [CollatzResearch.WordTrace]
  refine ⟨237496432546705075292505761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158330955031136716861670507 237496432546705075292505761)
  ·
    refine ⟨178122324410028806469379321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237496432546705075292505761 178122324410028806469379321)
    ·
      refine ⟨133591743307521604852034491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178122324410028806469379321 133591743307521604852034491)
      ·
        refine ⟨200387614961282407278051737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133591743307521604852034491 200387614961282407278051737)
        ·
          refine ⟨150290711220961805458538803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200387614961282407278051737 150290711220961805458538803)
          ·
            refine ⟨225436066831442708187808205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150290711220961805458538803 225436066831442708187808205)
            ·
              refine ⟨84538525061791015570428077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225436066831442708187808205 84538525061791015570428077)
              ·
                refine ⟨31701946898171630838910529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84538525061791015570428077 31701946898171630838910529)
                ·
                  refine ⟨23776460173628723129182897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31701946898171630838910529 23776460173628723129182897)
                  ·
                    refine ⟨17832345130221542346887173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23776460173628723129182897 17832345130221542346887173)
                    ·
                      refine ⟨3343564711916539190041345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17832345130221542346887173 3343564711916539190041345)
                      ·
                        rfl

theorem cell23_6511569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_6511569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511569 prefixEnd_6511569 := by exact prefixLift 6511569
  have htrace : WordTrace (prefixWord ++ tailWord_6511569) baseStart_6511569 baseEnd_6511569 := by
    simpa [prefixWord, tailWord_6511569, baseEnd_6511569] using wordTrace_append hprefix tailTrace_6511569
  have hstable : (prefixWord ++ tailWord_6511569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511569).length < 2 ^ (prefixWord ++ tailWord_6511569).sum := by decide
  have hdescent : baseEnd_6511569 < baseStart_6511569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511659 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_6511659 : Nat := 118140960795 + 6511659 * 2 ^ 59
def prefixEnd_6511659 : Nat := 4983230072969 + 3 ^ 40 * 6511659 * 2
def baseEnd_6511659 : Nat := 3343610925175443837915931

theorem tailTrace_6511659 : CollatzResearch.WordTrace tailWord_6511659 prefixEnd_6511659 3343610925175443837915931 := by
  unfold tailWord_6511659
  simp only [CollatzResearch.WordTrace]
  refine ⟨237499715116379020663282031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158333143410919347108854687 237499715116379020663282031)
  ·
    refine ⟨356249572674568530994923047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237499715116379020663282031 356249572674568530994923047)
    ·
      refine ⟨534374359011852796492384571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356249572674568530994923047 534374359011852796492384571)
      ·
        refine ⟨801561538517779194738576857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534374359011852796492384571 801561538517779194738576857)
        ·
          refine ⟨601171153888334396053932643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 801561538517779194738576857 601171153888334396053932643)
          ·
            refine ⟨901756730832501594080898965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601171153888334396053932643 901756730832501594080898965)
            ·
              refine ⟨42269846757773512222542139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 901756730832501594080898965 42269846757773512222542139)
              ·
                refine ⟨63404770136660268333813209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42269846757773512222542139 63404770136660268333813209)
                ·
                  refine ⟨47553577602495201250359907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63404770136660268333813209 47553577602495201250359907)
                  ·
                    refine ⟨71330366403742801875539861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47553577602495201250359907 71330366403742801875539861)
                    ·
                      refine ⟨3343610925175443837915931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71330366403742801875539861 3343610925175443837915931)
                      ·
                        rfl

theorem cell23_6511659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_6511659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511659 prefixEnd_6511659 := by exact prefixLift 6511659
  have htrace : WordTrace (prefixWord ++ tailWord_6511659) baseStart_6511659 baseEnd_6511659 := by
    simpa [prefixWord, tailWord_6511659, baseEnd_6511659] using wordTrace_append hprefix tailTrace_6511659
  have hstable : (prefixWord ++ tailWord_6511659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511659).length < 2 ^ (prefixWord ++ tailWord_6511659).sum := by decide
  have hdescent : baseEnd_6511659 < baseStart_6511659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511689 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_6511689 : Nat := 118140960795 + 6511689 * 2 ^ 59
def prefixEnd_6511689 : Nat := 4983230072969 + 3 ^ 40 * 6511689 * 2
def baseEnd_6511689 : Nat := 3343626329595078720540793

theorem tailTrace_6511689 : CollatzResearch.WordTrace tailWord_6511689 prefixEnd_6511689 3343626329595078720540793 := by
  unfold tailWord_6511689
  simp only [CollatzResearch.WordTrace]
  refine ⟨237500809306270335786874121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158333872870846890524582747 237500809306270335786874121)
  ·
    refine ⟨178125606979702751840155591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237500809306270335786874121 178125606979702751840155591)
    ·
      refine ⟨267188410469554127760233387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178125606979702751840155591 267188410469554127760233387)
      ·
        refine ⟨400782615704331191640350081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267188410469554127760233387 400782615704331191640350081)
        ·
          refine ⟨300586961778248393730262561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400782615704331191640350081 300586961778248393730262561)
          ·
            refine ⟨225440221333686295297696921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300586961778248393730262561 225440221333686295297696921)
            ·
              refine ⟨169080166000264721473272691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225440221333686295297696921 169080166000264721473272691)
              ·
                refine ⟨253620249000397082209909037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169080166000264721473272691 253620249000397082209909037)
                ·
                  refine ⟨95107593375148905828715889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253620249000397082209909037 95107593375148905828715889)
                  ·
                    refine ⟨71330695031361679371536917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95107593375148905828715889 71330695031361679371536917)
                    ·
                      refine ⟨3343626329595078720540793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71330695031361679371536917 3343626329595078720540793)
                      ·
                        rfl

theorem cell23_6511689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_6511689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511689 prefixEnd_6511689 := by exact prefixLift 6511689
  have htrace : WordTrace (prefixWord ++ tailWord_6511689) baseStart_6511689 baseEnd_6511689 := by
    simpa [prefixWord, tailWord_6511689, baseEnd_6511689] using wordTrace_append hprefix tailTrace_6511689
  have hstable : (prefixWord ++ tailWord_6511689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511689).length < 2 ^ (prefixWord ++ tailWord_6511689).sum := by decide
  have hdescent : baseEnd_6511689 < baseStart_6511689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511710 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6511710 : Nat := 118140960795 + 6511710 * 2 ^ 59
def prefixEnd_6511710 : Nat := 4983230072969 + 3 ^ 40 * 6511710 * 2
def baseEnd_6511710 : Nat := 3343637112688823138378197

theorem tailTrace_6511710 : CollatzResearch.WordTrace tailWord_6511710 prefixEnd_6511710 3343637112688823138378197 := by
  unfold tailWord_6511710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29687696904899282046673573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158334383492796170915592389 29687696904899282046673573)
  ·
    refine ⟨5566443169668615383751295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29687696904899282046673573 5566443169668615383751295)
    ·
      refine ⟨8349664754502923075626943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5566443169668615383751295 8349664754502923075626943)
      ·
        refine ⟨12524497131754384613440415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8349664754502923075626943 12524497131754384613440415)
        ·
          refine ⟨18786745697631576920160623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524497131754384613440415 18786745697631576920160623)
          ·
            refine ⟨28180118546447365380240935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18786745697631576920160623 28180118546447365380240935)
            ·
              refine ⟨42270177819671048070361403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28180118546447365380240935 42270177819671048070361403)
              ·
                refine ⟨63405266729506572105542105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42270177819671048070361403 63405266729506572105542105)
                ·
                  refine ⟨47553950047129929079156579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63405266729506572105542105 47553950047129929079156579)
                  ·
                    refine ⟨71330925070694893618734869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47553950047129929079156579 71330925070694893618734869)
                    ·
                      refine ⟨3343637112688823138378197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71330925070694893618734869 3343637112688823138378197)
                      ·
                        rfl

theorem cell23_6511710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6511710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511710 prefixEnd_6511710 := by exact prefixLift 6511710
  have htrace : WordTrace (prefixWord ++ tailWord_6511710) baseStart_6511710 baseEnd_6511710 := by
    simpa [prefixWord, tailWord_6511710, baseEnd_6511710] using wordTrace_append hprefix tailTrace_6511710
  have hstable : (prefixWord ++ tailWord_6511710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511710).length < 2 ^ (prefixWord ++ tailWord_6511710).sum := by decide
  have hdescent : baseEnd_6511710 < baseStart_6511710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511730 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_6511730 : Nat := 118140960795 + 6511730 * 2 ^ 59
def prefixEnd_6511730 : Nat := 4983230072969 + 3 ^ 40 * 6511730 * 2
def baseEnd_6511730 : Nat := 3343647382301913060128105

theorem tailTrace_6511730 : CollatzResearch.WordTrace tailWord_6511730 prefixEnd_6511730 3343647382301913060128105 := by
  unfold tailWord_6511730
  simp only [CollatzResearch.WordTrace]
  refine ⟨59375576174780449947279161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158334869799414533192744429 59375576174780449947279161)
  ·
    refine ⟨44531682131085337460459371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59375576174780449947279161 44531682131085337460459371)
    ·
      refine ⟨66797523196628006190689057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44531682131085337460459371 66797523196628006190689057)
      ·
        refine ⟨50098142397471004643016793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66797523196628006190689057 50098142397471004643016793)
        ·
          refine ⟨37573606798103253482262595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50098142397471004643016793 37573606798103253482262595)
          ·
            refine ⟨56360410197154880223393893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37573606798103253482262595 56360410197154880223393893)
            ·
              refine ⟨10567576911966540041886355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56360410197154880223393893 10567576911966540041886355)
              ·
                refine ⟨15851365367949810062829533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10567576911966540041886355 15851365367949810062829533)
                ·
                  refine ⟨5944262012981178773561075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15851365367949810062829533 5944262012981178773561075)
                  ·
                    refine ⟨8916393019471768160341613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5944262012981178773561075 8916393019471768160341613)
                    ·
                      refine ⟨3343647382301913060128105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8916393019471768160341613 3343647382301913060128105)
                      ·
                        rfl

theorem cell23_6511730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_6511730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511730 prefixEnd_6511730 := by exact prefixLift 6511730
  have htrace : WordTrace (prefixWord ++ tailWord_6511730) baseStart_6511730 baseEnd_6511730 := by
    simpa [prefixWord, tailWord_6511730, baseEnd_6511730] using wordTrace_append hprefix tailTrace_6511730
  have hstable : (prefixWord ++ tailWord_6511730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511730).length < 2 ^ (prefixWord ++ tailWord_6511730).sum := by decide
  have hdescent : baseEnd_6511730 < baseStart_6511730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511736 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_6511736 : Nat := 118140960795 + 6511736 * 2 ^ 59
def prefixEnd_6511736 : Nat := 4983230072969 + 3 ^ 40 * 6511736 * 2
def baseEnd_6511736 : Nat := 3343650463185840036653077

theorem tailTrace_6511736 : CollatzResearch.WordTrace tailWord_6511736 prefixEnd_6511736 3343650463185840036653077 := by
  unfold tailWord_6511736
  simp only [CollatzResearch.WordTrace]
  refine ⟨118751261768550031406917531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158335015691400041875890041 118751261768550031406917531)
  ·
    refine ⟨178126892652825047110376297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118751261768550031406917531 178126892652825047110376297)
    ·
      refine ⟨133595169489618785332782223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178126892652825047110376297 133595169489618785332782223)
      ·
        refine ⟨200392754234428177999173335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133595169489618785332782223 200392754234428177999173335)
        ·
          refine ⟨300589131351642266998760003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200392754234428177999173335 300589131351642266998760003)
          ·
            refine ⟨450883697027463400498140005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300589131351642266998760003 450883697027463400498140005)
            ·
              refine ⟨84540693192649387593401251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450883697027463400498140005 84540693192649387593401251)
              ·
                refine ⟨126811039788974081390101877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84540693192649387593401251 126811039788974081390101877)
                ·
                  refine ⟨11888534980216320130322051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126811039788974081390101877 11888534980216320130322051)
                  ·
                    refine ⟨17832802470324480195483077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11888534980216320130322051 17832802470324480195483077)
                    ·
                      refine ⟨3343650463185840036653077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17832802470324480195483077 3343650463185840036653077)
                      ·
                        rfl

theorem cell23_6511736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_6511736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511736 prefixEnd_6511736 := by exact prefixLift 6511736
  have htrace : WordTrace (prefixWord ++ tailWord_6511736) baseStart_6511736 baseEnd_6511736 := by
    simpa [prefixWord, tailWord_6511736, baseEnd_6511736] using wordTrace_append hprefix tailTrace_6511736
  have hstable : (prefixWord ++ tailWord_6511736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511736).length < 2 ^ (prefixWord ++ tailWord_6511736).sum := by decide
  have hdescent : baseEnd_6511736 < baseStart_6511736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511753 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 4]
def baseStart_6511753 : Nat := 118140960795 + 6511753 * 2 ^ 59
def prefixEnd_6511753 : Nat := 4983230072969 + 3 ^ 40 * 6511753 * 2
def baseEnd_6511753 : Nat := 3343659192356966470140499

theorem tailTrace_6511753 : CollatzResearch.WordTrace tailWord_6511753 prefixEnd_6511753 3343659192356966470140499 := by
  unfold tailWord_6511753
  simp only [CollatzResearch.WordTrace]
  refine ⟨237503143578038474717203913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158335429052025649811469275 237503143578038474717203913)
  ·
    refine ⟨178127357683528856037902935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237503143578038474717203913 178127357683528856037902935)
    ·
      refine ⟨267191036525293284056854403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178127357683528856037902935 267191036525293284056854403)
      ·
        refine ⟨400786554787939926085281605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267191036525293284056854403 400786554787939926085281605)
        ·
          refine ⟨75147479022738736140990301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400786554787939926085281605 75147479022738736140990301)
          ·
            refine ⟨28180304633527026052871363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75147479022738736140990301 28180304633527026052871363)
            ·
              refine ⟨42270456950290539079307045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28180304633527026052871363 42270456950290539079307045)
              ·
                refine ⟨7925710678179476077370071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42270456950290539079307045 7925710678179476077370071)
                ·
                  refine ⟨11888566017269214116055107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925710678179476077370071 11888566017269214116055107)
                  ·
                    refine ⟨17832849025903821174082661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11888566017269214116055107 17832849025903821174082661)
                    ·
                      refine ⟨3343659192356966470140499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17832849025903821174082661 3343659192356966470140499)
                      ·
                        rfl

theorem cell23_6511753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_6511753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511753 prefixEnd_6511753 := by exact prefixLift 6511753
  have htrace : WordTrace (prefixWord ++ tailWord_6511753) baseStart_6511753 baseEnd_6511753 := by
    simpa [prefixWord, tailWord_6511753, baseEnd_6511753] using wordTrace_append hprefix tailTrace_6511753
  have hstable : (prefixWord ++ tailWord_6511753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511753).length < 2 ^ (prefixWord ++ tailWord_6511753).sum := by decide
  have hdescent : baseEnd_6511753 < baseStart_6511753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511756 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_6511756 : Nat := 118140960795 + 6511756 * 2 ^ 59
def prefixEnd_6511756 : Nat := 4983230072969 + 3 ^ 40 * 6511756 * 2
def baseEnd_6511756 : Nat := 3343660732798929958402985

theorem tailTrace_6511756 : CollatzResearch.WordTrace tailWord_6511756 prefixEnd_6511756 3343660732798929958402985 := by
  unfold tailWord_6511756
  simp only [CollatzResearch.WordTrace]
  refine ⟨118751626498513803114781561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158335501998018404153042081 118751626498513803114781561)
  ·
    refine ⟨89063719873885352336086171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118751626498513803114781561 89063719873885352336086171)
    ·
      refine ⟨133595579810828028504129257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89063719873885352336086171 133595579810828028504129257)
      ·
        refine ⟨100196684858121021378096943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133595579810828028504129257 100196684858121021378096943)
        ·
          refine ⟨150295027287181532067145415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100196684858121021378096943 150295027287181532067145415)
          ·
            refine ⟨225442540930772298100718123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150295027287181532067145415 225442540930772298100718123)
            ·
              refine ⟨338163811396158447151077185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225442540930772298100718123 338163811396158447151077185)
              ·
                refine ⟨253622858547118835363307889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338163811396158447151077185 253622858547118835363307889)
                ·
                  refine ⟨190217143910339126522480917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253622858547118835363307889 190217143910339126522480917)
                  ·
                    refine ⟨8916428620797146555741293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 190217143910339126522480917 8916428620797146555741293)
                    ·
                      refine ⟨3343660732798929958402985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8916428620797146555741293 3343660732798929958402985)
                      ·
                        rfl

theorem cell23_6511756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_6511756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511756 prefixEnd_6511756 := by exact prefixLift 6511756
  have htrace : WordTrace (prefixWord ++ tailWord_6511756) baseStart_6511756 baseEnd_6511756 := by
    simpa [prefixWord, tailWord_6511756, baseEnd_6511756] using wordTrace_append hprefix tailTrace_6511756
  have hstable : (prefixWord ++ tailWord_6511756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511756).length < 2 ^ (prefixWord ++ tailWord_6511756).sum := by decide
  have hdescent : baseEnd_6511756 < baseStart_6511756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511770 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6511770 : Nat := 118140960795 + 6511770 * 2 ^ 59
def prefixEnd_6511770 : Nat := 4983230072969 + 3 ^ 40 * 6511770 * 2
def baseEnd_6511770 : Nat := 3343667921528092903627921

theorem tailTrace_6511770 : CollatzResearch.WordTrace tailWord_6511770 prefixEnd_6511770 3343667921528092903627921 := by
  unfold tailWord_6511770
  simp only [CollatzResearch.WordTrace]
  refine ⟨59375940904744221655143191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158335842412651257747048509 59375940904744221655143191)
  ·
    refine ⟨89063911357116332482714787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59375940904744221655143191 89063911357116332482714787)
    ·
      refine ⟨133595867035674498724072181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89063911357116332482714787 133595867035674498724072181)
      ·
        refine ⟨12524612534594484255381767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133595867035674498724072181 12524612534594484255381767)
        ·
          refine ⟨18786918801891726383072651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524612534594484255381767 18786918801891726383072651)
          ·
            refine ⟨28180378202837589574608977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18786918801891726383072651 28180378202837589574608977)
            ·
              refine ⟨21135283652128192180956733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28180378202837589574608977 21135283652128192180956733)
              ·
                refine ⟨7925731369548072067858775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21135283652128192180956733 7925731369548072067858775)
                ·
                  refine ⟨11888597054322108101788163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925731369548072067858775 11888597054322108101788163)
                  ·
                    refine ⟨17832895581483162152682245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11888597054322108101788163 17832895581483162152682245)
                    ·
                      refine ⟨3343667921528092903627921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17832895581483162152682245 3343667921528092903627921)
                      ·
                        rfl

theorem cell23_6511770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6511770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511770 prefixEnd_6511770 := by exact prefixLift 6511770
  have htrace : WordTrace (prefixWord ++ tailWord_6511770) baseStart_6511770 baseEnd_6511770 := by
    simpa [prefixWord, tailWord_6511770, baseEnd_6511770] using wordTrace_append hprefix tailTrace_6511770
  have hstable : (prefixWord ++ tailWord_6511770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511770).length < 2 ^ (prefixWord ++ tailWord_6511770).sum := by decide
  have hdescent : baseEnd_6511770 < baseStart_6511770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511773 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_6511773 : Nat := 118140960795 + 6511773 * 2 ^ 59
def prefixEnd_6511773 : Nat := 4983230072969 + 3 ^ 40 * 6511773 * 2
def baseEnd_6511773 : Nat := 3343669461970056391890407

theorem tailTrace_6511773 : CollatzResearch.WordTrace tailWord_6511773 prefixEnd_6511773 3343669461970056391890407 := by
  unfold tailWord_6511773
  simp only [CollatzResearch.WordTrace]
  refine ⟨237503873037966018132931973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158335915358644012088621315 237503873037966018132931973)
  ·
    refine ⟨44531976194618628399924745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237503873037966018132931973 44531976194618628399924745)
    ·
      refine ⟨33398982145963971299943559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44531976194618628399924745 33398982145963971299943559)
      ·
        refine ⟨50098473218945956949915339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33398982145963971299943559 50098473218945956949915339)
        ·
          refine ⟨75147709828418935424873009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50098473218945956949915339 75147709828418935424873009)
          ·
            refine ⟨56360782371314201568654757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75147709828418935424873009 56360782371314201568654757)
            ·
              refine ⟨10567646694621412794122767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56360782371314201568654757 10567646694621412794122767)
              ·
                refine ⟨15851470041932119191184151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10567646694621412794122767 15851470041932119191184151)
                ·
                  refine ⟨23777205062898178786776227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15851470041932119191184151 23777205062898178786776227)
                  ·
                    refine ⟨35665807594347268180164341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23777205062898178786776227 35665807594347268180164341)
                    ·
                      refine ⟨3343669461970056391890407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35665807594347268180164341 3343669461970056391890407)
                      ·
                        rfl

theorem cell23_6511773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_6511773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511773 prefixEnd_6511773 := by exact prefixLift 6511773
  have htrace : WordTrace (prefixWord ++ tailWord_6511773) baseStart_6511773 baseEnd_6511773 := by
    simpa [prefixWord, tailWord_6511773, baseEnd_6511773] using wordTrace_append hprefix tailTrace_6511773
  have hstable : (prefixWord ++ tailWord_6511773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511773).length < 2 ^ (prefixWord ++ tailWord_6511773).sum := by decide
  have hdescent : baseEnd_6511773 < baseStart_6511773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511783 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6511783 : Nat := 118140960795 + 6511783 * 2 ^ 59
def prefixEnd_6511783 : Nat := 4983230072969 + 3 ^ 40 * 6511783 * 2
def baseEnd_6511783 : Nat := 3343674596776601352765361

theorem tailTrace_6511783 : CollatzResearch.WordTrace tailWord_6511783 prefixEnd_6511783 3343674596776601352765361 := by
  unfold tailWord_6511783
  simp only [CollatzResearch.WordTrace]
  refine ⟨237504237767929789840796003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158336158511953193227197335 237504237767929789840796003)
  ·
    refine ⟨356256356651894684761194005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237504237767929789840796003 356256356651894684761194005)
    ·
      refine ⟨16699516718057563348180969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 356256356651894684761194005 16699516718057563348180969)
      ·
        refine ⟨12524637538543172511135727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16699516718057563348180969 12524637538543172511135727)
        ·
          refine ⟨18786956307814758766703591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524637538543172511135727 18786956307814758766703591)
          ·
            refine ⟨28180434461722138150055387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18786956307814758766703591 28180434461722138150055387)
            ·
              refine ⟨42270651692583207225083081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28180434461722138150055387 42270651692583207225083081)
              ·
                refine ⟨31702988769437405418812311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42270651692583207225083081 31702988769437405418812311)
                ·
                  refine ⟨47554483154156108128218467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31702988769437405418812311 47554483154156108128218467)
                  ·
                    refine ⟨71331724731234162192327701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47554483154156108128218467 71331724731234162192327701)
                    ·
                      refine ⟨3343674596776601352765361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71331724731234162192327701 3343674596776601352765361)
                      ·
                        rfl

theorem cell23_6511783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6511783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511783 prefixEnd_6511783 := by exact prefixLift 6511783
  have htrace : WordTrace (prefixWord ++ tailWord_6511783) baseStart_6511783 baseEnd_6511783 := by
    simpa [prefixWord, tailWord_6511783, baseEnd_6511783] using wordTrace_append hprefix tailTrace_6511783
  have hstable : (prefixWord ++ tailWord_6511783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511783).length < 2 ^ (prefixWord ++ tailWord_6511783).sum := by decide
  have hdescent : baseEnd_6511783 < baseStart_6511783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511793 : List Nat := [1, 2, 2, 5, 1, 2, 2, 8]
def baseStart_6511793 : Nat := 118140960795 + 6511793 * 2 ^ 59
def prefixEnd_6511793 : Nat := 4983230072969 + 3 ^ 40 * 6511793 * 2
def baseEnd_6511793 : Nat := 123839990058635048653345

theorem tailTrace_6511793 : CollatzResearch.WordTrace tailWord_6511793 prefixEnd_6511793 123839990058635048653345 := by
  unfold tailWord_6511793
  simp only [CollatzResearch.WordTrace]
  refine ⟨237504602497893561548660033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158336401665262374365773355 237504602497893561548660033)
  ·
    refine ⟨178128451873420171161495025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237504602497893561548660033 178128451873420171161495025)
    ·
      refine ⟨133596338905065128371121269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178128451873420171161495025 133596338905065128371121269)
      ·
        refine ⟨12524656772349855784792619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133596338905065128371121269 12524656772349855784792619)
        ·
          refine ⟨18786985158524783677188929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524656772349855784792619 18786985158524783677188929)
          ·
            refine ⟨14090238868893587757891697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18786985158524783677188929 14090238868893587757891697)
            ·
              refine ⟨10567679151670190818418773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14090238868893587757891697 10567679151670190818418773)
              ·
                refine ⟨123839990058635048653345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10567679151670190818418773 123839990058635048653345)
                ·
                  rfl

theorem cell23_6511793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 8].length) (baseStart_6511793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511793 prefixEnd_6511793 := by exact prefixLift 6511793
  have htrace : WordTrace (prefixWord ++ tailWord_6511793) baseStart_6511793 baseEnd_6511793 := by
    simpa [prefixWord, tailWord_6511793, baseEnd_6511793] using wordTrace_append hprefix tailTrace_6511793
  have hstable : (prefixWord ++ tailWord_6511793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511793).length < 2 ^ (prefixWord ++ tailWord_6511793).sum := by decide
  have hdescent : baseEnd_6511793 < baseStart_6511793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511803 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 3]
def baseStart_6511803 : Nat := 118140960795 + 6511803 * 2 ^ 59
def prefixEnd_6511803 : Nat := 4983230072969 + 3 ^ 40 * 6511803 * 2
def baseEnd_6511803 : Nat := 3343684866389691274515269

theorem tailTrace_6511803 : CollatzResearch.WordTrace tailWord_6511803 prefixEnd_6511803 3343684866389691274515269 := by
  unfold tailWord_6511803
  simp only [CollatzResearch.WordTrace]
  refine ⟨237504967227857333256524063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158336644818571555504349375 237504967227857333256524063)
  ·
    refine ⟨356257450841785999884786095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237504967227857333256524063 356257450841785999884786095)
    ·
      refine ⟨534386176262678999827179143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356257450841785999884786095 534386176262678999827179143)
      ·
        refine ⟨801579264394018499740768715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534386176262678999827179143 801579264394018499740768715)
        ·
          refine ⟨1202368896591027749611153073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801579264394018499740768715 1202368896591027749611153073)
          ·
            refine ⟨901776672443270812208364805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202368896591027749611153073 901776672443270812208364805)
            ·
              refine ⟨169083126083113277289068401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 901776672443270812208364805 169083126083113277289068401)
              ·
                refine ⟨126812344562334957966801301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169083126083113277289068401 126812344562334957966801301)
                ·
                  refine ⟨5944328651359451154693811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126812344562334957966801301 5944328651359451154693811)
                  ·
                    refine ⟨8916492977039176732040717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5944328651359451154693811 8916492977039176732040717)
                    ·
                      refine ⟨3343684866389691274515269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8916492977039176732040717 3343684866389691274515269)
                      ·
                        rfl

theorem cell23_6511803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 3].length) (baseStart_6511803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511803 prefixEnd_6511803 := by exact prefixLift 6511803
  have htrace : WordTrace (prefixWord ++ tailWord_6511803) baseStart_6511803 baseEnd_6511803 := by
    simpa [prefixWord, tailWord_6511803, baseEnd_6511803] using wordTrace_append hprefix tailTrace_6511803
  have hstable : (prefixWord ++ tailWord_6511803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511803).length < 2 ^ (prefixWord ++ tailWord_6511803).sum := by decide
  have hdescent : baseEnd_6511803 < baseStart_6511803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511814 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_6511814 : Nat := 118140960795 + 6511814 * 2 ^ 59
def prefixEnd_6511814 : Nat := 4983230072969 + 3 ^ 40 * 6511814 * 2
def baseEnd_6511814 : Nat := 1114563504892296910492573

theorem tailTrace_6511814 : CollatzResearch.WordTrace tailWord_6511814 prefixEnd_6511814 1114563504892296910492573 := by
  unfold tailWord_6511814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422042763463046316724203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158336912287211654756782997 7422042763463046316724203)
  ·
    refine ⟨11133064145194569475086305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7422042763463046316724203 11133064145194569475086305)
    ·
      refine ⟨8349798108895927106314729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11133064145194569475086305 8349798108895927106314729)
      ·
        refine ⟨6262348581671945329736047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8349798108895927106314729 6262348581671945329736047)
        ·
          refine ⟨9393522872507917994604071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6262348581671945329736047 9393522872507917994604071)
          ·
            refine ⟨14090284308761876991906107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393522872507917994604071 14090284308761876991906107)
            ·
              refine ⟨21135426463142815487859161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14090284308761876991906107 21135426463142815487859161)
              ·
                refine ⟨15851569847357111615894371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21135426463142815487859161 15851569847357111615894371)
                ·
                  refine ⟨23777354771035667423841557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15851569847357111615894371 23777354771035667423841557)
                  ·
                    refine ⟨1114563504892296910492573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23777354771035667423841557 1114563504892296910492573)
                    ·
                      rfl

theorem cell23_6511814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_6511814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511814 prefixEnd_6511814 := by exact prefixLift 6511814
  have htrace : WordTrace (prefixWord ++ tailWord_6511814) baseStart_6511814 baseEnd_6511814 := by
    simpa [prefixWord, tailWord_6511814, baseEnd_6511814] using wordTrace_append hprefix tailTrace_6511814
  have hstable : (prefixWord ++ tailWord_6511814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511814).length < 2 ^ (prefixWord ++ tailWord_6511814).sum := by decide
  have hdescent : baseEnd_6511814 < baseStart_6511814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511816 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_6511816 : Nat := 118140960795 + 6511816 * 2 ^ 59
def prefixEnd_6511816 : Nat := 4983230072969 + 3 ^ 40 * 6511816 * 2
def baseEnd_6511816 : Nat := 3343691541638199723652709

theorem tailTrace_6511816 : CollatzResearch.WordTrace tailWord_6511816 prefixEnd_6511816 3343691541638199723652709 := by
  unfold tailWord_6511816
  simp only [CollatzResearch.WordTrace]
  refine ⟨118752720688405118238373651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158336960917873490984498201 118752720688405118238373651)
  ·
    refine ⟨178129081032607677357560477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118752720688405118238373651 178129081032607677357560477)
    ·
      refine ⟨66798405387227879009085179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178129081032607677357560477 66798405387227879009085179)
      ·
        refine ⟨100197608080841818513627769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66798405387227879009085179 100197608080841818513627769)
        ·
          refine ⟨75148206060631363885220827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100197608080841818513627769 75148206060631363885220827)
          ·
            refine ⟨112722309090947045827831241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75148206060631363885220827 112722309090947045827831241)
            ·
              refine ⟨84541731818210284370873431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112722309090947045827831241 84541731818210284370873431)
              ·
                refine ⟨126812597727315426556310147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84541731818210284370873431 126812597727315426556310147)
                ·
                  refine ⟨190218896590973139834465221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126812597727315426556310147 190218896590973139834465221)
                  ·
                    refine ⟨35666043110807463718962229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190218896590973139834465221 35666043110807463718962229)
                    ·
                      refine ⟨3343691541638199723652709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35666043110807463718962229 3343691541638199723652709)
                      ·
                        rfl

theorem cell23_6511816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_6511816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511816 prefixEnd_6511816 := by exact prefixLift 6511816
  have htrace : WordTrace (prefixWord ++ tailWord_6511816) baseStart_6511816 baseEnd_6511816 := by
    simpa [prefixWord, tailWord_6511816, baseEnd_6511816] using wordTrace_append hprefix tailTrace_6511816
  have hstable : (prefixWord ++ tailWord_6511816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511816).length < 2 ^ (prefixWord ++ tailWord_6511816).sum := by decide
  have hdescent : baseEnd_6511816 < baseStart_6511816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511821 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6511821 : Nat := 118140960795 + 6511821 * 2 ^ 59
def prefixEnd_6511821 : Nat := 4983230072969 + 3 ^ 40 * 6511821 * 2
def baseEnd_6511821 : Nat := 3343694109041472204090187

theorem tailTrace_6511821 : CollatzResearch.WordTrace tailWord_6511821 prefixEnd_6511821 3343694109041472204090187 := by
  unfold tailWord_6511821
  simp only [CollatzResearch.WordTrace]
  refine ⟨237505623741792122330679317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158337082494528081553786211 237505623741792122330679317)
  ·
    refine ⟨11133076112896505734250593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237505623741792122330679317 11133076112896505734250593)
    ·
      refine ⟨8349807084672379300687945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11133076112896505734250593 8349807084672379300687945)
      ·
        refine ⟨6262355313504284475515959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8349807084672379300687945 6262355313504284475515959)
        ·
          refine ⟨9393532970256426713273939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6262355313504284475515959 9393532970256426713273939)
          ·
            refine ⟨14090299455384640069910909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9393532970256426713273939 14090299455384640069910909)
            ·
              refine ⟨5283862295769240026216591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14090299455384640069910909 5283862295769240026216591)
              ·
                refine ⟨7925793443653860039324887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5283862295769240026216591 7925793443653860039324887)
                ·
                  refine ⟨11888690165480790058987331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7925793443653860039324887 11888690165480790058987331)
                  ·
                    refine ⟨17833035248221185088480997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11888690165480790058987331 17833035248221185088480997)
                    ·
                      refine ⟨3343694109041472204090187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17833035248221185088480997 3343694109041472204090187)
                      ·
                        rfl

theorem cell23_6511821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6511821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511821 prefixEnd_6511821 := by exact prefixLift 6511821
  have htrace : WordTrace (prefixWord ++ tailWord_6511821) baseStart_6511821 baseEnd_6511821 := by
    simpa [prefixWord, tailWord_6511821, baseEnd_6511821] using wordTrace_append hprefix tailTrace_6511821
  have hstable : (prefixWord ++ tailWord_6511821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511821).length < 2 ^ (prefixWord ++ tailWord_6511821).sum := by decide
  have hdescent : baseEnd_6511821 < baseStart_6511821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511853 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_6511853 : Nat := 118140960795 + 6511853 * 2 ^ 59
def prefixEnd_6511853 : Nat := 4983230072969 + 3 ^ 40 * 6511853 * 2
def baseEnd_6511853 : Nat := 1114570180140805359630013

theorem tailTrace_6511853 : CollatzResearch.WordTrace tailWord_6511853 prefixEnd_6511853 1114570180140805359630013 := by
  unfold tailWord_6511853
  simp only [CollatzResearch.WordTrace]
  refine ⟨237506790877676191795844213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158337860585117461197229475 237506790877676191795844213)
  ·
    refine ⟨22266261644782142980860395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237506790877676191795844213 22266261644782142980860395)
    ·
      refine ⟨33399392467173214471290593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22266261644782142980860395 33399392467173214471290593)
      ·
        refine ⟨25049544350379910853467945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33399392467173214471290593 25049544350379910853467945)
        ·
          refine ⟨18787158262784933140100959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25049544350379910853467945 18787158262784933140100959)
          ·
            refine ⟨28180737394177399710151439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18787158262784933140100959 28180737394177399710151439)
            ·
              refine ⟨42271106091266099565227159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28180737394177399710151439 42271106091266099565227159)
              ·
                refine ⟨63406659136899149347840739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42271106091266099565227159 63406659136899149347840739)
                ·
                  refine ⟨95109988705348724021761109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63406659136899149347840739 95109988705348724021761109)
                  ·
                    refine ⟨1114570180140805359630013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95109988705348724021761109 1114570180140805359630013)
                    ·
                      rfl

theorem cell23_6511853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_6511853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511853 prefixEnd_6511853 := by exact prefixLift 6511853
  have htrace : WordTrace (prefixWord ++ tailWord_6511853) baseStart_6511853 baseEnd_6511853 := by
    simpa [prefixWord, tailWord_6511853, baseEnd_6511853] using wordTrace_append hprefix tailTrace_6511853
  have hstable : (prefixWord ++ tailWord_6511853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511853).length < 2 ^ (prefixWord ++ tailWord_6511853).sum := by decide
  have hdescent : baseEnd_6511853 < baseStart_6511853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511900 : List Nat := [2, 2, 3, 1, 1, 1, 4, 4, 5]
def baseStart_6511900 : Nat := 118140960795 + 6511900 * 2 ^ 59
def prefixEnd_6511900 : Nat := 4983230072969 + 3 ^ 40 * 6511900 * 2
def baseEnd_6511900 : Nat := 371526074890353043889147

theorem tailTrace_6511900 : CollatzResearch.WordTrace tailWord_6511900 prefixEnd_6511900 371526074890353043889147 := by
  unfold tailWord_6511900
  simp only [CollatzResearch.WordTrace]
  refine ⟨118754252554252959411402577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158339003405670612548536769 118754252554252959411402577)
  ·
    refine ⟨89065689415689719558551933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118754252554252959411402577 89065689415689719558551933)
    ·
      refine ⟨33399633530883644834456975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89065689415689719558551933 33399633530883644834456975)
      ·
        refine ⟨50099450296325467251685463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33399633530883644834456975 50099450296325467251685463)
        ·
          refine ⟨75149175444488200877528195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50099450296325467251685463 75149175444488200877528195)
          ·
            refine ⟨112723763166732301316292293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75149175444488200877528195 112723763166732301316292293)
            ·
              refine ⟨21135705593762306496804805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112723763166732301316292293 21135705593762306496804805)
              ·
                refine ⟨3962944798830432468150901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21135705593762306496804805 3962944798830432468150901)
                ·
                  refine ⟨371526074890353043889147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3962944798830432468150901 371526074890353043889147)
                  ·
                    rfl

theorem cell23_6511900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_6511900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511900 prefixEnd_6511900 := by exact prefixLift 6511900
  have htrace : WordTrace (prefixWord ++ tailWord_6511900) baseStart_6511900 baseEnd_6511900 := by
    simpa [prefixWord, tailWord_6511900, baseEnd_6511900] using wordTrace_append hprefix tailTrace_6511900
  have hstable : (prefixWord ++ tailWord_6511900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511900).length < 2 ^ (prefixWord ++ tailWord_6511900).sum := by decide
  have hdescent : baseEnd_6511900 < baseStart_6511900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6511950 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_6511950 : Nat := 118140960795 + 6511950 * 2 ^ 59
def prefixEnd_6511950 : Nat := 4983230072969 + 3 ^ 40 * 6511950 * 2
def baseEnd_6511950 : Nat := 3343760348045902199377093

theorem tailTrace_6511950 : CollatzResearch.WordTrace tailWord_6511950 prefixEnd_6511950 3343760348045902199377093 := by
  unfold tailWord_6511950
  simp only [CollatzResearch.WordTrace]
  refine ⟨29688791094790597170265663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158340219172216518241416869 29688791094790597170265663)
  ·
    refine ⟨44533186642185895755398495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29688791094790597170265663 44533186642185895755398495)
    ·
      refine ⟨66799779963278843633097743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44533186642185895755398495 66799779963278843633097743)
      ·
        refine ⟨100199669944918265449646615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66799779963278843633097743 100199669944918265449646615)
        ·
          refine ⟨150299504917377398174469923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100199669944918265449646615 150299504917377398174469923)
          ·
            refine ⟨225449257376066097261704885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150299504917377398174469923 225449257376066097261704885)
            ·
              refine ⟨21135867879006196618284833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225449257376066097261704885 21135867879006196618284833)
              ·
                refine ⟨15851900909254647463713625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21135867879006196618284833 15851900909254647463713625)
                ·
                  refine ⟨11888925681940985597785219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15851900909254647463713625 11888925681940985597785219)
                  ·
                    refine ⟨17833388522911478396677829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11888925681940985597785219 17833388522911478396677829)
                    ·
                      refine ⟨3343760348045902199377093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17833388522911478396677829 3343760348045902199377093)
                      ·
                        rfl

theorem cell23_6511950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_6511950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6511950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6511950 prefixEnd_6511950 := by exact prefixLift 6511950
  have htrace : WordTrace (prefixWord ++ tailWord_6511950) baseStart_6511950 baseEnd_6511950 := by
    simpa [prefixWord, tailWord_6511950, baseEnd_6511950] using wordTrace_append hprefix tailTrace_6511950
  have hstable : (prefixWord ++ tailWord_6511950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6511950).length < 2 ^ (prefixWord ++ tailWord_6511950).sum := by decide
  have hdescent : baseEnd_6511950 < baseStart_6511950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6511950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512034 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_6512034 : Nat := 118140960795 + 6512034 * 2 ^ 59
def prefixEnd_6512034 : Nat := 4983230072969 + 3 ^ 40 * 6512034 * 2
def baseEnd_6512034 : Nat := 3343803480420879870726707

theorem tailTrace_6512034 : CollatzResearch.WordTrace tailWord_6512034 prefixEnd_6512034 3343803480420879870726707 := by
  unfold tailWord_6512034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378348122505114927045789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158342261660013639805455437 59378348122505114927045789)
  ·
    refine ⟨22266880545939418097642171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59378348122505114927045789 22266880545939418097642171)
    ·
      refine ⟨33400320818909127146463257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22266880545939418097642171 33400320818909127146463257)
      ·
        refine ⟨25050240614181845359847443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33400320818909127146463257 25050240614181845359847443)
        ·
          refine ⟨37575360921272768039771165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25050240614181845359847443 37575360921272768039771165)
          ·
            refine ⟨14090760345477288014914187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37575360921272768039771165 14090760345477288014914187)
            ·
              refine ⟨21136140518215932022371281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14090760345477288014914187 21136140518215932022371281)
              ·
                refine ⟨15852105388661949016778461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21136140518215932022371281 15852105388661949016778461)
                ·
                  refine ⟨5944539520748230881291923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15852105388661949016778461 5944539520748230881291923)
                  ·
                    refine ⟨8916809281122346321937885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5944539520748230881291923 8916809281122346321937885)
                    ·
                      refine ⟨3343803480420879870726707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8916809281122346321937885 3343803480420879870726707)
                      ·
                        rfl

theorem cell23_6512034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_6512034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512034 prefixEnd_6512034 := by exact prefixLift 6512034
  have htrace : WordTrace (prefixWord ++ tailWord_6512034) baseStart_6512034 baseEnd_6512034 := by
    simpa [prefixWord, tailWord_6512034, baseEnd_6512034] using wordTrace_append hprefix tailTrace_6512034
  have hstable : (prefixWord ++ tailWord_6512034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512034).length < 2 ^ (prefixWord ++ tailWord_6512034).sum := by decide
  have hdescent : baseEnd_6512034 < baseStart_6512034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512067 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 2, 4]
def baseStart_6512067 : Nat := 118140960795 + 6512067 * 2 ^ 59
def prefixEnd_6512067 : Nat := 4983230072969 + 3 ^ 40 * 6512067 * 2
def baseEnd_6512067 : Nat := 1114606808427492747204685

theorem tailTrace_6512067 : CollatzResearch.WordTrace tailWord_6512067 prefixEnd_6512067 1114606808427492747204685 := by
  unfold tailWord_6512067
  simp only [CollatzResearch.WordTrace]
  refine ⟨237514596098900906344134455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158343064065933937562756303 237514596098900906344134455)
  ·
    refine ⟨356271894148351359516201683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237514596098900906344134455 356271894148351359516201683)
    ·
      refine ⟨534407841222527039274302525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356271894148351359516201683 534407841222527039274302525)
      ·
        refine ⟨200402940458447639727863447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534407841222527039274302525 200402940458447639727863447)
        ·
          refine ⟨300604410687671459591795171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200402940458447639727863447 300604410687671459591795171)
          ·
            refine ⟨450906616031507189387692757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300604410687671459591795171 450906616031507189387692757)
            ·
              refine ⟨10568123813238449751274049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 450906616031507189387692757 10568123813238449751274049)
              ·
                refine ⟨7926092859928837313455537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10568123813238449751274049 7926092859928837313455537)
                ·
                  refine ⟨5944569644946627985091653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7926092859928837313455537 5944569644946627985091653)
                  ·
                    refine ⟨1114606808427492747204685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5944569644946627985091653 1114606808427492747204685)
                    ·
                      rfl

theorem cell23_6512067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 4].length) (baseStart_6512067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512067 prefixEnd_6512067 := by exact prefixLift 6512067
  have htrace : WordTrace (prefixWord ++ tailWord_6512067) baseStart_6512067 baseEnd_6512067 := by
    simpa [prefixWord, tailWord_6512067, baseEnd_6512067] using wordTrace_append hprefix tailTrace_6512067
  have hstable : (prefixWord ++ tailWord_6512067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512067).length < 2 ^ (prefixWord ++ tailWord_6512067).sum := by decide
  have hdescent : baseEnd_6512067 < baseStart_6512067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512073 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_6512073 : Nat := 118140960795 + 6512073 * 2 ^ 59
def prefixEnd_6512073 : Nat := 4983230072969 + 3 ^ 40 * 6512073 * 2
def baseEnd_6512073 : Nat := 3343823506166405218139027

theorem tailTrace_6512073 : CollatzResearch.WordTrace tailWord_6512073 prefixEnd_6512073 3343823506166405218139027 := by
  unfold tailWord_6512073
  simp only [CollatzResearch.WordTrace]
  refine ⟨237514814936879169368852873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158343209957919446245901915 237514814936879169368852873)
  ·
    refine ⟨178136111202659377026639655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237514814936879169368852873 178136111202659377026639655)
    ·
      refine ⟨267204166803989065539959483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178136111202659377026639655 267204166803989065539959483)
      ·
        refine ⟨400806250205983598309939225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267204166803989065539959483 400806250205983598309939225)
        ·
          refine ⟨300604687654487698732454419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400806250205983598309939225 300604687654487698732454419)
          ·
            refine ⟨450907031481731548098681629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300604687654487698732454419 450907031481731548098681629)
            ·
              refine ⟨169090136805649330537005611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450907031481731548098681629 169090136805649330537005611)
              ·
                refine ⟨253635205208473995805508417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169090136805649330537005611 253635205208473995805508417)
                ·
                  refine ⟨190226403906355496854131313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253635205208473995805508417 190226403906355496854131313)
                  ·
                    refine ⟨142669802929766622640598485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190226403906355496854131313 142669802929766622640598485)
                    ·
                      refine ⟨3343823506166405218139027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142669802929766622640598485 3343823506166405218139027)
                      ·
                        rfl

theorem cell23_6512073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_6512073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512073 prefixEnd_6512073 := by exact prefixLift 6512073
  have htrace : WordTrace (prefixWord ++ tailWord_6512073) baseStart_6512073 baseEnd_6512073 := by
    simpa [prefixWord, tailWord_6512073, baseEnd_6512073] using wordTrace_append hprefix tailTrace_6512073
  have hstable : (prefixWord ++ tailWord_6512073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512073).length < 2 ^ (prefixWord ++ tailWord_6512073).sum := by decide
  have hdescent : baseEnd_6512073 < baseStart_6512073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512074 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_6512074 : Nat := 118140960795 + 6512074 * 2 ^ 59
def prefixEnd_6512074 : Nat := 4983230072969 + 3 ^ 40 * 6512074 * 2
def baseEnd_6512074 : Nat := 3343824019647059714226523

theorem tailTrace_6512074 : CollatzResearch.WordTrace tailWord_6512074 prefixEnd_6512074 3343824019647059714226523 := by
  unfold tailWord_6512074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378712852468886634909819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158343234273250364359759517 59378712852468886634909819)
  ·
    refine ⟨89068069278703329952364729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59378712852468886634909819 89068069278703329952364729)
    ·
      refine ⟨66801051959027497464273547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89068069278703329952364729 66801051959027497464273547)
      ·
        refine ⟨100201577938541246196410321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66801051959027497464273547 100201577938541246196410321)
        ·
          refine ⟨75151183453905934647307741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100201577938541246196410321 75151183453905934647307741)
          ·
            refine ⟨28181693795214725492740403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75151183453905934647307741 28181693795214725492740403)
            ·
              refine ⟨42272540692822088239110605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28181693795214725492740403 42272540692822088239110605)
              ·
                refine ⟨15852202759808283089666477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42272540692822088239110605 15852202759808283089666477)
                ·
                  refine ⟨5944576034928106158624929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15852202759808283089666477 5944576034928106158624929)
                  ·
                    refine ⟨4458432026196079618968697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5944576034928106158624929 4458432026196079618968697)
                    ·
                      refine ⟨3343824019647059714226523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458432026196079618968697 3343824019647059714226523)
                      ·
                        rfl

theorem cell23_6512074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_6512074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512074 prefixEnd_6512074 := by exact prefixLift 6512074
  have htrace : WordTrace (prefixWord ++ tailWord_6512074) baseStart_6512074 baseEnd_6512074 := by
    simpa [prefixWord, tailWord_6512074, baseEnd_6512074] using wordTrace_append hprefix tailTrace_6512074
  have hstable : (prefixWord ++ tailWord_6512074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512074).length < 2 ^ (prefixWord ++ tailWord_6512074).sum := by decide
  have hdescent : baseEnd_6512074 < baseStart_6512074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512084 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_6512084 : Nat := 118140960795 + 6512084 * 2 ^ 59
def prefixEnd_6512084 : Nat := 4983230072969 + 3 ^ 40 * 6512084 * 2
def baseEnd_6512084 : Nat := 1114609718151201558367159

theorem tailTrace_6512084 : CollatzResearch.WordTrace tailWord_6512084 prefixEnd_6512084 1114609718151201558367159 := by
  unfold tailWord_6512084
  simp only [CollatzResearch.WordTrace]
  refine ⟨118757608069919659123751653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158343477426559545498335537 118757608069919659123751653)
  ·
    refine ⟨22267051513109936085703435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118757608069919659123751653 22267051513109936085703435)
    ·
      refine ⟨33400577269664904128555153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22267051513109936085703435 33400577269664904128555153)
      ·
        refine ⟨25050432952248678096416365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33400577269664904128555153 25050432952248678096416365)
        ·
          refine ⟨9393912357093254286156137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25050432952248678096416365 9393912357093254286156137)
          ·
            refine ⟨7045434267819940714617103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9393912357093254286156137 7045434267819940714617103)
            ·
              refine ⟨10568151401729911071925655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7045434267819940714617103 10568151401729911071925655)
              ·
                refine ⟨15852227102594866607888483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10568151401729911071925655 15852227102594866607888483)
                ·
                  refine ⟨23778340653892299911832725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15852227102594866607888483 23778340653892299911832725)
                  ·
                    refine ⟨1114609718151201558367159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23778340653892299911832725 1114609718151201558367159)
                    ·
                      rfl

theorem cell23_6512084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_6512084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512084 prefixEnd_6512084 := by exact prefixLift 6512084
  have htrace : WordTrace (prefixWord ++ tailWord_6512084) baseStart_6512084 baseEnd_6512084 := by
    simpa [prefixWord, tailWord_6512084, baseEnd_6512084] using wordTrace_append hprefix tailTrace_6512084
  have hstable : (prefixWord ++ tailWord_6512084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512084).length < 2 ^ (prefixWord ++ tailWord_6512084).sum := by decide
  have hdescent : baseEnd_6512084 < baseStart_6512084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512097 : List Nat := [1, 2, 3, 1, 2, 5, 2, 7]
def baseStart_6512097 : Nat := 118140960795 + 6512097 * 2 ^ 59
def prefixEnd_6512097 : Nat := 4983230072969 + 3 ^ 40 * 6512097 * 2
def baseEnd_6512097 : Nat := 123845771470448634231071

theorem tailTrace_6512097 : CollatzResearch.WordTrace tailWord_6512097 prefixEnd_6512097 123845771470448634231071 := by
  unfold tailWord_6512097
  simp only [CollatzResearch.WordTrace]
  refine ⟨237515690288792221467726545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158343793525861480978484363 237515690288792221467726545)
  ·
    refine ⟨178136767716594166100794909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237515690288792221467726545 178136767716594166100794909)
    ·
      refine ⟨66801287893722812287798091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178136767716594166100794909 66801287893722812287798091)
      ·
        refine ⟨100201931840584218431697137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66801287893722812287798091 100201931840584218431697137)
        ·
          refine ⟨75151448880438163823772853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100201931840584218431697137 75151448880438163823772853)
          ·
            refine ⟨7045448332541077858478705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75151448880438163823772853 7045448332541077858478705)
            ·
              refine ⟨5284086249405808393859029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7045448332541077858478705 5284086249405808393859029)
              ·
                refine ⟨123845771470448634231071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5284086249405808393859029 123845771470448634231071)
                ·
                  rfl

theorem cell23_6512097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 7].length) (baseStart_6512097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512097 prefixEnd_6512097 := by exact prefixLift 6512097
  have htrace : WordTrace (prefixWord ++ tailWord_6512097) baseStart_6512097 baseEnd_6512097 := by
    simpa [prefixWord, tailWord_6512097, baseEnd_6512097] using wordTrace_append hprefix tailTrace_6512097
  have hstable : (prefixWord ++ tailWord_6512097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512097).length < 2 ^ (prefixWord ++ tailWord_6512097).sum := by decide
  have hdescent : baseEnd_6512097 < baseStart_6512097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512181 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_6512181 : Nat := 118140960795 + 6512181 * 2 ^ 59
def prefixEnd_6512181 : Nat := 4983230072969 + 3 ^ 40 * 6512181 * 2
def baseEnd_6512181 : Nat := 3343878962077090795588531

theorem tailTrace_6512181 : CollatzResearch.WordTrace tailWord_6512181 prefixEnd_6512181 3343878962077090795588531 := by
  unfold tailWord_6512181
  simp only [CollatzResearch.WordTrace]
  refine ⟨237518754020487903813784397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158345836013658602542522931 237518754020487903813784397)
  ·
    refine ⟨89069532757682963930169149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237518754020487903813784397 89069532757682963930169149)
    ·
      refine ⟨33401074784131111473813431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89069532757682963930169149 33401074784131111473813431)
      ·
        refine ⟨50101612176196667210720147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33401074784131111473813431 50101612176196667210720147)
        ·
          refine ⟨75152418264295000816080221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50101612176196667210720147 75152418264295000816080221)
          ·
            refine ⟨28182156849110625306030083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75152418264295000816080221 28182156849110625306030083)
            ·
              refine ⟨42273235273665937959045125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28182156849110625306030083 42273235273665937959045125)
              ·
                refine ⟨7926231613812363367320961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42273235273665937959045125 7926231613812363367320961)
                ·
                  refine ⟨5944673710359272525490721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7926231613812363367320961 5944673710359272525490721)
                  ·
                    refine ⟨4458505282769454394118041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5944673710359272525490721 4458505282769454394118041)
                    ·
                      refine ⟨3343878962077090795588531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458505282769454394118041 3343878962077090795588531)
                      ·
                        rfl

theorem cell23_6512181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_6512181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512181 prefixEnd_6512181 := by exact prefixLift 6512181
  have htrace : WordTrace (prefixWord ++ tailWord_6512181) baseStart_6512181 baseEnd_6512181 := by
    simpa [prefixWord, tailWord_6512181, baseEnd_6512181] using wordTrace_append hprefix tailTrace_6512181
  have hstable : (prefixWord ++ tailWord_6512181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512181).length < 2 ^ (prefixWord ++ tailWord_6512181).sum := by decide
  have hdescent : baseEnd_6512181 < baseStart_6512181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512197 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_6512197 : Nat := 118140960795 + 6512197 * 2 ^ 59
def prefixEnd_6512197 : Nat := 4983230072969 + 3 ^ 40 * 6512197 * 2
def baseEnd_6512197 : Nat := 3343887177767562732988457

theorem tailTrace_6512197 : CollatzResearch.WordTrace tailWord_6512197 prefixEnd_6512197 3343887177767562732988457 := by
  unfold tailWord_6512197
  simp only [CollatzResearch.WordTrace]
  refine ⟨237519337588429938546366845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158346225058953292364244563 237519337588429938546366845)
  ·
    refine ⟨89069751595661226954887567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237519337588429938546366845 89069751595661226954887567)
    ·
      refine ⟨133604627393491840432331351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89069751595661226954887567 133604627393491840432331351)
      ·
        refine ⟨200406941090237760648497027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133604627393491840432331351 200406941090237760648497027)
        ·
          refine ⟨300610411635356640972745541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200406941090237760648497027 300610411635356640972745541)
          ·
            refine ⟨56364452181629370182389789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300610411635356640972745541 56364452181629370182389789)
            ·
              refine ⟨21136669568111013818396171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56364452181629370182389789 21136669568111013818396171)
              ·
                refine ⟨31705004352166520727594257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21136669568111013818396171 31705004352166520727594257)
                ·
                  refine ⟨23778753264124890545695693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31705004352166520727594257 23778753264124890545695693)
                  ·
                    refine ⟨8917032474046833954635885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23778753264124890545695693 8917032474046833954635885)
                    ·
                      refine ⟨3343887177767562732988457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8917032474046833954635885 3343887177767562732988457)
                      ·
                        rfl

theorem cell23_6512197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_6512197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512197 prefixEnd_6512197 := by exact prefixLift 6512197
  have htrace : WordTrace (prefixWord ++ tailWord_6512197) baseStart_6512197 baseEnd_6512197 := by
    simpa [prefixWord, tailWord_6512197, baseEnd_6512197] using wordTrace_append hprefix tailTrace_6512197
  have hstable : (prefixWord ++ tailWord_6512197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512197).length < 2 ^ (prefixWord ++ tailWord_6512197).sum := by decide
  have hdescent : baseEnd_6512197 < baseStart_6512197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512207 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 4, 5, 2]
def baseStart_6512207 : Nat := 118140960795 + 6512207 * 2 ^ 59
def prefixEnd_6512207 : Nat := 4983230072969 + 3 ^ 40 * 6512207 * 2
def baseEnd_6512207 : Nat := 3343892312574107693863411

theorem tailTrace_6512207 : CollatzResearch.WordTrace tailWord_6512207 prefixEnd_6512207 3343892312574107693863411 := by
  unfold tailWord_6512207
  simp only [CollatzResearch.WordTrace]
  refine ⟨237519702318393710254230875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158346468212262473502820583 237519702318393710254230875)
  ·
    refine ⟨356279553477590565381346313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237519702318393710254230875 356279553477590565381346313)
    ·
      refine ⟨267209665108192924036009735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356279553477590565381346313 267209665108192924036009735)
      ·
        refine ⟨400814497662289386054014603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267209665108192924036009735 400814497662289386054014603)
        ·
          refine ⟨601221746493434079081021905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400814497662289386054014603 601221746493434079081021905)
          ·
            refine ⟨450916309870075559310766429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601221746493434079081021905 450916309870075559310766429)
            ·
              refine ⟨169093616201278334741537411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450916309870075559310766429 169093616201278334741537411)
              ·
                refine ⟨253640424301917502112306117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169093616201278334741537411 253640424301917502112306117)
                ·
                  refine ⟨47557579556609531646057397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253640424301917502112306117 47557579556609531646057397)
                  ·
                    refine ⟨4458523083432143591817881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47557579556609531646057397 4458523083432143591817881)
                    ·
                      refine ⟨3343892312574107693863411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458523083432143591817881 3343892312574107693863411)
                      ·
                        rfl

theorem cell23_6512207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5, 2].length) (baseStart_6512207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512207 prefixEnd_6512207 := by exact prefixLift 6512207
  have htrace : WordTrace (prefixWord ++ tailWord_6512207) baseStart_6512207 baseEnd_6512207 := by
    simpa [prefixWord, tailWord_6512207, baseEnd_6512207] using wordTrace_append hprefix tailTrace_6512207
  have hstable : (prefixWord ++ tailWord_6512207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512207).length < 2 ^ (prefixWord ++ tailWord_6512207).sum := by decide
  have hdescent : baseEnd_6512207 < baseStart_6512207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512307 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 3, 5]
def baseStart_6512307 : Nat := 118140960795 + 6512307 * 2 ^ 59
def prefixEnd_6512307 : Nat := 4983230072969 + 3 ^ 40 * 6512307 * 2
def baseEnd_6512307 : Nat := 1114647886879852434204317

theorem tailTrace_6512307 : CollatzResearch.WordTrace tailWord_6512307 prefixEnd_6512307 1114647886879852434204317 := by
  unfold tailWord_6512307
  simp only [CollatzResearch.WordTrace]
  refine ⟨237523349618031427332871175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158348899745354284888580783 237523349618031427332871175)
  ·
    refine ⟨356285024427047140999306763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237523349618031427332871175 356285024427047140999306763)
    ·
      refine ⟨534427536640570711498960145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356285024427047140999306763 534427536640570711498960145)
      ·
        refine ⟨400820652480428033624220109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534427536640570711498960145 400820652480428033624220109)
        ·
          refine ⟨150307744680160512609082541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400820652480428033624220109 150307744680160512609082541)
          ·
            refine ⟨56365404255060192228405953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150307744680160512609082541 56365404255060192228405953)
            ·
              refine ⟨42274053191295144171304465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56365404255060192228405953 42274053191295144171304465)
              ·
                refine ⟨31705539893471358128478349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42274053191295144171304465 31705539893471358128478349)
                ·
                  refine ⟨11889577460051759298179381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31705539893471358128478349 11889577460051759298179381)
                  ·
                    refine ⟨1114647886879852434204317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11889577460051759298179381 1114647886879852434204317)
                    ·
                      rfl

theorem cell23_6512307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 5].length) (baseStart_6512307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512307 prefixEnd_6512307 := by exact prefixLift 6512307
  have htrace : WordTrace (prefixWord ++ tailWord_6512307) baseStart_6512307 baseEnd_6512307 := by
    simpa [prefixWord, tailWord_6512307, baseEnd_6512307] using wordTrace_append hprefix tailTrace_6512307
  have hstable : (prefixWord ++ tailWord_6512307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512307).length < 2 ^ (prefixWord ++ tailWord_6512307).sum := by decide
  have hdescent : baseEnd_6512307 < baseStart_6512307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512311 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 6]
def baseStart_6512311 : Nat := 118140960795 + 6512311 * 2 ^ 59
def prefixEnd_6512311 : Nat := 4983230072969 + 3 ^ 40 * 6512311 * 2
def baseEnd_6512311 : Nat := 371549523840241698551437

theorem tailTrace_6512311 : CollatzResearch.WordTrace tailWord_6512311 prefixEnd_6512311 371549523840241698551437 := by
  unfold tailWord_6512311
  simp only [CollatzResearch.WordTrace]
  refine ⟨237523495510016936016016787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158348997006677957344011191 237523495510016936016016787)
  ·
    refine ⟨356285243265025404024025181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237523495510016936016016787 356285243265025404024025181)
    ·
      refine ⟨133606966224384526509009443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356285243265025404024025181 133606966224384526509009443)
      ·
        refine ⟨200410449336576789763514165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133606966224384526509009443 200410449336576789763514165)
        ·
          refine ⟨18788479625304074040329453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200410449336576789763514165 18788479625304074040329453)
          ·
            refine ⟨7045679859489027765123545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18788479625304074040329453 7045679859489027765123545)
            ·
              refine ⟨5284259894616770823842659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7045679859489027765123545 5284259894616770823842659)
              ·
                refine ⟨7926389841925156235763989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284259894616770823842659 7926389841925156235763989)
                ·
                  refine ⟨371549523840241698551437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7926389841925156235763989 371549523840241698551437)
                  ·
                    rfl

theorem cell23_6512311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 6].length) (baseStart_6512311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512311 prefixEnd_6512311 := by exact prefixLift 6512311
  have htrace : WordTrace (prefixWord ++ tailWord_6512311) baseStart_6512311 baseEnd_6512311 := by
    simpa [prefixWord, tailWord_6512311, baseEnd_6512311] using wordTrace_append hprefix tailTrace_6512311
  have hstable : (prefixWord ++ tailWord_6512311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512311).length < 2 ^ (prefixWord ++ tailWord_6512311).sum := by decide
  have hdescent : baseEnd_6512311 < baseStart_6512311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512324 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_6512324 : Nat := 118140960795 + 6512324 * 2 ^ 59
def prefixEnd_6512324 : Nat := 4983230072969 + 3 ^ 40 * 6512324 * 2
def baseEnd_6512324 : Nat := 1114650796603561245366791

theorem tailTrace_6512324 : CollatzResearch.WordTrace tailWord_6512324 prefixEnd_6512324 1114650796603561245366791 := by
  unfold tailWord_6512324
  simp only [CollatzResearch.WordTrace]
  refine ⟨118761984829484919618120013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158349313105979892824160017 118761984829484919618120013)
  ·
    refine ⟨44535744311056844856795005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118761984829484919618120013 44535744311056844856795005)
    ·
      refine ⟨16700904116646316821298127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44535744311056844856795005 16700904116646316821298127)
      ·
        refine ⟨25051356174969475231947191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16700904116646316821298127 25051356174969475231947191)
        ·
          refine ⟨37577034262454212847920787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25051356174969475231947191 37577034262454212847920787)
          ·
            refine ⟨56365551393681319271881181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37577034262454212847920787 56365551393681319271881181)
            ·
              refine ⟨21137081772630494726955443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56365551393681319271881181 21137081772630494726955443)
              ·
                refine ⟨31705622658945742090433165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21137081772630494726955443 31705622658945742090433165)
                ·
                  refine ⟨11889608497104653283912437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31705622658945742090433165 11889608497104653283912437)
                  ·
                    refine ⟨1114650796603561245366791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11889608497104653283912437 1114650796603561245366791)
                    ·
                      rfl

theorem cell23_6512324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_6512324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512324 prefixEnd_6512324 := by exact prefixLift 6512324
  have htrace : WordTrace (prefixWord ++ tailWord_6512324) baseStart_6512324 baseEnd_6512324 := by
    simpa [prefixWord, tailWord_6512324, baseEnd_6512324] using wordTrace_append hprefix tailTrace_6512324
  have hstable : (prefixWord ++ tailWord_6512324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512324).length < 2 ^ (prefixWord ++ tailWord_6512324).sum := by decide
  have hdescent : baseEnd_6512324 < baseStart_6512324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512337 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_6512337 : Nat := 118140960795 + 6512337 * 2 ^ 59
def prefixEnd_6512337 : Nat := 4983230072969 + 3 ^ 40 * 6512337 * 2
def baseEnd_6512337 : Nat := 1114653021686397395079271

theorem tailTrace_6512337 : CollatzResearch.WordTrace tailWord_6512337 prefixEnd_6512337 1114653021686397395079271 := by
  unfold tailWord_6512337
  simp only [CollatzResearch.WordTrace]
  refine ⟨237524443807922742456463265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158349629205281828304308843 237524443807922742456463265)
  ·
    refine ⟨178143332855942056842347449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237524443807922742456463265 178143332855942056842347449)
    ·
      refine ⟨133607499641956542631760587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178143332855942056842347449 133607499641956542631760587)
      ·
        refine ⟨200411249462934813947640881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133607499641956542631760587 200411249462934813947640881)
        ·
          refine ⟨150308437097201110460730661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200411249462934813947640881 150308437097201110460730661)
          ·
            refine ⟨28182831955725208211386999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150308437097201110460730661 28182831955725208211386999)
            ·
              refine ⟨42274247933587812317080499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28182831955725208211386999 42274247933587812317080499)
              ·
                refine ⟨63411371900381718475620749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42274247933587812317080499 63411371900381718475620749)
                ·
                  refine ⟨23779264462643144428357781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63411371900381718475620749 23779264462643144428357781)
                  ·
                    refine ⟨1114653021686397395079271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23779264462643144428357781 1114653021686397395079271)
                    ·
                      rfl

theorem cell23_6512337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_6512337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512337 prefixEnd_6512337 := by exact prefixLift 6512337
  have htrace : WordTrace (prefixWord ++ tailWord_6512337) baseStart_6512337 baseEnd_6512337 := by
    simpa [prefixWord, tailWord_6512337, baseEnd_6512337] using wordTrace_append hprefix tailTrace_6512337
  have hstable : (prefixWord ++ tailWord_6512337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512337).length < 2 ^ (prefixWord ++ tailWord_6512337).sum := by decide
  have hdescent : baseEnd_6512337 < baseStart_6512337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512349 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6512349 : Nat := 118140960795 + 6512349 * 2 ^ 59
def prefixEnd_6512349 : Nat := 4983230072969 + 3 ^ 40 * 6512349 * 2
def baseEnd_6512349 : Nat := 1114655075609015379429253

theorem tailTrace_6512349 : CollatzResearch.WordTrace tailWord_6512349 prefixEnd_6512349 1114655075609015379429253 := by
  unfold tailWord_6512349
  simp only [CollatzResearch.WordTrace]
  refine ⟨237524881483879268505900101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158349920989252845670600067 237524881483879268505900101)
  ·
    refine ⟨44535915278227362844856269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237524881483879268505900101 44535915278227362844856269)
    ·
      refine ⟨16700968229335261066821101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44535915278227362844856269 16700968229335261066821101)
      ·
        refine ⟨6262863086000722900057913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16700968229335261066821101 6262863086000722900057913)
        ·
          refine ⟨4697147314500542175043435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262863086000722900057913 4697147314500542175043435)
          ·
            refine ⟨7045720971750813262565153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697147314500542175043435 7045720971750813262565153)
            ·
              refine ⟨5284290728813109946923865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7045720971750813262565153 5284290728813109946923865)
              ·
                refine ⟨3963218046609832460192899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5284290728813109946923865 3963218046609832460192899)
                ·
                  refine ⟨5944827069914748690289349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963218046609832460192899 5944827069914748690289349)
                  ·
                    refine ⟨1114655075609015379429253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5944827069914748690289349 1114655075609015379429253)
                    ·
                      rfl

theorem cell23_6512349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6512349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512349 prefixEnd_6512349 := by exact prefixLift 6512349
  have htrace : WordTrace (prefixWord ++ tailWord_6512349) baseStart_6512349 baseEnd_6512349 := by
    simpa [prefixWord, tailWord_6512349, baseEnd_6512349] using wordTrace_append hprefix tailTrace_6512349
  have hstable : (prefixWord ++ tailWord_6512349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512349).length < 2 ^ (prefixWord ++ tailWord_6512349).sum := by decide
  have hdescent : baseEnd_6512349 < baseStart_6512349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512355 : List Nat := [1, 1, 1, 7, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6512355 : Nat := 118140960795 + 6512355 * 2 ^ 59
def prefixEnd_6512355 : Nat := 4983230072969 + 3 ^ 40 * 6512355 * 2
def baseEnd_6512355 : Nat := 3343968307710973114812731

theorem tailTrace_6512355 : CollatzResearch.WordTrace tailWord_6512355 prefixEnd_6512355 3343968307710973114812731 := by
  unfold tailWord_6512355
  simp only [CollatzResearch.WordTrace]
  refine ⟨237525100321857531530618519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158350066881238354353745679 237525100321857531530618519)
  ·
    refine ⟨356287650482786297295927779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237525100321857531530618519 356287650482786297295927779)
    ·
      refine ⟨534431475724179445943891669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356287650482786297295927779 534431475724179445943891669)
      ·
        refine ⟨12525737712285455764309961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 534431475724179445943891669 12525737712285455764309961)
        ·
          refine ⟨9394303284214091823232471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12525737712285455764309961 9394303284214091823232471)
          ·
            refine ⟨14091454926321137734848707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9394303284214091823232471 14091454926321137734848707)
            ·
              refine ⟨21137182389481706602273061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14091454926321137734848707 21137182389481706602273061)
              ·
                refine ⟨3963221698027819987926199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21137182389481706602273061 3963221698027819987926199)
                ·
                  refine ⟨5944832547041729981889299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963221698027819987926199 5944832547041729981889299)
                  ·
                    refine ⟨8917248820562594972833949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5944832547041729981889299 8917248820562594972833949)
                    ·
                      refine ⟨3343968307710973114812731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8917248820562594972833949 3343968307710973114812731)
                      ·
                        rfl

theorem cell23_6512355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6512355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512355 prefixEnd_6512355 := by exact prefixLift 6512355
  have htrace : WordTrace (prefixWord ++ tailWord_6512355) baseStart_6512355 baseEnd_6512355 := by
    simpa [prefixWord, tailWord_6512355, baseEnd_6512355] using wordTrace_append hprefix tailTrace_6512355
  have hstable : (prefixWord ++ tailWord_6512355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512355).length < 2 ^ (prefixWord ++ tailWord_6512355).sum := by decide
  have hdescent : baseEnd_6512355 < baseStart_6512355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512361 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 3, 2, 2]
def baseStart_6512361 : Nat := 118140960795 + 6512361 * 2 ^ 59
def prefixEnd_6512361 : Nat := 4983230072969 + 3 ^ 40 * 6512361 * 2
def baseEnd_6512361 : Nat := 3343971388594900091337703

theorem tailTrace_6512361 : CollatzResearch.WordTrace tailWord_6512361 prefixEnd_6512361 3343971388594900091337703 := by
  unfold tailWord_6512361
  simp only [CollatzResearch.WordTrace]
  refine ⟨237525319159835794555336937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158350212773223863036891291 237525319159835794555336937)
  ·
    refine ⟨178143989369876845916502703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237525319159835794555336937 178143989369876845916502703)
    ·
      refine ⟨267215984054815268874754055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178143989369876845916502703 267215984054815268874754055)
      ·
        refine ⟨400823976082222903312131083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267215984054815268874754055 400823976082222903312131083)
        ·
          refine ⟨601235964123334354968196625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400823976082222903312131083 601235964123334354968196625)
          ·
            refine ⟨450926973092500766226147469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601235964123334354968196625 450926973092500766226147469)
            ·
              refine ⟨169097614909687787334805301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450926973092500766226147469 169097614909687787334805301)
              ·
                refine ⟨15852901397783230062637997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169097614909687787334805301 15852901397783230062637997)
                ·
                  refine ⟨5944838024168711273489249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15852901397783230062637997 5944838024168711273489249)
                  ·
                    refine ⟨4458628518126533455116937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5944838024168711273489249 4458628518126533455116937)
                    ·
                      refine ⟨3343971388594900091337703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458628518126533455116937 3343971388594900091337703)
                      ·
                        rfl

theorem cell23_6512361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 2, 2].length) (baseStart_6512361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512361 prefixEnd_6512361 := by exact prefixLift 6512361
  have htrace : WordTrace (prefixWord ++ tailWord_6512361) baseStart_6512361 baseEnd_6512361 := by
    simpa [prefixWord, tailWord_6512361, baseEnd_6512361] using wordTrace_append hprefix tailTrace_6512361
  have hstable : (prefixWord ++ tailWord_6512361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512361).length < 2 ^ (prefixWord ++ tailWord_6512361).sum := by decide
  have hdescent : baseEnd_6512361 < baseStart_6512361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512364 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_6512364 : Nat := 118140960795 + 6512364 * 2 ^ 59
def prefixEnd_6512364 : Nat := 4983230072969 + 3 ^ 40 * 6512364 * 2
def baseEnd_6512364 : Nat := 3343972929036863579600189

theorem tailTrace_6512364 : CollatzResearch.WordTrace tailWord_6512364 prefixEnd_6512364 3343972929036863579600189 := by
  unfold tailWord_6512364
  simp only [CollatzResearch.WordTrace]
  refine ⟨118762714289412463033848073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158350285719216617378464097 118762714289412463033848073)
  ·
    refine ⟨89072035717059347275386055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118762714289412463033848073 89072035717059347275386055)
    ·
      refine ⟨133608053575589020913079083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89072035717059347275386055 133608053575589020913079083)
      ·
        refine ⟨200412080363383531369618625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133608053575589020913079083 200412080363383531369618625)
        ·
          refine ⟨150309060272537648527213969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200412080363383531369618625 150309060272537648527213969)
          ·
            refine ⟨112731795204403236395410477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150309060272537648527213969 112731795204403236395410477)
            ·
              refine ⟨42274423201651213648278929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112731795204403236395410477 42274423201651213648278929)
              ·
                refine ⟨31705817401238410236209197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42274423201651213648278929 31705817401238410236209197)
                ·
                  refine ⟨11889681525464403838578449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31705817401238410236209197 11889681525464403838578449)
                  ·
                    refine ⟨8917261144098302878933837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11889681525464403838578449 8917261144098302878933837)
                    ·
                      refine ⟨3343972929036863579600189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8917261144098302878933837 3343972929036863579600189)
                      ·
                        rfl

theorem cell23_6512364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_6512364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512364 prefixEnd_6512364 := by exact prefixLift 6512364
  have htrace : WordTrace (prefixWord ++ tailWord_6512364) baseStart_6512364 baseEnd_6512364 := by
    simpa [prefixWord, tailWord_6512364, baseEnd_6512364] using wordTrace_append hprefix tailTrace_6512364
  have hstable : (prefixWord ++ tailWord_6512364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512364).length < 2 ^ (prefixWord ++ tailWord_6512364).sum := by decide
  have hdescent : baseEnd_6512364 < baseStart_6512364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512382 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_6512382 : Nat := 118140960795 + 6512382 * 2 ^ 59
def prefixEnd_6512382 : Nat := 4983230072969 + 3 ^ 40 * 6512382 * 2
def baseEnd_6512382 : Nat := 3343982171688644509175107

theorem tailTrace_6512382 : CollatzResearch.WordTrace tailWord_6512382 prefixEnd_6512382 3343982171688644509175107 := by
  unfold tailWord_6512382
  simp only [CollatzResearch.WordTrace]
  refine ⟨29690760636594964392731425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158350723395173143427900933 29690760636594964392731425)
  ·
    refine ⟨22268070477446223294548569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29690760636594964392731425 22268070477446223294548569)
    ·
      refine ⟨16701052858084667470911427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22268070477446223294548569 16701052858084667470911427)
      ·
        refine ⟨25051579287127001206367141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16701052858084667470911427 25051579287127001206367141)
        ·
          refine ⟨4697171116336312726193839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25051579287127001206367141 4697171116336312726193839)
          ·
            refine ⟨7045756674504469089290759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697171116336312726193839 7045756674504469089290759)
            ·
              refine ⟨10568635011756703633936139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7045756674504469089290759 10568635011756703633936139)
              ·
                refine ⟨15852952517635055450904209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10568635011756703633936139 15852952517635055450904209)
                ·
                  refine ⟨11889714388226291588178157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15852952517635055450904209 11889714388226291588178157)
                  ·
                    refine ⟨4458642895584859345566809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11889714388226291588178157 4458642895584859345566809)
                    ·
                      refine ⟨3343982171688644509175107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458642895584859345566809 3343982171688644509175107)
                      ·
                        rfl

theorem cell23_6512382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_6512382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512382 prefixEnd_6512382 := by exact prefixLift 6512382
  have htrace : WordTrace (prefixWord ++ tailWord_6512382) baseStart_6512382 baseEnd_6512382 := by
    simpa [prefixWord, tailWord_6512382, baseEnd_6512382] using wordTrace_append hprefix tailTrace_6512382
  have hstable : (prefixWord ++ tailWord_6512382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512382).length < 2 ^ (prefixWord ++ tailWord_6512382).sum := by decide
  have hdescent : baseEnd_6512382 < baseStart_6512382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512398 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_6512398 : Nat := 118140960795 + 6512398 * 2 ^ 59
def prefixEnd_6512398 : Nat := 4983230072969 + 3 ^ 40 * 6512398 * 2
def baseEnd_6512398 : Nat := 3343990387379116446575033

theorem tailTrace_6512398 : CollatzResearch.WordTrace tailWord_6512398 prefixEnd_6512398 3343990387379116446575033 := by
  unfold tailWord_6512398
  simp only [CollatzResearch.WordTrace]
  refine ⟨29690833582587718734304231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158351112440467833249622565 29690833582587718734304231)
  ·
    refine ⟨44536250373881578101456347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29690833582587718734304231 44536250373881578101456347)
    ·
      refine ⟨66804375560822367152184521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44536250373881578101456347 66804375560822367152184521)
      ·
        refine ⟨50103281670616775364138391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66804375560822367152184521 50103281670616775364138391)
        ·
          refine ⟨75154922505925163046207587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50103281670616775364138391 75154922505925163046207587)
          ·
            refine ⟨112732383758887744569311381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75154922505925163046207587 112732383758887744569311381)
            ·
              refine ⟨5284330488697863026686471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112732383758887744569311381 5284330488697863026686471)
              ·
                refine ⟨7926495733046794540029707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284330488697863026686471 7926495733046794540029707)
                ·
                  refine ⟨11889743599570191810044561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7926495733046794540029707 11889743599570191810044561)
                  ·
                    refine ⟨8917307699677643857533421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11889743599570191810044561 8917307699677643857533421)
                    ·
                      refine ⟨3343990387379116446575033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8917307699677643857533421 3343990387379116446575033)
                      ·
                        rfl

theorem cell23_6512398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_6512398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512398 prefixEnd_6512398 := by exact prefixLift 6512398
  have htrace : WordTrace (prefixWord ++ tailWord_6512398) baseStart_6512398 baseEnd_6512398 := by
    simpa [prefixWord, tailWord_6512398, baseEnd_6512398] using wordTrace_append hprefix tailTrace_6512398
  have hstable : (prefixWord ++ tailWord_6512398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512398).length < 2 ^ (prefixWord ++ tailWord_6512398).sum := by decide
  have hdescent : baseEnd_6512398 < baseStart_6512398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512427 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 6, 6]
def baseStart_6512427 : Nat := 118140960795 + 6512427 * 2 ^ 59
def prefixEnd_6512427 : Nat := 4983230072969 + 3 ^ 40 * 6512427 * 2
def baseEnd_6512427 : Nat := 1114668426106032277704133

theorem tailTrace_6512427 : CollatzResearch.WordTrace tailWord_6512427 prefixEnd_6512427 1114668426106032277704133 := by
  unfold tailWord_6512427
  simp only [CollatzResearch.WordTrace]
  refine ⟨237527726377596687827239535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158351817585064458551493023 237527726377596687827239535)
  ·
    refine ⟨356291589566395031740859303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237527726377596687827239535 356291589566395031740859303)
    ·
      refine ⟨534437384349592547611288955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356291589566395031740859303 534437384349592547611288955)
      ·
        refine ⟨801656076524388821416933433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534437384349592547611288955 801656076524388821416933433)
        ·
          refine ⟨601242057393291616062700075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 801656076524388821416933433 601242057393291616062700075)
          ·
            refine ⟨901863086089937424094050113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601242057393291616062700075 901863086089937424094050113)
            ·
              refine ⟨676397314567453068070537585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901863086089937424094050113 676397314567453068070537585)
              ·
                refine ⟨507297985925589801052903189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676397314567453068070537585 507297985925589801052903189)
                ·
                  refine ⟨23779593090262021924354837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 507297985925589801052903189 23779593090262021924354837)
                  ·
                    refine ⟨1114668426106032277704133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23779593090262021924354837 1114668426106032277704133)
                    ·
                      rfl

theorem cell23_6512427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_6512427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512427 prefixEnd_6512427 := by exact prefixLift 6512427
  have htrace : WordTrace (prefixWord ++ tailWord_6512427) baseStart_6512427 baseEnd_6512427 := by
    simpa [prefixWord, tailWord_6512427, baseEnd_6512427] using wordTrace_append hprefix tailTrace_6512427
  have hstable : (prefixWord ++ tailWord_6512427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512427).length < 2 ^ (prefixWord ++ tailWord_6512427).sum := by decide
  have hdescent : baseEnd_6512427 < baseStart_6512427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512524 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_6512524 : Nat := 118140960795 + 6512524 * 2 ^ 59
def prefixEnd_6512524 : Nat := 4983230072969 + 3 ^ 40 * 6512524 * 2
def baseEnd_6512524 : Nat := 3344055085941582953599453

theorem tailTrace_6512524 : CollatzResearch.WordTrace tailWord_6512524 prefixEnd_6512524 3344055085941582953599453 := by
  unfold tailWord_6512524
  simp only [CollatzResearch.WordTrace]
  refine ⟨118765632129122636696760313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158354176172163515595680417 118765632129122636696760313)
  ·
    refine ⟨89074224096841977522570235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118765632129122636696760313 89074224096841977522570235)
    ·
      refine ⟨133611336145262966283855353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89074224096841977522570235 133611336145262966283855353)
      ·
        refine ⟨100208502108947224712891515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133611336145262966283855353 100208502108947224712891515)
        ·
          refine ⟨150312753163420837069337273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100208502108947224712891515 150312753163420837069337273)
          ·
            refine ⟨112734564872565627802002955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150312753163420837069337273 112734564872565627802002955)
            ·
              refine ⟨169101847308848441703004433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112734564872565627802002955 169101847308848441703004433)
              ·
                refine ⟨126826385481636331277253325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169101847308848441703004433 126826385481636331277253325)
                ·
                  refine ⟨47559894555613624228969997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126826385481636331277253325 47559894555613624228969997)
                  ·
                    refine ⟨17834960458355109085863749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47559894555613624228969997 17834960458355109085863749)
                    ·
                      refine ⟨3344055085941582953599453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17834960458355109085863749 3344055085941582953599453)
                      ·
                        rfl

theorem cell23_6512524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_6512524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512524 prefixEnd_6512524 := by exact prefixLift 6512524
  have htrace : WordTrace (prefixWord ++ tailWord_6512524) baseStart_6512524 baseEnd_6512524 := by
    simpa [prefixWord, tailWord_6512524, baseEnd_6512524] using wordTrace_append hprefix tailTrace_6512524
  have hstable : (prefixWord ++ tailWord_6512524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512524).length < 2 ^ (prefixWord ++ tailWord_6512524).sum := by decide
  have hdescent : baseEnd_6512524 < baseStart_6512524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512618 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_6512618 : Nat := 118140960795 + 6512618 * 2 ^ 59
def prefixEnd_6512618 : Nat := 4983230072969 + 3 ^ 40 * 6512618 * 2
def baseEnd_6512618 : Nat := 3344103353123105585824021

theorem tailTrace_6512618 : CollatzResearch.WordTrace tailWord_6512618 prefixEnd_6512618 3344103353123105585824021 := by
  unfold tailWord_6512618
  simp only [CollatzResearch.WordTrace]
  refine ⟨59383673179976181861860627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158356461813269818298295005 59383673179976181861860627)
  ·
    refine ⟨89075509769964272792790941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59383673179976181861860627 89075509769964272792790941)
    ·
      refine ⟨33403316163736602297296603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89075509769964272792790941 33403316163736602297296603)
      ·
        refine ⟨50104974245604903445944905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33403316163736602297296603 50104974245604903445944905)
        ·
          refine ⟨37578730684203677584458679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50104974245604903445944905 37578730684203677584458679)
          ·
            refine ⟨56368096026305516376688019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37578730684203677584458679 56368096026305516376688019)
            ·
              refine ⟨84552144039458274565032029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56368096026305516376688019 84552144039458274565032029)
              ·
                refine ⟨31707054014796852961887011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84552144039458274565032029 31707054014796852961887011)
                ·
                  refine ⟨47560581022195279442830517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31707054014796852961887011 47560581022195279442830517)
                  ·
                    refine ⟨4458804470830807447765361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47560581022195279442830517 4458804470830807447765361)
                    ·
                      refine ⟨3344103353123105585824021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458804470830807447765361 3344103353123105585824021)
                      ·
                        rfl

theorem cell23_6512618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_6512618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512618 prefixEnd_6512618 := by exact prefixLift 6512618
  have htrace : WordTrace (prefixWord ++ tailWord_6512618) baseStart_6512618 baseEnd_6512618 := by
    simpa [prefixWord, tailWord_6512618, baseEnd_6512618] using wordTrace_append hprefix tailTrace_6512618
  have hstable : (prefixWord ++ tailWord_6512618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512618).length < 2 ^ (prefixWord ++ tailWord_6512618).sum := by decide
  have hdescent : baseEnd_6512618 < baseStart_6512618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512651 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5]
def baseStart_6512651 : Nat := 118140960795 + 6512651 * 2 ^ 59
def prefixEnd_6512651 : Nat := 4983230072969 + 3 ^ 40 * 6512651 * 2
def baseEnd_6512651 : Nat := 3344120297984703956711369

theorem tailTrace_6512651 : CollatzResearch.WordTrace tailWord_6512651 prefixEnd_6512651 3344120297984703956711369 := by
  unfold tailWord_6512651
  simp only [CollatzResearch.WordTrace]
  refine ⟨237535896328785174083393807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158357264219190116055595871 237535896328785174083393807)
  ·
    refine ⟨356303844493177761125090711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237535896328785174083393807 356303844493177761125090711)
    ·
      refine ⟨534455766739766641687636067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356303844493177761125090711 534455766739766641687636067)
      ·
        refine ⟨801683650109649962531454101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534455766739766641687636067 801683650109649962531454101)
        ·
          refine ⟨37578921098889841993661911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 801683650109649962531454101 37578921098889841993661911)
          ·
            refine ⟨56368381648334762990492867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37578921098889841993661911 56368381648334762990492867)
            ·
              refine ⟨84552572472502144485739301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56368381648334762990492867 84552572472502144485739301)
              ·
                refine ⟨15853607338594152091076119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84552572472502144485739301 15853607338594152091076119)
                ·
                  refine ⟨23780411007891228136614179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15853607338594152091076119 23780411007891228136614179)
                  ·
                    refine ⟨35670616511836842204921269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23780411007891228136614179 35670616511836842204921269)
                    ·
                      refine ⟨3344120297984703956711369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35670616511836842204921269 3344120297984703956711369)
                      ·
                        rfl

theorem cell23_6512651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 5].length) (baseStart_6512651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512651 prefixEnd_6512651 := by exact prefixLift 6512651
  have htrace : WordTrace (prefixWord ++ tailWord_6512651) baseStart_6512651 baseEnd_6512651 := by
    simpa [prefixWord, tailWord_6512651, baseEnd_6512651] using wordTrace_append hprefix tailTrace_6512651
  have hstable : (prefixWord ++ tailWord_6512651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512651).length < 2 ^ (prefixWord ++ tailWord_6512651).sum := by decide
  have hdescent : baseEnd_6512651 < baseStart_6512651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512682 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6512682 : Nat := 118140960795 + 6512682 * 2 ^ 59
def prefixEnd_6512682 : Nat := 4983230072969 + 3 ^ 40 * 6512682 * 2
def baseEnd_6512682 : Nat := 3344136215884993335423727

theorem tailTrace_6512682 : CollatzResearch.WordTrace tailWord_6512682 prefixEnd_6512682 3344136215884993335423727 := by
  unfold tailWord_6512682
  simp only [CollatzResearch.WordTrace]
  refine ⟨59384256747918216594443075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158358017994448577585181533 59384256747918216594443075)
  ·
    refine ⟨89076385121877324891664613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59384256747918216594443075 89076385121877324891664613)
    ·
      refine ⟨16701822210351998417187115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89076385121877324891664613 16701822210351998417187115)
      ·
        refine ⟨25052733315527997625780673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16701822210351998417187115 25052733315527997625780673)
        ·
          refine ⟨18789549986645998219335505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25052733315527997625780673 18789549986645998219335505)
          ·
            refine ⟨14092162489984498664501629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18789549986645998219335505 14092162489984498664501629)
            ·
              refine ⟨5284560933744186999188111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14092162489984498664501629 5284560933744186999188111)
              ·
                refine ⟨7926841400616280498782167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284560933744186999188111 7926841400616280498782167)
                ·
                  refine ⟨11890262100924420748173251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7926841400616280498782167 11890262100924420748173251)
                  ·
                    refine ⟨17835393151386631122259877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11890262100924420748173251 17835393151386631122259877)
                    ·
                      refine ⟨3344136215884993335423727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17835393151386631122259877 3344136215884993335423727)
                      ·
                        rfl

theorem cell23_6512682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6512682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512682 prefixEnd_6512682 := by exact prefixLift 6512682
  have htrace : WordTrace (prefixWord ++ tailWord_6512682) baseStart_6512682 baseEnd_6512682 := by
    simpa [prefixWord, tailWord_6512682, baseEnd_6512682] using wordTrace_append hprefix tailTrace_6512682
  have hstable : (prefixWord ++ tailWord_6512682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512682).length < 2 ^ (prefixWord ++ tailWord_6512682).sum := by decide
  have hdescent : baseEnd_6512682 < baseStart_6512682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512701 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_6512701 : Nat := 118140960795 + 6512701 * 2 ^ 59
def prefixEnd_6512701 : Nat := 4983230072969 + 3 ^ 40 * 6512701 * 2
def baseEnd_6512701 : Nat := 1114715324005809587028713

theorem tailTrace_6512701 : CollatzResearch.WordTrace tailWord_6512701 prefixEnd_6512701 1114715324005809587028713 := by
  unfold tailWord_6512701
  simp only [CollatzResearch.WordTrace]
  refine ⟨237537719978604032622713957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158358479985736021748475971 237537719978604032622713957)
  ·
    refine ⟨44538322495988256116758867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237537719978604032622713957 44538322495988256116758867)
    ·
      refine ⟨66807483743982384175138301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44538322495988256116758867 66807483743982384175138301)
      ·
        refine ⟨25052806403993394065676863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66807483743982384175138301 25052806403993394065676863)
        ·
          refine ⟨37579209605990091098515295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25052806403993394065676863 37579209605990091098515295)
          ·
            refine ⟨56368814408985136647772943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37579209605990091098515295 56368814408985136647772943)
            ·
              refine ⟨84553221613477704971659415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56368814408985136647772943 84553221613477704971659415)
              ·
                refine ⟨126829832420216557457489123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84553221613477704971659415 126829832420216557457489123)
                ·
                  refine ⟨190244748630324836186233685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126829832420216557457489123 190244748630324836186233685)
                  ·
                    refine ⟨1114715324005809587028713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 190244748630324836186233685 1114715324005809587028713)
                    ·
                      rfl

theorem cell23_6512701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_6512701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512701 prefixEnd_6512701 := by exact prefixLift 6512701
  have htrace : WordTrace (prefixWord ++ tailWord_6512701) baseStart_6512701 baseEnd_6512701 := by
    simpa [prefixWord, tailWord_6512701, baseEnd_6512701] using wordTrace_append hprefix tailTrace_6512701
  have hstable : (prefixWord ++ tailWord_6512701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512701).length < 2 ^ (prefixWord ++ tailWord_6512701).sum := by decide
  have hdescent : baseEnd_6512701 < baseStart_6512701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512721 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_6512721 : Nat := 118140960795 + 6512721 * 2 ^ 59
def prefixEnd_6512721 : Nat := 4983230072969 + 3 ^ 40 * 6512721 * 2
def baseEnd_6512721 : Nat := 3344156241630518682836047

theorem tailTrace_6512721 : CollatzResearch.WordTrace tailWord_6512721 prefixEnd_6512721 3344156241630518682836047 := by
  unfold tailWord_6512721
  simp only [CollatzResearch.WordTrace]
  refine ⟨237538449438531576038442017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158358966292354384025628011 237538449438531576038442017)
  ·
    refine ⟨178153837078898682028831513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237538449438531576038442017 178153837078898682028831513)
    ·
      refine ⟨133615377809174011521623635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178153837078898682028831513 133615377809174011521623635)
      ·
        refine ⟨200423066713761017282435453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133615377809174011521623635 200423066713761017282435453)
        ·
          refine ⟨75158650017660381480913295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200423066713761017282435453 75158650017660381480913295)
          ·
            refine ⟨112737975026490572221369943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75158650017660381480913295 112737975026490572221369943)
            ·
              refine ⟨169106962539735858332054915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112737975026490572221369943 169106962539735858332054915)
              ·
                refine ⟨253660443809603787498082373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169106962539735858332054915 253660443809603787498082373)
                ·
                  refine ⟨47561333214300710155890445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253660443809603787498082373 47561333214300710155890445)
                  ·
                    refine ⟨17835499955362766308458917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47561333214300710155890445 17835499955362766308458917)
                    ·
                      refine ⟨3344156241630518682836047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17835499955362766308458917 3344156241630518682836047)
                      ·
                        rfl

theorem cell23_6512721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_6512721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512721 prefixEnd_6512721 := by exact prefixLift 6512721
  have htrace : WordTrace (prefixWord ++ tailWord_6512721) baseStart_6512721 baseEnd_6512721 := by
    simpa [prefixWord, tailWord_6512721, baseEnd_6512721] using wordTrace_append hprefix tailTrace_6512721
  have hstable : (prefixWord ++ tailWord_6512721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512721).length < 2 ^ (prefixWord ++ tailWord_6512721).sum := by decide
  have hdescent : baseEnd_6512721 < baseStart_6512721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512725 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_6512725 : Nat := 118140960795 + 6512725 * 2 ^ 59
def prefixEnd_6512725 : Nat := 4983230072969 + 3 ^ 40 * 6512725 * 2
def baseEnd_6512725 : Nat := 3344158295553136667186029

theorem tailTrace_6512725 : CollatzResearch.WordTrace tailWord_6512725 prefixEnd_6512725 3344158295553136667186029 := by
  unfold tailWord_6512725
  simp only [CollatzResearch.WordTrace]
  refine ⟨237538595330517084721587629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158359063553678056481058419 237538595330517084721587629)
  ·
    refine ⟨89076973248943906770595361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237538595330517084721587629 89076973248943906770595361)
    ·
      refine ⟨66807729936707930077946521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89076973248943906770595361 66807729936707930077946521)
      ·
        refine ⟨50105797452530947558459891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66807729936707930077946521 50105797452530947558459891)
        ·
          refine ⟨75158696178796421337689837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50105797452530947558459891 75158696178796421337689837)
          ·
            refine ⟨28184511067048658001633689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75158696178796421337689837 28184511067048658001633689)
            ·
              refine ⟨21138383300286493501225267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28184511067048658001633689 21138383300286493501225267)
              ·
                refine ⟨31707574950429740251837901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21138383300286493501225267 31707574950429740251837901)
                ·
                  refine ⟨11890340606411152594439213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31707574950429740251837901 11890340606411152594439213)
                  ·
                    refine ⟨4458877727404182222914705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11890340606411152594439213 4458877727404182222914705)
                    ·
                      refine ⟨3344158295553136667186029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4458877727404182222914705 3344158295553136667186029)
                      ·
                        rfl

theorem cell23_6512725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_6512725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512725 prefixEnd_6512725 := by exact prefixLift 6512725
  have htrace : WordTrace (prefixWord ++ tailWord_6512725) baseStart_6512725 baseEnd_6512725 := by
    simpa [prefixWord, tailWord_6512725, baseEnd_6512725] using wordTrace_append hprefix tailTrace_6512725
  have hstable : (prefixWord ++ tailWord_6512725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512725).length < 2 ^ (prefixWord ++ tailWord_6512725).sum := by decide
  have hdescent : baseEnd_6512725 < baseStart_6512725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512778 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_6512778 : Nat := 118140960795 + 6512778 * 2 ^ 59
def prefixEnd_6512778 : Nat := 4983230072969 + 3 ^ 40 * 6512778 * 2
def baseEnd_6512778 : Nat := 371576167780869439980365

theorem tailTrace_6512778 : CollatzResearch.WordTrace tailWord_6512778 prefixEnd_6512778 371576167780869439980365 := by
  unfold tailWord_6512778
  simp only [CollatzResearch.WordTrace]
  refine ⟨59385132099831268693316747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158360352266216716515511325 59385132099831268693316747)
  ·
    refine ⟨89077698149746903039975121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59385132099831268693316747 89077698149746903039975121)
    ·
      refine ⟨66808273612310177279981341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89077698149746903039975121 66808273612310177279981341)
      ·
        refine ⟨25053102604616316479993003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66808273612310177279981341 25053102604616316479993003)
        ·
          refine ⟨37579653906924474719989505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25053102604616316479993003 37579653906924474719989505)
          ·
            refine ⟨28184740430193356039992129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37579653906924474719989505 28184740430193356039992129)
            ·
              refine ⟨21138555322645017029994097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28184740430193356039992129 21138555322645017029994097)
              ·
                refine ⟨15853916491983762772495573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21138555322645017029994097 15853916491983762772495573)
                ·
                  refine ⟨371576167780869439980365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15853916491983762772495573 371576167780869439980365)
                  ·
                    rfl

theorem cell23_6512778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_6512778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512778 prefixEnd_6512778 := by exact prefixLift 6512778
  have htrace : WordTrace (prefixWord ++ tailWord_6512778) baseStart_6512778 baseEnd_6512778 := by
    simpa [prefixWord, tailWord_6512778, baseEnd_6512778] using wordTrace_append hprefix tailTrace_6512778
  have hstable : (prefixWord ++ tailWord_6512778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512778).length < 2 ^ (prefixWord ++ tailWord_6512778).sum := by decide
  have hdescent : baseEnd_6512778 < baseStart_6512778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512818 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6512818 : Nat := 118140960795 + 6512818 * 2 ^ 59
def prefixEnd_6512818 : Nat := 4983230072969 + 3 ^ 40 * 6512818 * 2
def baseEnd_6512818 : Nat := 3344206049254004803323101

theorem tailTrace_6512818 : CollatzResearch.WordTrace tailWord_6512818 prefixEnd_6512818 3344206049254004803323101 := by
  unfold tailWord_6512818
  simp only [CollatzResearch.WordTrace]
  refine ⟨59385496829795040401180777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158361324879453441069815405 59385496829795040401180777)
  ·
    refine ⟨44539122622346280300885583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59385496829795040401180777 44539122622346280300885583)
    ·
      refine ⟨66808683933519420451328375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44539122622346280300885583 66808683933519420451328375)
      ·
        refine ⟨100213025900279130676992563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66808683933519420451328375 100213025900279130676992563)
        ·
          refine ⟨150319538850418696015488845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100213025900279130676992563 150319538850418696015488845)
          ·
            refine ⟨56369827068907011005808317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150319538850418696015488845 56369827068907011005808317)
            ·
              refine ⟨21138685150840129127178119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56369827068907011005808317 21138685150840129127178119)
              ·
                refine ⟨31708027726260193690767179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21138685150840129127178119 31708027726260193690767179)
                ·
                  refine ⟨47562041589390290536150769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31708027726260193690767179 47562041589390290536150769)
                  ·
                    refine ⟨35671531192042717902113077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47562041589390290536150769 35671531192042717902113077)
                    ·
                      refine ⟨3344206049254004803323101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35671531192042717902113077 3344206049254004803323101)
                      ·
                        rfl

theorem cell23_6512818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6512818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512818 prefixEnd_6512818 := by exact prefixLift 6512818
  have htrace : WordTrace (prefixWord ++ tailWord_6512818) baseStart_6512818 baseEnd_6512818 := by
    simpa [prefixWord, tailWord_6512818, baseEnd_6512818] using wordTrace_append hprefix tailTrace_6512818
  have hstable : (prefixWord ++ tailWord_6512818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512818).length < 2 ^ (prefixWord ++ tailWord_6512818).sum := by decide
  have hdescent : baseEnd_6512818 < baseStart_6512818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512865 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_6512865 : Nat := 118140960795 + 6512865 * 2 ^ 59
def prefixEnd_6512865 : Nat := 4983230072969 + 3 ^ 40 * 6512865 * 2
def baseEnd_6512865 : Nat := 3344230182844766119435385

theorem tailTrace_6512865 : CollatzResearch.WordTrace tailWord_6512865 prefixEnd_6512865 3344230182844766119435385 := by
  unfold tailWord_6512865
  simp only [CollatzResearch.WordTrace]
  refine ⟨237543701550009888631684049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158362467700006592421122699 237543701550009888631684049)
  ·
    refine ⟨178157776162507416473763037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237543701550009888631684049 178157776162507416473763037)
    ·
      refine ⟨66809166060940281177661139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178157776162507416473763037 66809166060940281177661139)
      ·
        refine ⟨100213749091410421766491709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66809166060940281177661139 100213749091410421766491709)
        ·
          refine ⟨37580155909278908162434391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100213749091410421766491709 37580155909278908162434391)
          ·
            refine ⟨56370233863918362243651587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37580155909278908162434391 56370233863918362243651587)
            ·
              refine ⟨84555350795877543365477381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56370233863918362243651587 84555350795877543365477381)
              ·
                refine ⟨15854128274227039381027009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84555350795877543365477381 15854128274227039381027009)
                ·
                  refine ⟨11890596205670279535770257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15854128274227039381027009 11890596205670279535770257)
                  ·
                    refine ⟨8917947154252709651827693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11890596205670279535770257 8917947154252709651827693)
                    ·
                      refine ⟨3344230182844766119435385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8917947154252709651827693 3344230182844766119435385)
                      ·
                        rfl

theorem cell23_6512865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_6512865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512865 prefixEnd_6512865 := by exact prefixLift 6512865
  have htrace : WordTrace (prefixWord ++ tailWord_6512865) baseStart_6512865 baseEnd_6512865 := by
    simpa [prefixWord, tailWord_6512865, baseEnd_6512865] using wordTrace_append hprefix tailTrace_6512865
  have hstable : (prefixWord ++ tailWord_6512865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512865).length < 2 ^ (prefixWord ++ tailWord_6512865).sum := by decide
  have hdescent : baseEnd_6512865 < baseStart_6512865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512929 : List Nat := [1, 2, 3, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_6512929 : Nat := 118140960795 + 6512929 * 2 ^ 59
def prefixEnd_6512929 : Nat := 4983230072969 + 3 ^ 40 * 6512929 * 2
def baseEnd_6512929 : Nat := 3344263045606653869035091

theorem tailTrace_6512929 : CollatzResearch.WordTrace tailWord_6512929 prefixEnd_6512929 3344263045606653869035091 := by
  unfold tailWord_6512929
  simp only [CollatzResearch.WordTrace]
  refine ⟨237546035821778027562013841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158364023881185351708009227 237546035821778027562013841)
  ·
    refine ⟨178159526866333520671510381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237546035821778027562013841 178159526866333520671510381)
    ·
      refine ⟨66809822574875070251816393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178159526866333520671510381 66809822574875070251816393)
      ·
        refine ⟨50107366931156302688862295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66809822574875070251816393 50107366931156302688862295)
        ·
          refine ⟨75161050396734454033293443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50107366931156302688862295 75161050396734454033293443)
          ·
            refine ⟨112741575595101681049940165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75161050396734454033293443 112741575595101681049940165)
            ·
              refine ⟨21139045424081565196863781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112741575595101681049940165 21139045424081565196863781)
              ·
                refine ⟨3963571017015293474411959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21139045424081565196863781 3963571017015293474411959)
                ·
                  refine ⟨5945356525522940211617939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963571017015293474411959 5945356525522940211617939)
                  ·
                    refine ⟨8918034788284410317426909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5945356525522940211617939 8918034788284410317426909)
                    ·
                      refine ⟨3344263045606653869035091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8918034788284410317426909 3344263045606653869035091)
                      ·
                        rfl

theorem cell23_6512929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_6512929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512929 prefixEnd_6512929 := by exact prefixLift 6512929
  have htrace : WordTrace (prefixWord ++ tailWord_6512929) baseStart_6512929 baseEnd_6512929 := by
    simpa [prefixWord, tailWord_6512929, baseEnd_6512929] using wordTrace_append hprefix tailTrace_6512929
  have hstable : (prefixWord ++ tailWord_6512929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512929).length < 2 ^ (prefixWord ++ tailWord_6512929).sum := by decide
  have hdescent : baseEnd_6512929 < baseStart_6512929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6512972 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_6512972 : Nat := 118140960795 + 6512972 * 2 ^ 59
def prefixEnd_6512972 : Nat := 4983230072969 + 3 ^ 40 * 6512972 * 2
def baseEnd_6512972 : Nat := 3344285125274797200797393

theorem tailTrace_6512972 : CollatzResearch.WordTrace tailWord_6512972 prefixEnd_6512972 3344285125274797200797393 := by
  unfold tailWord_6512972
  simp only [CollatzResearch.WordTrace]
  refine ⟨118773802080311122952914585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158365069440414830603886113 118773802080311122952914585)
  ·
    refine ⟨89080351560233342214685939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118773802080311122952914585 89080351560233342214685939)
    ·
      refine ⟨133620527340350013322028909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89080351560233342214685939 133620527340350013322028909)
      ·
        refine ⟨50107697752631254995760841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133620527340350013322028909 50107697752631254995760841)
        ·
          refine ⟨37580773314473441246820631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50107697752631254995760841 37580773314473441246820631)
          ·
            refine ⟨56371159971710161870230947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37580773314473441246820631 56371159971710161870230947)
            ·
              refine ⟨84556739957565242805346421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56371159971710161870230947 84556739957565242805346421)
              ·
                refine ⟨7927194371021741513001227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84556739957565242805346421 7927194371021741513001227)
                ·
                  refine ⟨11890791556532612269501841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7927194371021741513001227 11890791556532612269501841)
                  ·
                    refine ⟨8918093667399459202126381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11890791556532612269501841 8918093667399459202126381)
                    ·
                      refine ⟨3344285125274797200797393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8918093667399459202126381 3344285125274797200797393)
                      ·
                        rfl

theorem cell23_6512972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_6512972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6512972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6512972 prefixEnd_6512972 := by exact prefixLift 6512972
  have htrace : WordTrace (prefixWord ++ tailWord_6512972) baseStart_6512972 baseEnd_6512972 := by
    simpa [prefixWord, tailWord_6512972, baseEnd_6512972] using wordTrace_append hprefix tailTrace_6512972
  have hstable : (prefixWord ++ tailWord_6512972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6512972).length < 2 ^ (prefixWord ++ tailWord_6512972).sum := by decide
  have hdescent : baseEnd_6512972 < baseStart_6512972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6512972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513059 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 1, 4, 2]
def baseStart_6513059 : Nat := 118140960795 + 6513059 * 2 ^ 59
def prefixEnd_6513059 : Nat := 4983230072969 + 3 ^ 40 * 6513059 * 2
def baseEnd_6513059 : Nat := 3344329798091738360409493

theorem tailTrace_6513059 : CollatzResearch.WordTrace tailWord_6513059 prefixEnd_6513059 3344329798091738360409493 := by
  unfold tailWord_6513059
  simp only [CollatzResearch.WordTrace]
  refine ⟨237550777311307059764246231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158367184874204706509497487 237550777311307059764246231)
  ·
    refine ⟨356326165966960589646369347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237550777311307059764246231 356326165966960589646369347)
    ·
      refine ⟨534489248950440884469554021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356326165966960589646369347 534489248950440884469554021)
      ·
        refine ⟨100216734178207665838041379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534489248950440884469554021 100216734178207665838041379)
        ·
          refine ⟨150325101267311498757062069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100216734178207665838041379 150325101267311498757062069)
          ·
            refine ⟨14092978243810453008474569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150325101267311498757062069 14092978243810453008474569)
            ·
              refine ⟨10569733682857839756355927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14092978243810453008474569 10569733682857839756355927)
              ·
                refine ⟨15854600524286759634533891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10569733682857839756355927 15854600524286759634533891)
                ·
                  refine ⟨23781900786430139451800837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15854600524286759634533891 23781900786430139451800837)
                  ·
                    refine ⟨4459106397455651147212657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23781900786430139451800837 4459106397455651147212657)
                    ·
                      refine ⟨3344329798091738360409493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459106397455651147212657 3344329798091738360409493)
                      ·
                        rfl

theorem cell23_6513059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_6513059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513059 prefixEnd_6513059 := by exact prefixLift 6513059
  have htrace : WordTrace (prefixWord ++ tailWord_6513059) baseStart_6513059 baseEnd_6513059 := by
    simpa [prefixWord, tailWord_6513059, baseEnd_6513059] using wordTrace_append hprefix tailTrace_6513059
  have hstable : (prefixWord ++ tailWord_6513059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513059).length < 2 ^ (prefixWord ++ tailWord_6513059).sum := by decide
  have hdescent : baseEnd_6513059 < baseStart_6513059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513105 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_6513105 : Nat := 118140960795 + 6513105 * 2 ^ 59
def prefixEnd_6513105 : Nat := 4983230072969 + 3 ^ 40 * 6513105 * 2
def baseEnd_6513105 : Nat := 3344353418201845180434281

theorem tailTrace_6513105 : CollatzResearch.WordTrace tailWord_6513105 prefixEnd_6513105 3344353418201845180434281 := by
  unfold tailWord_6513105
  simp only [CollatzResearch.WordTrace]
  refine ⟨237552455069140409620420769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158368303379426939746947179 237552455069140409620420769)
  ·
    refine ⟨178164341301855307215315577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237552455069140409620420769 178164341301855307215315577)
    ·
      refine ⟨133623255976391480411486683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178164341301855307215315577 133623255976391480411486683)
      ·
        refine ⟨200434883964587220617230025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133623255976391480411486683 200434883964587220617230025)
        ·
          refine ⟨150326162973440415462922519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200434883964587220617230025 150326162973440415462922519)
          ·
            refine ⟨225489244460160623194383779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150326162973440415462922519 225489244460160623194383779)
            ·
              refine ⟨338233866690240934791575669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225489244460160623194383779 338233866690240934791575669)
              ·
                refine ⟨31709425002210087636710219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338233866690240934791575669 31709425002210087636710219)
                ·
                  refine ⟨47564137503315131455065329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31709425002210087636710219 47564137503315131455065329)
                  ·
                    refine ⟨35673103127486348591298997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47564137503315131455065329 35673103127486348591298997)
                    ·
                      refine ⟨3344353418201845180434281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35673103127486348591298997 3344353418201845180434281)
                      ·
                        rfl

theorem cell23_6513105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_6513105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513105 prefixEnd_6513105 := by exact prefixLift 6513105
  have htrace : WordTrace (prefixWord ++ tailWord_6513105) baseStart_6513105 baseEnd_6513105 := by
    simpa [prefixWord, tailWord_6513105, baseEnd_6513105] using wordTrace_append hprefix tailTrace_6513105
  have hstable : (prefixWord ++ tailWord_6513105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513105).length < 2 ^ (prefixWord ++ tailWord_6513105).sum := by decide
  have hdescent : baseEnd_6513105 < baseStart_6513105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513110 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_6513110 : Nat := 118140960795 + 6513110 * 2 ^ 59
def prefixEnd_6513110 : Nat := 4983230072969 + 3 ^ 40 * 6513110 * 2
def baseEnd_6513110 : Nat := 3344355985605117660871759

theorem tailTrace_6513110 : CollatzResearch.WordTrace tailWord_6513110 prefixEnd_6513110 3344355985605117660871759 := by
  unfold tailWord_6513110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14847039839632643467147049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158368424956081530316235189 14847039839632643467147049)
  ·
    refine ⟨11135279879724482600360287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14847039839632643467147049 11135279879724482600360287)
    ·
      refine ⟨16702919819586723900540431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11135279879724482600360287 16702919819586723900540431)
      ·
        refine ⟨25054379729380085850810647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16702919819586723900540431 25054379729380085850810647)
        ·
          refine ⟨37581569594070128776215971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25054379729380085850810647 37581569594070128776215971)
          ·
            refine ⟨56372354391105193164323957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37581569594070128776215971 56372354391105193164323957)
            ·
              refine ⟨5284908224166111859155371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56372354391105193164323957 5284908224166111859155371)
              ·
                refine ⟨7927362336249167788733057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5284908224166111859155371 7927362336249167788733057)
                ·
                  refine ⟨5945521752186875841549793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927362336249167788733057 5945521752186875841549793)
                  ·
                    refine ⟨4459141314140156881162345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5945521752186875841549793 4459141314140156881162345)
                    ·
                      refine ⟨3344355985605117660871759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459141314140156881162345 3344355985605117660871759)
                      ·
                        rfl

theorem cell23_6513110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_6513110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513110 prefixEnd_6513110 := by exact prefixLift 6513110
  have htrace : WordTrace (prefixWord ++ tailWord_6513110) baseStart_6513110 baseEnd_6513110 := by
    simpa [prefixWord, tailWord_6513110, baseEnd_6513110] using wordTrace_append hprefix tailTrace_6513110
  have hstable : (prefixWord ++ tailWord_6513110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513110).length < 2 ^ (prefixWord ++ tailWord_6513110).sum := by decide
  have hdescent : baseEnd_6513110 < baseStart_6513110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513132 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_6513132 : Nat := 118140960795 + 6513132 * 2 ^ 59
def prefixEnd_6513132 : Nat := 4983230072969 + 3 ^ 40 * 6513132 * 2
def baseEnd_6513132 : Nat := 3344367282179516574796657

theorem tailTrace_6513132 : CollatzResearch.WordTrace tailWord_6513132 prefixEnd_6513132 3344367282179516574796657 := by
  unfold tailWord_6513132
  simp only [CollatzResearch.WordTrace]
  refine ⟨118776719920021296615826825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158368959893361728821102433 118776719920021296615826825)
  ·
    refine ⟨89082539940015972461870119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118776719920021296615826825 89082539940015972461870119)
    ·
      refine ⟨133623809910023958692805179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89082539940015972461870119 133623809910023958692805179)
      ·
        refine ⟨200435714865035938039207769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133623809910023958692805179 200435714865035938039207769)
        ·
          refine ⟨150326786148776953529405827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200435714865035938039207769 150326786148776953529405827)
          ·
            refine ⟨225490179223165430294108741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150326786148776953529405827 225490179223165430294108741)
            ·
              refine ⟨42279408604343518180145389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225490179223165430294108741 42279408604343518180145389)
              ·
                refine ⟨15854778226628819317554521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42279408604343518180145389 15854778226628819317554521)
                ·
                  refine ⟨11891083669971614488165891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15854778226628819317554521 11891083669971614488165891)
                  ·
                    refine ⟨17836625504957421732248837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11891083669971614488165891 17836625504957421732248837)
                    ·
                      refine ⟨3344367282179516574796657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17836625504957421732248837 3344367282179516574796657)
                      ·
                        rfl

theorem cell23_6513132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_6513132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513132 prefixEnd_6513132 := by exact prefixLift 6513132
  have htrace : WordTrace (prefixWord ++ tailWord_6513132) baseStart_6513132 baseEnd_6513132 := by
    simpa [prefixWord, tailWord_6513132, baseEnd_6513132] using wordTrace_append hprefix tailTrace_6513132
  have hstable : (prefixWord ++ tailWord_6513132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513132).length < 2 ^ (prefixWord ++ tailWord_6513132).sum := by decide
  have hdescent : baseEnd_6513132 < baseStart_6513132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513135 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_6513135 : Nat := 118140960795 + 6513135 * 2 ^ 59
def prefixEnd_6513135 : Nat := 4983230072969 + 3 ^ 40 * 6513135 * 2
def baseEnd_6513135 : Nat := 3344368822621480063059143

theorem tailTrace_6513135 : CollatzResearch.WordTrace tailWord_6513135 prefixEnd_6513135 3344368822621480063059143 := by
  unfold tailWord_6513135
  simp only [CollatzResearch.WordTrace]
  refine ⟨237553549259031724744012859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158369032839354483162675239 237553549259031724744012859)
  ·
    refine ⟨356330323888547587116019289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237553549259031724744012859 356330323888547587116019289)
    ·
      refine ⟨267247742916410690337014467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356330323888547587116019289 267247742916410690337014467)
      ·
        refine ⟨400871614374616035505521701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267247742916410690337014467 400871614374616035505521701)
        ·
          refine ⟨75163427695240506657285319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400871614374616035505521701 75163427695240506657285319)
          ·
            refine ⟨112745141542860759985927979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75163427695240506657285319 112745141542860759985927979)
            ·
              refine ⟨169117712314291139978891969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112745141542860759985927979 169117712314291139978891969)
              ·
                refine ⟨126838284235718354984168977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169117712314291139978891969 126838284235718354984168977)
                ·
                  refine ⟨95128713176788766238126733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126838284235718354984168977 95128713176788766238126733)
                  ·
                    refine ⟨35673267441295787339297525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95128713176788766238126733 35673267441295787339297525)
                    ·
                      refine ⟨3344368822621480063059143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35673267441295787339297525 3344368822621480063059143)
                      ·
                        rfl

theorem cell23_6513135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_6513135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513135 prefixEnd_6513135 := by exact prefixLift 6513135
  have htrace : WordTrace (prefixWord ++ tailWord_6513135) baseStart_6513135 baseEnd_6513135 := by
    simpa [prefixWord, tailWord_6513135, baseEnd_6513135] using wordTrace_append hprefix tailTrace_6513135
  have hstable : (prefixWord ++ tailWord_6513135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513135).length < 2 ^ (prefixWord ++ tailWord_6513135).sum := by decide
  have hdescent : baseEnd_6513135 < baseStart_6513135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513145 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_6513145 : Nat := 118140960795 + 6513145 * 2 ^ 59
def prefixEnd_6513145 : Nat := 4983230072969 + 3 ^ 40 * 6513145 * 2
def baseEnd_6513145 : Nat := 3344373957428025023934097

theorem tailTrace_6513145 : CollatzResearch.WordTrace tailWord_6513145 prefixEnd_6513145 3344373957428025023934097 := by
  unfold tailWord_6513145
  simp only [CollatzResearch.WordTrace]
  refine ⟨237553913988995496451876889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158369275992663664301251259 237553913988995496451876889)
  ·
    refine ⟨178165435491746622338907667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237553913988995496451876889 178165435491746622338907667)
    ·
      refine ⟨267248153237619933508361501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178165435491746622338907667 267248153237619933508361501)
      ·
        refine ⟨100218057464107475065635563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267248153237619933508361501 100218057464107475065635563)
        ·
          refine ⟨150327086196161212598453345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100218057464107475065635563 150327086196161212598453345)
          ·
            refine ⟨112745314647120909448840009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150327086196161212598453345 112745314647120909448840009)
            ·
              refine ⟨84558985985340682086630007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112745314647120909448840009 84558985985340682086630007)
              ·
                refine ⟨126838478978011023129945011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84558985985340682086630007 126838478978011023129945011)
                ·
                  refine ⟨190257718467016534694917517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126838478978011023129945011 190257718467016534694917517)
                  ·
                    refine ⟨71346644425131200510594069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190257718467016534694917517 71346644425131200510594069)
                    ·
                      refine ⟨3344373957428025023934097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71346644425131200510594069 3344373957428025023934097)
                      ·
                        rfl

theorem cell23_6513145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_6513145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513145 prefixEnd_6513145 := by exact prefixLift 6513145
  have htrace : WordTrace (prefixWord ++ tailWord_6513145) baseStart_6513145 baseEnd_6513145 := by
    simpa [prefixWord, tailWord_6513145, baseEnd_6513145] using wordTrace_append hprefix tailTrace_6513145
  have hstable : (prefixWord ++ tailWord_6513145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513145).length < 2 ^ (prefixWord ++ tailWord_6513145).sum := by decide
  have hdescent : baseEnd_6513145 < baseStart_6513145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513155 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 8]
def baseStart_6513155 : Nat := 118140960795 + 6513155 * 2 ^ 59
def prefixEnd_6513155 : Nat := 4983230072969 + 3 ^ 40 * 6513155 * 2
def baseEnd_6513155 : Nat := 371597676914952220534339

theorem tailTrace_6513155 : CollatzResearch.WordTrace tailWord_6513155 prefixEnd_6513155 371597676914952220534339 := by
  unfold tailWord_6513155
  simp only [CollatzResearch.WordTrace]
  refine ⟨237554278718959268159740919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158369519145972845439827279 237554278718959268159740919)
  ·
    refine ⟨356331418078438902239611379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237554278718959268159740919 356331418078438902239611379)
    ·
      refine ⟨534497127117658353359417069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356331418078438902239611379 534497127117658353359417069)
      ·
        refine ⟨200436422669121882509781401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534497127117658353359417069 200436422669121882509781401)
        ·
          refine ⟨150327317001841411882336051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200436422669121882509781401 150327317001841411882336051)
          ·
            refine ⟨225490975502762117823504077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150327317001841411882336051 225490975502762117823504077)
            ·
              refine ⟨84559115813535794183814029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225490975502762117823504077 84559115813535794183814029)
              ·
                refine ⟨31709668430075922818930261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84559115813535794183814029 31709668430075922818930261)
                ·
                  refine ⟨371597676914952220534339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31709668430075922818930261 371597676914952220534339)
                  ·
                    rfl

theorem cell23_6513155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 8].length) (baseStart_6513155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513155 prefixEnd_6513155 := by exact prefixLift 6513155
  have htrace : WordTrace (prefixWord ++ tailWord_6513155) baseStart_6513155 baseEnd_6513155 := by
    simpa [prefixWord, tailWord_6513155, baseEnd_6513155] using wordTrace_append hprefix tailTrace_6513155
  have hstable : (prefixWord ++ tailWord_6513155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513155).length < 2 ^ (prefixWord ++ tailWord_6513155).sum := by decide
  have hdescent : baseEnd_6513155 < baseStart_6513155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513195 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7]
def baseStart_6513195 : Nat := 118140960795 + 6513195 * 2 ^ 59
def prefixEnd_6513195 : Nat := 4983230072969 + 3 ^ 40 * 6513195 * 2
def baseEnd_6513195 : Nat := 3344399631460749828308867

theorem tailTrace_6513195 : CollatzResearch.WordTrace tailWord_6513195 prefixEnd_6513195 3344399631460749828308867 := by
  unfold tailWord_6513195
  simp only [CollatzResearch.WordTrace]
  refine ⟨237555737638814354991197039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158370491759209569994131359 237555737638814354991197039)
  ·
    refine ⟨356333606458221532486795559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237555737638814354991197039 356333606458221532486795559)
    ·
      refine ⟨534500409687332298730193339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356333606458221532486795559 534500409687332298730193339)
      ·
        refine ⟨801750614530998448095290009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534500409687332298730193339 801750614530998448095290009)
        ·
          refine ⟨601312960898248836071467507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 801750614530998448095290009 601312960898248836071467507)
          ·
            refine ⟨901969441347373254107201261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601312960898248836071467507 901969441347373254107201261)
            ·
              refine ⟨338238540505264970290200473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 901969441347373254107201261 338238540505264970290200473)
              ·
                refine ⟨253678905378948727717650355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338238540505264970290200473 253678905378948727717650355)
                ·
                  refine ⟨380518358068423091576475533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253678905378948727717650355 380518358068423091576475533)
                  ·
                    refine ⟨142694384275658659341178325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380518358068423091576475533 142694384275658659341178325)
                    ·
                      refine ⟨3344399631460749828308867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142694384275658659341178325 3344399631460749828308867)
                      ·
                        rfl

theorem cell23_6513195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_6513195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513195 prefixEnd_6513195 := by exact prefixLift 6513195
  have htrace : WordTrace (prefixWord ++ tailWord_6513195) baseStart_6513195 baseEnd_6513195 := by
    simpa [prefixWord, tailWord_6513195, baseEnd_6513195] using wordTrace_append hprefix tailTrace_6513195
  have hstable : (prefixWord ++ tailWord_6513195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513195).length < 2 ^ (prefixWord ++ tailWord_6513195).sum := by decide
  have hdescent : baseEnd_6513195 < baseStart_6513195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513206 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_6513206 : Nat := 118140960795 + 6513206 * 2 ^ 59
def prefixEnd_6513206 : Nat := 4983230072969 + 3 ^ 40 * 6513206 * 2
def baseEnd_6513206 : Nat := 371600586638661031696813

theorem tailTrace_6513206 : CollatzResearch.WordTrace tailWord_6513206 prefixEnd_6513206 371600586638661031696813 := by
  unfold tailWord_6513206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14847258677610906491865467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158370759227849669246564981 14847258677610906491865467)
  ·
    refine ⟨22270888016416359737798201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14847258677610906491865467 22270888016416359737798201)
    ·
      refine ⟨16703166012312269803348651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22270888016416359737798201 16703166012312269803348651)
      ·
        refine ⟨25054749018468404705022977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16703166012312269803348651 25054749018468404705022977)
        ·
          refine ⟨18791061763851303528767233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25054749018468404705022977 18791061763851303528767233)
          ·
            refine ⟨14093296322888477646575425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18791061763851303528767233 14093296322888477646575425)
            ·
              refine ⟨10569972242166358234931569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14093296322888477646575425 10569972242166358234931569)
              ·
                refine ⟨7927479181624768676198677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10569972242166358234931569 7927479181624768676198677)
                ·
                  refine ⟨371600586638661031696813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7927479181624768676198677 371600586638661031696813)
                  ·
                    rfl

theorem cell23_6513206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_6513206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513206 prefixEnd_6513206 := by exact prefixLift 6513206
  have htrace : WordTrace (prefixWord ++ tailWord_6513206) baseStart_6513206 baseEnd_6513206 := by
    simpa [prefixWord, tailWord_6513206, baseEnd_6513206] using wordTrace_append hprefix tailTrace_6513206
  have hstable : (prefixWord ++ tailWord_6513206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513206).length < 2 ^ (prefixWord ++ tailWord_6513206).sum := by decide
  have hdescent : baseEnd_6513206 < baseStart_6513206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513239 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_6513239 : Nat := 118140960795 + 6513239 * 2 ^ 59
def prefixEnd_6513239 : Nat := 4983230072969 + 3 ^ 40 * 6513239 * 2
def baseEnd_6513239 : Nat := 3344422224609547656158665

theorem tailTrace_6513239 : CollatzResearch.WordTrace tailWord_6513239 prefixEnd_6513239 3344422224609547656158665 := by
  unfold tailWord_6513239
  simp only [CollatzResearch.WordTrace]
  refine ⟨237557342450654950505798771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158371561633769967003865847 237557342450654950505798771)
  ·
    refine ⟨356336013675982425758698157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237557342450654950505798771 356336013675982425758698157)
    ·
      refine ⟨133626005128493409659511809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356336013675982425758698157 133626005128493409659511809)
      ·
        refine ⟨100219503846370057244633857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133626005128493409659511809 100219503846370057244633857)
        ·
          refine ⟨75164627884777542933475393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100219503846370057244633857 75164627884777542933475393)
          ·
            refine ⟨56373470913583157200106545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75164627884777542933475393 56373470913583157200106545)
            ·
              refine ⟨42280103185187367900079909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56373470913583157200106545 42280103185187367900079909)
              ·
                refine ⟨7927519347222631481264983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42280103185187367900079909 7927519347222631481264983)
                ·
                  refine ⟨11891279020833947221897475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7927519347222631481264983 11891279020833947221897475)
                  ·
                    refine ⟨17836918531250920832846213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11891279020833947221897475 17836918531250920832846213)
                    ·
                      refine ⟨3344422224609547656158665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17836918531250920832846213 3344422224609547656158665)
                      ·
                        rfl

theorem cell23_6513239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_6513239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513239 prefixEnd_6513239 := by exact prefixLift 6513239
  have htrace : WordTrace (prefixWord ++ tailWord_6513239) baseStart_6513239 baseEnd_6513239 := by
    simpa [prefixWord, tailWord_6513239, baseEnd_6513239] using wordTrace_append hprefix tailTrace_6513239
  have hstable : (prefixWord ++ tailWord_6513239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513239).length < 2 ^ (prefixWord ++ tailWord_6513239).sum := by decide
  have hdescent : baseEnd_6513239 < baseStart_6513239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513253 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_6513253 : Nat := 118140960795 + 6513253 * 2 ^ 59
def prefixEnd_6513253 : Nat := 4983230072969 + 3 ^ 40 * 6513253 * 2
def baseEnd_6513253 : Nat := 1114809804446236867127867

theorem tailTrace_6513253 : CollatzResearch.WordTrace tailWord_6513253 prefixEnd_6513253 1114809804446236867127867 := by
  unfold tailWord_6513253
  simp only [CollatzResearch.WordTrace]
  refine ⟨237557853072604230896808413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158371902048402820597872275 237557853072604230896808413)
  ·
    refine ⟨89084194902226586586303155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237557853072604230896808413 89084194902226586586303155)
    ·
      refine ⟨133626292353339879879454733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89084194902226586586303155 133626292353339879879454733)
      ·
        refine ⟨50109859632502454954795525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133626292353339879879454733 50109859632502454954795525)
        ·
          refine ⟨9395598681094210304024161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50109859632502454954795525 9395598681094210304024161)
          ·
            refine ⟨7046699010820657728018121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9395598681094210304024161 7046699010820657728018121)
            ·
              refine ⟨5285024258115493296013591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7046699010820657728018121 5285024258115493296013591)
              ·
                refine ⟨7927536387173239944020387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285024258115493296013591 7927536387173239944020387)
                ·
                  refine ⟨11891304580759859916030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7927536387173239944020387 11891304580759859916030581)
                  ·
                    refine ⟨1114809804446236867127867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11891304580759859916030581 1114809804446236867127867)
                    ·
                      rfl

theorem cell23_6513253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_6513253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513253 prefixEnd_6513253 := by exact prefixLift 6513253
  have htrace : WordTrace (prefixWord ++ tailWord_6513253) baseStart_6513253 baseEnd_6513253 := by
    simpa [prefixWord, tailWord_6513253, baseEnd_6513253] using wordTrace_append hprefix tailTrace_6513253
  have hstable : (prefixWord ++ tailWord_6513253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513253).length < 2 ^ (prefixWord ++ tailWord_6513253).sum := by decide
  have hdescent : baseEnd_6513253 < baseStart_6513253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513266 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_6513266 : Nat := 118140960795 + 6513266 * 2 ^ 59
def prefixEnd_6513266 : Nat := 4983230072969 + 3 ^ 40 * 6513266 * 2
def baseEnd_6513266 : Nat := 1114812029529073016840347

theorem tailTrace_6513266 : CollatzResearch.WordTrace tailWord_6513266 prefixEnd_6513266 1114812029529073016840347 := by
  unfold tailWord_6513266
  simp only [CollatzResearch.WordTrace]
  refine ⟨59389581805389283529257913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158372218147704756078021101 59389581805389283529257913)
  ·
    refine ⟨44542186354041962646943435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59389581805389283529257913 44542186354041962646943435)
    ·
      refine ⟨66813279531062943970415153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44542186354041962646943435 66813279531062943970415153)
      ·
        refine ⟨50109959648297207977811365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66813279531062943970415153 50109959648297207977811365)
        ·
          refine ⟨9395617434055726495839631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50109959648297207977811365 9395617434055726495839631)
          ·
            refine ⟨14093426151083589743759447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9395617434055726495839631 14093426151083589743759447)
            ·
              refine ⟨21140139226625384615639171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14093426151083589743759447 21140139226625384615639171)
              ·
                refine ⟨31710208839938076923458757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21140139226625384615639171 31710208839938076923458757)
                ·
                  refine ⟨5945664157488389423148517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31710208839938076923458757 5945664157488389423148517)
                  ·
                    refine ⟨1114812029529073016840347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945664157488389423148517 1114812029529073016840347)
                    ·
                      rfl

theorem cell23_6513266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_6513266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513266 prefixEnd_6513266 := by exact prefixLift 6513266
  have htrace : WordTrace (prefixWord ++ tailWord_6513266) baseStart_6513266 baseEnd_6513266 := by
    simpa [prefixWord, tailWord_6513266, baseEnd_6513266] using wordTrace_append hprefix tailTrace_6513266
  have hstable : (prefixWord ++ tailWord_6513266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513266).length < 2 ^ (prefixWord ++ tailWord_6513266).sum := by decide
  have hdescent : baseEnd_6513266 < baseStart_6513266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513273 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 3, 2, 2]
def baseStart_6513273 : Nat := 118140960795 + 6513273 * 2 ^ 59
def prefixEnd_6513273 : Nat := 4983230072969 + 3 ^ 40 * 6513273 * 2
def baseEnd_6513273 : Nat := 3344439682951800523133509

theorem tailTrace_6513273 : CollatzResearch.WordTrace tailWord_6513273 prefixEnd_6513273 3344439682951800523133509 := by
  unfold tailWord_6513273
  simp only [CollatzResearch.WordTrace]
  refine ⟨237558582532531774312536473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158372388355021182875024315 237558582532531774312536473)
  ·
    refine ⟨178168936899398830734402355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237558582532531774312536473 178168936899398830734402355)
    ·
      refine ⟨267253405349098246101603533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178168936899398830734402355 267253405349098246101603533)
      ·
        refine ⟨100220027005911842288101325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267253405349098246101603533 100220027005911842288101325)
        ·
          refine ⟨37582510127216940858037997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100220027005911842288101325 37582510127216940858037997)
          ·
            refine ⟨14093441297706352821764249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37582510127216940858037997 14093441297706352821764249)
            ·
              refine ⟨10570080973279764616323187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14093441297706352821764249 10570080973279764616323187)
              ·
                refine ⟨15855121459919646924484781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10570080973279764616323187 15855121459919646924484781)
                ·
                  refine ⟨5945670547469867596681793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15855121459919646924484781 5945670547469867596681793)
                  ·
                    refine ⟨4459252910602400697511345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5945670547469867596681793 4459252910602400697511345)
                    ·
                      refine ⟨3344439682951800523133509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459252910602400697511345 3344439682951800523133509)
                      ·
                        rfl

theorem cell23_6513273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_6513273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513273 prefixEnd_6513273 := by exact prefixLift 6513273
  have htrace : WordTrace (prefixWord ++ tailWord_6513273) baseStart_6513273 baseEnd_6513273 := by
    simpa [prefixWord, tailWord_6513273, baseEnd_6513273] using wordTrace_append hprefix tailTrace_6513273
  have hstable : (prefixWord ++ tailWord_6513273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513273).length < 2 ^ (prefixWord ++ tailWord_6513273).sum := by decide
  have hdescent : baseEnd_6513273 < baseStart_6513273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513334 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6513334 : Nat := 118140960795 + 6513334 * 2 ^ 59
def prefixEnd_6513334 : Nat := 4983230072969 + 3 ^ 40 * 6513334 * 2
def baseEnd_6513334 : Nat := 1114823668423908261490243

theorem tailTrace_6513334 : CollatzResearch.WordTrace tailWord_6513334 prefixEnd_6513334 1114823668423908261490243 := by
  unfold tailWord_6513334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14847550461581923858156691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158373871590207187820338037 14847550461581923858156691)
  ·
    refine ⟨22271325692372885787235037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14847550461581923858156691 22271325692372885787235037)
    ·
      refine ⟨8351747134639832170213139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22271325692372885787235037 8351747134639832170213139)
      ·
        refine ⟨12527620701959748255319709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8351747134639832170213139 12527620701959748255319709)
        ·
          refine ⟨4697857763234905595744891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12527620701959748255319709 4697857763234905595744891)
          ·
            refine ⟨7046786644852358393617337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697857763234905595744891 7046786644852358393617337)
            ·
              refine ⟨5285089983639268795213003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7046786644852358393617337 5285089983639268795213003)
              ·
                refine ⟨7927634975458903192819505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285089983639268795213003 7927634975458903192819505)
                ·
                  refine ⟨5945726231594177394614629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927634975458903192819505 5945726231594177394614629)
                  ·
                    refine ⟨1114823668423908261490243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945726231594177394614629 1114823668423908261490243)
                    ·
                      rfl

theorem cell23_6513334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6513334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513334 prefixEnd_6513334 := by exact prefixLift 6513334
  have htrace : WordTrace (prefixWord ++ tailWord_6513334) baseStart_6513334 baseEnd_6513334 := by
    simpa [prefixWord, tailWord_6513334, baseEnd_6513334] using wordTrace_append hprefix tailTrace_6513334
  have hstable : (prefixWord ++ tailWord_6513334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513334).length < 2 ^ (prefixWord ++ tailWord_6513334).sum := by decide
  have hdescent : baseEnd_6513334 < baseStart_6513334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513380 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_6513380 : Nat := 118140960795 + 6513380 * 2 ^ 59
def prefixEnd_6513380 : Nat := 4983230072969 + 3 ^ 40 * 6513380 * 2
def baseEnd_6513380 : Nat := 3344494625381831604495517

theorem tailTrace_6513380 : CollatzResearch.WordTrace tailWord_6513380 prefixEnd_6513380 3344494625381831604495517 := by
  unfold tailWord_6513380
  simp only [CollatzResearch.WordTrace]
  refine ⟨118781242571572065793340797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158374990095429421057787729 118781242571572065793340797)
  ·
    refine ⟨44542965964339524672502799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118781242571572065793340797 44542965964339524672502799)
    ·
      refine ⟨66814448946509287008754199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44542965964339524672502799 66814448946509287008754199)
      ·
        refine ⟨100221673419763930513131299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66814448946509287008754199 100221673419763930513131299)
        ·
          refine ⟨150332510129645895769696949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100221673419763930513131299 150332510129645895769696949)
          ·
            refine ⟨14093672824654302728409089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150332510129645895769696949 14093672824654302728409089)
            ·
              refine ⟨10570254618490727046306817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14093672824654302728409089 10570254618490727046306817)
              ·
                refine ⟨7927690963868045284730113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10570254618490727046306817 7927690963868045284730113)
                ·
                  refine ⟨5945768222901033963547585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927690963868045284730113 5945768222901033963547585)
                  ·
                    refine ⟨4459326167175775472660689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5945768222901033963547585 4459326167175775472660689)
                    ·
                      refine ⟨3344494625381831604495517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459326167175775472660689 3344494625381831604495517)
                      ·
                        rfl

theorem cell23_6513380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_6513380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513380 prefixEnd_6513380 := by exact prefixLift 6513380
  have htrace : WordTrace (prefixWord ++ tailWord_6513380) baseStart_6513380 baseEnd_6513380 := by
    simpa [prefixWord, tailWord_6513380, baseEnd_6513380] using wordTrace_append hprefix tailTrace_6513380
  have hstable : (prefixWord ++ tailWord_6513380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513380).length < 2 ^ (prefixWord ++ tailWord_6513380).sum := by decide
  have hdescent : baseEnd_6513380 < baseStart_6513380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513416 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 2, 5]
def baseStart_6513416 : Nat := 118140960795 + 6513416 * 2 ^ 59
def prefixEnd_6513416 : Nat := 4983230072969 + 3 ^ 40 * 6513416 * 2
def baseEnd_6513416 : Nat := 1114837703561797821215117

theorem tailTrace_6513416 : CollatzResearch.WordTrace tailWord_6513416 prefixEnd_6513416 1114837703561797821215117 := by
  unfold tailWord_6513416
  simp only [CollatzResearch.WordTrace]
  refine ⟨118781899085506854867496051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158375865447342473156661401 118781899085506854867496051)
  ·
    refine ⟨178172848628260282301244077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118781899085506854867496051 178172848628260282301244077)
    ·
      refine ⟨66814818235597605862966529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178172848628260282301244077 66814818235597605862966529)
      ·
        refine ⟨50111113676698204397224897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66814818235597605862966529 50111113676698204397224897)
        ·
          refine ⟨37583335257523653297918673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50111113676698204397224897 37583335257523653297918673)
          ·
            refine ⟨28187501443142739973439005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37583335257523653297918673 28187501443142739973439005)
            ·
              refine ⟨10570313041178527490039627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28187501443142739973439005 10570313041178527490039627)
              ·
                refine ⟨15855469561767791235059441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10570313041178527490039627 15855469561767791235059441)
                ·
                  refine ⟨11891602171325843426294581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15855469561767791235059441 11891602171325843426294581)
                  ·
                    refine ⟨1114837703561797821215117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11891602171325843426294581 1114837703561797821215117)
                    ·
                      rfl

theorem cell23_6513416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_6513416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513416 prefixEnd_6513416 := by exact prefixLift 6513416
  have htrace : WordTrace (prefixWord ++ tailWord_6513416) baseStart_6513416 baseEnd_6513416 := by
    simpa [prefixWord, tailWord_6513416, baseEnd_6513416] using wordTrace_append hprefix tailTrace_6513416
  have hstable : (prefixWord ++ tailWord_6513416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513416).length < 2 ^ (prefixWord ++ tailWord_6513416).sum := by decide
  have hdescent : baseEnd_6513416 < baseStart_6513416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513519 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 5, 6]
def baseStart_6513519 : Nat := 118140960795 + 6513519 * 2 ^ 59
def prefixEnd_6513519 : Nat := 4983230072969 + 3 ^ 40 * 6513519 * 2
def baseEnd_6513519 : Nat := 1114855333064268853552459

theorem tailTrace_6513519 : CollatzResearch.WordTrace tailWord_6513519 prefixEnd_6513519 1114855333064268853552459 := by
  unfold tailWord_6513519
  simp only [CollatzResearch.WordTrace]
  refine ⟨237567554889640558325991611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158378369926427038883994407 237567554889640558325991611)
  ·
    refine ⟨356351332334460837488987417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237567554889640558325991611 356351332334460837488987417)
    ·
      refine ⟨267263499250845628116740563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356351332334460837488987417 267263499250845628116740563)
      ·
        refine ⟨400895248876268442175110845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267263499250845628116740563 400895248876268442175110845)
        ·
          refine ⟨150335718328600665815666567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400895248876268442175110845 150335718328600665815666567)
          ·
            refine ⟨225503577492900998723499851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150335718328600665815666567 225503577492900998723499851)
            ·
              refine ⟨338255366239351498085249777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225503577492900998723499851 338255366239351498085249777)
              ·
                refine ⟨253691524679513623563937333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338255366239351498085249777 253691524679513623563937333)
                ·
                  refine ⟨23783580438704402209119125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253691524679513623563937333 23783580438704402209119125)
                  ·
                    refine ⟨1114855333064268853552459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23783580438704402209119125 1114855333064268853552459)
                    ·
                      rfl

theorem cell23_6513519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_6513519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513519 prefixEnd_6513519 := by exact prefixLift 6513519
  have htrace : WordTrace (prefixWord ++ tailWord_6513519) baseStart_6513519 baseEnd_6513519 := by
    simpa [prefixWord, tailWord_6513519, baseEnd_6513519] using wordTrace_append hprefix tailTrace_6513519
  have hstable : (prefixWord ++ tailWord_6513519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513519).length < 2 ^ (prefixWord ++ tailWord_6513519).sum := by decide
  have hdescent : baseEnd_6513519 < baseStart_6513519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513536 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 4, 4]
def baseStart_6513536 : Nat := 118140960795 + 6513536 * 2 ^ 59
def prefixEnd_6513536 : Nat := 4983230072969 + 3 ^ 40 * 6513536 * 2
def baseEnd_6513536 : Nat := 1114858242787977664714933

theorem tailTrace_6513536 : CollatzResearch.WordTrace tailWord_6513536 prefixEnd_6513536 1114858242787977664714933 := by
  unfold tailWord_6513536
  simp only [CollatzResearch.WordTrace]
  refine ⟨118784087465289485114680231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158378783287052646819573641 118784087465289485114680231)
  ·
    refine ⟨178176131197934227672020347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118784087465289485114680231 178176131197934227672020347)
    ·
      refine ⟨267264196796901341508030521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178176131197934227672020347 267264196796901341508030521)
      ·
        refine ⟨200448147597676006131022891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267264196796901341508030521 200448147597676006131022891)
        ·
          refine ⟨300672221396514009196534337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200448147597676006131022891 300672221396514009196534337)
          ·
            refine ⟨225504166047385506897400753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300672221396514009196534337 225504166047385506897400753)
            ·
              refine ⟨169128124535539130173050565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225504166047385506897400753 169128124535539130173050565)
              ·
                refine ⟨31711523350413586907446981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169128124535539130173050565 31711523350413586907446981)
                ·
                  refine ⟨5945910628202547545146309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31711523350413586907446981 5945910628202547545146309)
                  ·
                    refine ⟨1114858242787977664714933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945910628202547545146309 1114858242787977664714933)
                    ·
                      rfl

theorem cell23_6513536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 4].length) (baseStart_6513536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513536 prefixEnd_6513536 := by exact prefixLift 6513536
  have htrace : WordTrace (prefixWord ++ tailWord_6513536) baseStart_6513536 baseEnd_6513536 := by
    simpa [prefixWord, tailWord_6513536, baseEnd_6513536] using wordTrace_append hprefix tailTrace_6513536
  have hstable : (prefixWord ++ tailWord_6513536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513536).length < 2 ^ (prefixWord ++ tailWord_6513536).sum := by decide
  have hdescent : baseEnd_6513536 < baseStart_6513536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513554 : List Nat := [3, 2, 3, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_6513554 : Nat := 118140960795 + 6513554 * 2 ^ 59
def prefixEnd_6513554 : Nat := 4983230072969 + 3 ^ 40 * 6513554 * 2
def baseEnd_6513554 : Nat := 3344583971015713923719717

theorem tailTrace_6513554 : CollatzResearch.WordTrace tailWord_6513554 prefixEnd_6513554 3344583971015713923719717 := by
  unfold tailWord_6513554
  simp only [CollatzResearch.WordTrace]
  refine ⟨59392207861128439825878929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158379220963009172869010477 59392207861128439825878929)
  ·
    refine ⟨44544155895846329869409197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59392207861128439825878929 44544155895846329869409197)
    ·
      refine ⟨16704058460942373701028449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44544155895846329869409197 16704058460942373701028449)
      ·
        refine ⟨12528043845706780275771337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16704058460942373701028449 12528043845706780275771337)
        ·
          refine ⟨9396032884280085206828503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12528043845706780275771337 9396032884280085206828503)
          ·
            refine ⟨14094049326420127810242755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396032884280085206828503 14094049326420127810242755)
            ·
              refine ⟨21141073989630191715364133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14094049326420127810242755 21141073989630191715364133)
              ·
                refine ⟨3963951373055660946630775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21141073989630191715364133 3963951373055660946630775)
                ·
                  refine ⟨5945927059583491419946163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3963951373055660946630775 5945927059583491419946163)
                  ·
                    refine ⟨8918890589375237129919245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5945927059583491419946163 8918890589375237129919245)
                    ·
                      refine ⟨3344583971015713923719717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8918890589375237129919245 3344583971015713923719717)
                      ·
                        rfl

theorem cell23_6513554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_6513554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513554 prefixEnd_6513554 := by exact prefixLift 6513554
  have htrace : WordTrace (prefixWord ++ tailWord_6513554) baseStart_6513554 baseEnd_6513554 := by
    simpa [prefixWord, tailWord_6513554, baseEnd_6513554] using wordTrace_append hprefix tailTrace_6513554
  have hstable : (prefixWord ++ tailWord_6513554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513554).length < 2 ^ (prefixWord ++ tailWord_6513554).sum := by decide
  have hdescent : baseEnd_6513554 < baseStart_6513554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513570 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_6513570 : Nat := 118140960795 + 6513570 * 2 ^ 59
def prefixEnd_6513570 : Nat := 4983230072969 + 3 ^ 40 * 6513570 * 2
def baseEnd_6513570 : Nat := 1114864062235395287039881

theorem tailTrace_6513570 : CollatzResearch.WordTrace tailWord_6513570 prefixEnd_6513570 1114864062235395287039881 := by
  unfold tailWord_6513570
  simp only [CollatzResearch.WordTrace]
  refine ⟨59392353753113948509024541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158379610008303862690732109 59392353753113948509024541)
  ·
    refine ⟨22272132657417730690884203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59392353753113948509024541 22272132657417730690884203)
    ·
      refine ⟨33408198986126596036326305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22272132657417730690884203 33408198986126596036326305)
      ·
        refine ⟨25056149239594947027244729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33408198986126596036326305 25056149239594947027244729)
        ·
          refine ⟨18792111929696210270433547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25056149239594947027244729 18792111929696210270433547)
          ·
            refine ⟨28188167894544315405650321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18792111929696210270433547 28188167894544315405650321)
            ·
              refine ⟨21141125920908236554237741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28188167894544315405650321 21141125920908236554237741)
              ·
                refine ⟨7927922220340588707839153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21141125920908236554237741 7927922220340588707839153)
                ·
                  refine ⟨5945941665255441530879365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927922220340588707839153 5945941665255441530879365)
                  ·
                    refine ⟨1114864062235395287039881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945941665255441530879365 1114864062235395287039881)
                    ·
                      rfl

theorem cell23_6513570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_6513570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513570 prefixEnd_6513570 := by exact prefixLift 6513570
  have htrace : WordTrace (prefixWord ++ tailWord_6513570) baseStart_6513570 baseEnd_6513570 := by
    simpa [prefixWord, tailWord_6513570, baseEnd_6513570] using wordTrace_append hprefix tailTrace_6513570
  have hstable : (prefixWord ++ tailWord_6513570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513570).length < 2 ^ (prefixWord ++ tailWord_6513570).sum := by decide
  have hdescent : baseEnd_6513570 < baseStart_6513570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513581 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_6513581 : Nat := 118140960795 + 6513581 * 2 ^ 59
def prefixEnd_6513581 : Nat := 4983230072969 + 3 ^ 40 * 6513581 * 2
def baseEnd_6513581 : Nat := 3344597834993385318082093

theorem tailTrace_6513581 : CollatzResearch.WordTrace tailWord_6513581 prefixEnd_6513581 3344597834993385318082093 := by
  unfold tailWord_6513581
  simp only [CollatzResearch.WordTrace]
  refine ⟨237569816215415942914748597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158379877476943961943165731 237569816215415942914748597)
  ·
    refine ⟨22272170270195244648257681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237569816215415942914748597 22272170270195244648257681)
    ·
      refine ⟨16704127702646433486193261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22272170270195244648257681 16704127702646433486193261)
      ·
        refine ⟨6264047888492412557322473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16704127702646433486193261 6264047888492412557322473)
        ·
          refine ⟨4698035916369309417991855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264047888492412557322473 4698035916369309417991855)
          ·
            refine ⟨7047053874553964126987783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698035916369309417991855 7047053874553964126987783)
            ·
              refine ⟨10570580811830946190481675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7047053874553964126987783 10570580811830946190481675)
              ·
                refine ⟨15855871217746419285722513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10570580811830946190481675 15855871217746419285722513)
                ·
                  refine ⟨11891903413309814464291885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15855871217746419285722513 11891903413309814464291885)
                  ·
                    refine ⟨4459463779991180424109457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11891903413309814464291885 4459463779991180424109457)
                    ·
                      refine ⟨3344597834993385318082093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459463779991180424109457 3344597834993385318082093)
                      ·
                        rfl

theorem cell23_6513581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_6513581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513581 prefixEnd_6513581 := by exact prefixLift 6513581
  have htrace : WordTrace (prefixWord ++ tailWord_6513581) baseStart_6513581 baseEnd_6513581 := by
    simpa [prefixWord, tailWord_6513581, baseEnd_6513581] using wordTrace_append hprefix tailTrace_6513581
  have hstable : (prefixWord ++ tailWord_6513581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513581).length < 2 ^ (prefixWord ++ tailWord_6513581).sum := by decide
  have hdescent : baseEnd_6513581 < baseStart_6513581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513593 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6513593 : Nat := 118140960795 + 6513593 * 2 ^ 59
def prefixEnd_6513593 : Nat := 4983230072969 + 3 ^ 40 * 6513593 * 2
def baseEnd_6513593 : Nat := 3344603996761239271132037

theorem tailTrace_6513593 : CollatzResearch.WordTrace tailWord_6513593 prefixEnd_6513593 3344603996761239271132037 := by
  unfold tailWord_6513593
  simp only [CollatzResearch.WordTrace]
  refine ⟨237570253891372468964185433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158380169260914979309456955 237570253891372468964185433)
  ·
    refine ⟨178177690418529351723139075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237570253891372468964185433 178177690418529351723139075)
    ·
      refine ⟨267266535627794027584708613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178177690418529351723139075 267266535627794027584708613)
      ·
        refine ⟨50112475430211380172132865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267266535627794027584708613 50112475430211380172132865)
        ·
          refine ⟨37584356572658535129099649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50112475430211380172132865 37584356572658535129099649)
          ·
            refine ⟨28188267429493901346824737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37584356572658535129099649 28188267429493901346824737)
            ·
              refine ⟨21141200572120426010118553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28188267429493901346824737 21141200572120426010118553)
              ·
                refine ⟨15855900429090319507588915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21141200572120426010118553 15855900429090319507588915)
                ·
                  refine ⟨23783850643635479261383373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15855900429090319507588915 23783850643635479261383373)
                  ·
                    refine ⟨8918943991363304723018765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23783850643635479261383373 8918943991363304723018765)
                    ·
                      refine ⟨3344603996761239271132037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8918943991363304723018765 3344603996761239271132037)
                      ·
                        rfl

theorem cell23_6513593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6513593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513593 prefixEnd_6513593 := by exact prefixLift 6513593
  have htrace : WordTrace (prefixWord ++ tailWord_6513593) baseStart_6513593 baseEnd_6513593 := by
    simpa [prefixWord, tailWord_6513593, baseEnd_6513593] using wordTrace_append hprefix tailTrace_6513593
  have hstable : (prefixWord ++ tailWord_6513593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513593).length < 2 ^ (prefixWord ++ tailWord_6513593).sum := by decide
  have hdescent : baseEnd_6513593 < baseStart_6513593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513604 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_6513604 : Nat := 118140960795 + 6513604 * 2 ^ 59
def prefixEnd_6513604 : Nat := 4983230072969 + 3 ^ 40 * 6513604 * 2
def baseEnd_6513604 : Nat := 1114869881682812909364829

theorem tailTrace_6513604 : CollatzResearch.WordTrace tailWord_6513604 prefixEnd_6513604 1114869881682812909364829 := by
  unfold tailWord_6513604
  simp only [CollatzResearch.WordTrace]
  refine ⟨118785327547166308921417933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158380436729555078561890577 118785327547166308921417933)
  ·
    refine ⟨44544497830187365845531725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118785327547166308921417933 44544497830187365845531725)
    ·
      refine ⟨16704186686320262192074397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44544497830187365845531725 16704186686320262192074397)
      ·
        refine ⟨6264070007370098322027899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16704186686320262192074397 6264070007370098322027899)
        ·
          refine ⟨9396105011055147483041849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264070007370098322027899 9396105011055147483041849)
          ·
            refine ⟨7047078758291360612281387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9396105011055147483041849 7047078758291360612281387)
            ·
              refine ⟨10570618137437040918422081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7047078758291360612281387 10570618137437040918422081)
              ·
                refine ⟨7927963603077780688816561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10570618137437040918422081 7927963603077780688816561)
                ·
                  refine ⟨5945972702308335516612421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7927963603077780688816561 5945972702308335516612421)
                  ·
                    refine ⟨1114869881682812909364829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945972702308335516612421 1114869881682812909364829)
                    ·
                      rfl

theorem cell23_6513604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_6513604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513604 prefixEnd_6513604 := by exact prefixLift 6513604
  have htrace : WordTrace (prefixWord ++ tailWord_6513604) baseStart_6513604 baseEnd_6513604 := by
    simpa [prefixWord, tailWord_6513604, baseEnd_6513604] using wordTrace_append hprefix tailTrace_6513604
  have hstable : (prefixWord ++ tailWord_6513604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513604).length < 2 ^ (prefixWord ++ tailWord_6513604).sum := by decide
  have hdescent : baseEnd_6513604 < baseStart_6513604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513673 : List Nat := [1, 2, 1, 1, 3, 1, 1, 8, 5]
def baseStart_6513673 : Nat := 118140960795 + 6513673 * 2 ^ 59
def prefixEnd_6513673 : Nat := 4983230072969 + 3 ^ 40 * 6513673 * 2
def baseEnd_6513673 : Nat := 371627230579288773125741

theorem tailTrace_6513673 : CollatzResearch.WordTrace tailWord_6513673 prefixEnd_6513673 371627230579288773125741 := by
  unfold tailWord_6513673
  simp only [CollatzResearch.WordTrace]
  refine ⟨237573171731082642627097673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158382114487388428418065115 237573171731082642627097673)
  ·
    refine ⟨178179878798311981970323255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237573171731082642627097673 178179878798311981970323255)
    ·
      refine ⟨267269818197467972955484883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178179878798311981970323255 267269818197467972955484883)
      ·
        refine ⟨400904727296201959433227325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267269818197467972955484883 400904727296201959433227325)
        ·
          refine ⟨150339272736075734787460247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400904727296201959433227325 150339272736075734787460247)
          ·
            refine ⟨225508909104113602181190371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150339272736075734787460247 225508909104113602181190371)
            ·
              refine ⟨338263363656170403271785557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225508909104113602181190371 338263363656170403271785557)
              ·
                refine ⟨3964023792845746913341237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 338263363656170403271785557 3964023792845746913341237)
                ·
                  refine ⟨371627230579288773125741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3964023792845746913341237 371627230579288773125741)
                  ·
                    rfl

theorem cell23_6513673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 5].length) (baseStart_6513673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513673 prefixEnd_6513673 := by exact prefixLift 6513673
  have htrace : WordTrace (prefixWord ++ tailWord_6513673) baseStart_6513673 baseEnd_6513673 := by
    simpa [prefixWord, tailWord_6513673, baseEnd_6513673] using wordTrace_append hprefix tailTrace_6513673
  have hstable : (prefixWord ++ tailWord_6513673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513673).length < 2 ^ (prefixWord ++ tailWord_6513673).sum := by decide
  have hdescent : baseEnd_6513673 < baseStart_6513673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513757 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6513757 : Nat := 118140960795 + 6513757 * 2 ^ 59
def prefixEnd_6513757 : Nat := 4983230072969 + 3 ^ 40 * 6513757 * 2
def baseEnd_6513757 : Nat := 3344688207588576629481283

theorem tailTrace_6513757 : CollatzResearch.WordTrace tailWord_6513757 prefixEnd_6513757 3344688207588576629481283 := by
  unfold tailWord_6513757
  simp only [CollatzResearch.WordTrace]
  refine ⟨237576235462778324973155525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158384156975185549982103683 237576235462778324973155525)
  ·
    refine ⟨44545544149270935932466661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237576235462778324973155525 44545544149270935932466661)
    ·
      refine ⟨8352289527988300487337499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44545544149270935932466661 8352289527988300487337499)
      ·
        refine ⟨12528434291982450731006249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352289527988300487337499 12528434291982450731006249)
        ·
          refine ⟨9396325718986838048254687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12528434291982450731006249 9396325718986838048254687)
          ·
            refine ⟨14094488578480257072382031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396325718986838048254687 14094488578480257072382031)
            ·
              refine ⟨21141732867720385608573047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14094488578480257072382031 21141732867720385608573047)
              ·
                refine ⟨31712599301580578412859571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21141732867720385608573047 31712599301580578412859571)
                ·
                  refine ⟨47568898952370867619289357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31712599301580578412859571 47568898952370867619289357)
                  ·
                    refine ⟨17838337107139075357233509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47568898952370867619289357 17838337107139075357233509)
                    ·
                      refine ⟨3344688207588576629481283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17838337107139075357233509 3344688207588576629481283)
                      ·
                        rfl

theorem cell23_6513757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6513757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513757 prefixEnd_6513757 := by exact prefixLift 6513757
  have htrace : WordTrace (prefixWord ++ tailWord_6513757) baseStart_6513757 baseEnd_6513757 := by
    simpa [prefixWord, tailWord_6513757, baseEnd_6513757] using wordTrace_append hprefix tailTrace_6513757
  have hstable : (prefixWord ++ tailWord_6513757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513757).length < 2 ^ (prefixWord ++ tailWord_6513757).sum := by decide
  have hdescent : baseEnd_6513757 < baseStart_6513757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513767 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 1, 4]
def baseStart_6513767 : Nat := 118140960795 + 6513767 * 2 ^ 59
def prefixEnd_6513767 : Nat := 4983230072969 + 3 ^ 40 * 6513767 * 2
def baseEnd_6513767 : Nat := 1114897780798373863452079

theorem tailTrace_6513767 : CollatzResearch.WordTrace tailWord_6513767 prefixEnd_6513767 1114897780798373863452079 := by
  unfold tailWord_6513767
  simp only [CollatzResearch.WordTrace]
  refine ⟨237576600192742096681019555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158384400128494731120679703 237576600192742096681019555)
  ·
    refine ⟨356364900289113145021529333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237576600192742096681019555 356364900289113145021529333)
    ·
      refine ⟨33409209402104357345768375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356364900289113145021529333 33409209402104357345768375)
      ·
        refine ⟨50113814103156536018652563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33409209402104357345768375 50113814103156536018652563)
        ·
          refine ⟨75170721154734804027978845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50113814103156536018652563 75170721154734804027978845)
          ·
            refine ⟨28189020433025551510492067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75170721154734804027978845 28189020433025551510492067)
            ·
              refine ⟨42283530649538327265738101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28189020433025551510492067 42283530649538327265738101)
              ·
                refine ⟨3964080998394218181162947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42283530649538327265738101 3964080998394218181162947)
                ·
                  refine ⟨5946121497591327271744421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964080998394218181162947 5946121497591327271744421)
                  ·
                    refine ⟨1114897780798373863452079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946121497591327271744421 1114897780798373863452079)
                    ·
                      rfl

theorem cell23_6513767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_6513767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513767 prefixEnd_6513767 := by exact prefixLift 6513767
  have htrace : WordTrace (prefixWord ++ tailWord_6513767) baseStart_6513767 baseEnd_6513767 := by
    simpa [prefixWord, tailWord_6513767, baseEnd_6513767] using wordTrace_append hprefix tailTrace_6513767
  have hstable : (prefixWord ++ tailWord_6513767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513767).length < 2 ^ (prefixWord ++ tailWord_6513767).sum := by decide
  have hdescent : baseEnd_6513767 < baseStart_6513767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513797 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 6]
def baseStart_6513797 : Nat := 118140960795 + 6513797 * 2 ^ 59
def prefixEnd_6513797 : Nat := 4983230072969 + 3 ^ 40 * 6513797 * 2
def baseEnd_6513797 : Nat := 371634305201639608109011

theorem tailTrace_6513797 : CollatzResearch.WordTrace tailWord_6513797 prefixEnd_6513797 371634305201639608109011 := by
  unfold tailWord_6513797
  simp only [CollatzResearch.WordTrace]
  refine ⟨237577694382633411804611645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158385129588422274536407763 237577694382633411804611645)
  ·
    refine ⟨89091635393487529426729367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237577694382633411804611645 89091635393487529426729367)
    ·
      refine ⟨133637453090231294140094051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89091635393487529426729367 133637453090231294140094051)
      ·
        refine ⟨200456179635346941210141077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133637453090231294140094051 200456179635346941210141077)
        ·
          refine ⟨9396383420406887869225363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200456179635346941210141077 9396383420406887869225363)
          ·
            refine ⟨14094575130610331803838045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396383420406887869225363 14094575130610331803838045)
            ·
              refine ⟨5285465673978874426439267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14094575130610331803838045 5285465673978874426439267)
              ·
                refine ⟨7928198510968311639658901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285465673978874426439267 7928198510968311639658901)
                ·
                  refine ⟨371634305201639608109011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7928198510968311639658901 371634305201639608109011)
                  ·
                    rfl

theorem cell23_6513797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_6513797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513797 prefixEnd_6513797 := by exact prefixLift 6513797
  have htrace : WordTrace (prefixWord ++ tailWord_6513797) baseStart_6513797 baseEnd_6513797 := by
    simpa [prefixWord, tailWord_6513797, baseEnd_6513797] using wordTrace_append hprefix tailTrace_6513797
  have hstable : (prefixWord ++ tailWord_6513797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513797).length < 2 ^ (prefixWord ++ tailWord_6513797).sum := by decide
  have hdescent : baseEnd_6513797 < baseStart_6513797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513834 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6513834 : Nat := 118140960795 + 6513834 * 2 ^ 59
def prefixEnd_6513834 : Nat := 4983230072969 + 3 ^ 40 * 6513834 * 2
def baseEnd_6513834 : Nat := 3344727745598972828218429

theorem tailTrace_6513834 : CollatzResearch.WordTrace tailWord_6513834 prefixEnd_6513834 3344727745598972828218429 := by
  unfold tailWord_6513834
  simp only [CollatzResearch.WordTrace]
  refine ⟨59394760970874841780927139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158386029255666244749139037 59394760970874841780927139)
  ·
    refine ⟨89092141456312262671390709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59394760970874841780927139 89092141456312262671390709)
    ·
      refine ⟨8352388261529274625442879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89092141456312262671390709 8352388261529274625442879)
      ·
        refine ⟨12528582392293911938164319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352388261529274625442879 12528582392293911938164319)
        ·
          refine ⟨18792873588440867907246479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528582392293911938164319 18792873588440867907246479)
          ·
            refine ⟨28189310382661301860869719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18792873588440867907246479 28189310382661301860869719)
            ·
              refine ⟨42283965573991952791304579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28189310382661301860869719 42283965573991952791304579)
              ·
                refine ⟨63425948360987929186956869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42283965573991952791304579 63425948360987929186956869)
                ·
                  refine ⟨11892365317685236722554413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63425948360987929186956869 11892365317685236722554413)
                  ·
                    refine ⟨4459636994131963770957905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11892365317685236722554413 4459636994131963770957905)
                    ·
                      refine ⟨3344727745598972828218429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459636994131963770957905 3344727745598972828218429)
                      ·
                        rfl

theorem cell23_6513834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6513834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513834 prefixEnd_6513834 := by exact prefixLift 6513834
  have htrace : WordTrace (prefixWord ++ tailWord_6513834) baseStart_6513834 baseEnd_6513834 := by
    simpa [prefixWord, tailWord_6513834, baseEnd_6513834] using wordTrace_append hprefix tailTrace_6513834
  have hstable : (prefixWord ++ tailWord_6513834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513834).length < 2 ^ (prefixWord ++ tailWord_6513834).sum := by decide
  have hdescent : baseEnd_6513834 < baseStart_6513834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513843 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6]
def baseStart_6513843 : Nat := 118140960795 + 6513843 * 2 ^ 59
def prefixEnd_6513843 : Nat := 4983230072969 + 3 ^ 40 * 6513843 * 2
def baseEnd_6513843 : Nat := 3344732366924863293005887

theorem tailTrace_6513843 : CollatzResearch.WordTrace tailWord_6513843 prefixEnd_6513843 3344732366924863293005887 := by
  unfold tailWord_6513843
  simp only [CollatzResearch.WordTrace]
  refine ⟨237579372140466761660786183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158386248093644507773857455 237579372140466761660786183)
  ·
    refine ⟨356369058210700142491179275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237579372140466761660786183 356369058210700142491179275)
    ·
      refine ⟨534553587316050213736768913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356369058210700142491179275 534553587316050213736768913)
      ·
        refine ⟨400915190487037660302576685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534553587316050213736768913 400915190487037660302576685)
        ·
          refine ⟨150343196432639122613466257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400915190487037660302576685 150343196432639122613466257)
          ·
            refine ⟨112757397324479341960099693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150343196432639122613466257 112757397324479341960099693)
            ·
              refine ⟨42284023996679753235037385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112757397324479341960099693 42284023996679753235037385)
              ·
                refine ⟨31713017997509814926278039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42284023996679753235037385 31713017997509814926278039)
                ·
                  refine ⟨47569526996264722389417059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31713017997509814926278039 47569526996264722389417059)
                  ·
                    refine ⟨71354290494397083584125589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47569526996264722389417059 71354290494397083584125589)
                    ·
                      refine ⟨3344732366924863293005887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71354290494397083584125589 3344732366924863293005887)
                      ·
                        rfl

theorem cell23_6513843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_6513843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513843 prefixEnd_6513843 := by exact prefixLift 6513843
  have htrace : WordTrace (prefixWord ++ tailWord_6513843) baseStart_6513843 baseEnd_6513843 := by
    simpa [prefixWord, tailWord_6513843, baseEnd_6513843] using wordTrace_append hprefix tailTrace_6513843
  have hstable : (prefixWord ++ tailWord_6513843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513843).length < 2 ^ (prefixWord ++ tailWord_6513843).sum := by decide
  have hdescent : baseEnd_6513843 < baseStart_6513843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
