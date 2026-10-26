import V185TrunkScan22Chunk010

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_97571 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 1, 3]
def baseStart_97571 : Nat := 118140960795 + 97571 * 2 ^ 59
def prefixEnd_97571 : Nat := 4983230072969 + 3 ^ 40 * 97571 * 2
def baseEnd_97571 : Nat := 33400547293295324475857

theorem tailTrace_97571 : CollatzResearch.WordTrace tailWord_97571 prefixEnd_97571 33400547293295324475857 := by
  unfold tailWord_97571
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558706729524405645236567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2372471153016270430157711 3558706729524405645236567)
  ·
    refine ⟨5338060094286608467854851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3558706729524405645236567 5338060094286608467854851)
    ·
      refine ⟨8007090141429912701782277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338060094286608467854851 8007090141429912701782277)
      ·
        refine ⟨1501329401518108631584177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8007090141429912701782277 1501329401518108631584177)
        ·
          refine ⟨1125997051138581473688133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1501329401518108631584177 1125997051138581473688133)
          ·
            refine ⟨211124447088484026316525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1125997051138581473688133 211124447088484026316525)
            ·
              refine ⟨79171667658181509868697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211124447088484026316525 79171667658181509868697)
              ·
                refine ⟨59378750743636132401523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79171667658181509868697 59378750743636132401523)
                ·
                  refine ⟨89068126115454198602285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59378750743636132401523 89068126115454198602285)
                  ·
                    refine ⟨33400547293295324475857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89068126115454198602285 33400547293295324475857)
                    ·
                      rfl

theorem cell22_97571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 3].length) (baseStart_97571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97571 prefixEnd_97571 := by exact prefixLift 97571
  have htrace : WordTrace (prefixWord ++ tailWord_97571) baseStart_97571 baseEnd_97571 := by
    simpa [prefixWord, tailWord_97571, baseEnd_97571] using wordTrace_append hprefix tailTrace_97571
  have hstable : (prefixWord ++ tailWord_97571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97571).length < 2 ^ (prefixWord ++ tailWord_97571).sum := by decide
  have hdescent : baseEnd_97571 < baseStart_97571 := by decide
  rcases family_descends (prefixWord ++ tailWord_97571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97580 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_97580 : Nat := 118140960795 + 97580 * 2 ^ 59
def prefixEnd_97580 : Nat := 4983230072969 + 3 ^ 40 * 97580 * 2
def baseEnd_97580 : Nat := 33403628177222301000829

theorem tailTrace_97580 : CollatzResearch.WordTrace tailWord_97580 prefixEnd_97580 33403628177222301000829 := by
  unfold tailWord_97580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779517493245900091157097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2372689990994533454876129 1779517493245900091157097)
  ·
    refine ⟨1334638119934425068367823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1779517493245900091157097 1334638119934425068367823)
    ·
      refine ⟨2001957179901637602551735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334638119934425068367823 2001957179901637602551735)
      ·
        refine ⟨3002935769852456403827603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001957179901637602551735 3002935769852456403827603)
        ·
          refine ⟨4504403654778684605741405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002935769852456403827603 4504403654778684605741405)
          ·
            refine ⟨1689151370542006727153027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4504403654778684605741405 1689151370542006727153027)
            ·
              refine ⟨2533727055813010090729541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689151370542006727153027 2533727055813010090729541)
              ·
                refine ⟨475073822964939392011789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2533727055813010090729541 475073822964939392011789)
                ·
                  refine ⟨178152683611852272004421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475073822964939392011789 178152683611852272004421)
                  ·
                    refine ⟨33403628177222301000829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178152683611852272004421 33403628177222301000829)
                    ·
                      rfl

theorem cell22_97580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_97580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97580 prefixEnd_97580 := by exact prefixLift 97580
  have htrace : WordTrace (prefixWord ++ tailWord_97580) baseStart_97580 baseEnd_97580 := by
    simpa [prefixWord, tailWord_97580, baseEnd_97580] using wordTrace_append hprefix tailTrace_97580
  have hstable : (prefixWord ++ tailWord_97580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97580).length < 2 ^ (prefixWord ++ tailWord_97580).sum := by decide
  have hdescent : baseEnd_97580 < baseStart_97580 := by decide
  rcases family_descends (prefixWord ++ tailWord_97580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97614 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_97614 : Nat := 118140960795 + 97614 * 2 ^ 59
def prefixEnd_97614 : Nat := 4983230072969 + 3 ^ 40 * 97614 * 2
def baseEnd_97614 : Nat := 33415267072057545650725

theorem tailTrace_97614 : CollatzResearch.WordTrace tailWord_97614 prefixEnd_97614 33415267072057545650725 := by
  unfold tailWord_97614
  simp only [CollatzResearch.WordTrace]
  refine ⟨445034383546077998631487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2373516712245749326034597 445034383546077998631487)
  ·
    refine ⟨667551575319116997947231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445034383546077998631487 667551575319116997947231)
    ·
      refine ⟨1001327362978675496920847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667551575319116997947231 1001327362978675496920847)
      ·
        refine ⟨1501991044468013245381271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001327362978675496920847 1501991044468013245381271)
        ·
          refine ⟨2252986566702019868071907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501991044468013245381271 2252986566702019868071907)
          ·
            refine ⟨3379479850053029802107861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252986566702019868071907 3379479850053029802107861)
            ·
              refine ⟨79206558985617885986903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 3379479850053029802107861 79206558985617885986903)
              ·
                refine ⟨118809838478426828980355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79206558985617885986903 118809838478426828980355)
                ·
                  refine ⟨178214757717640243470533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118809838478426828980355 178214757717640243470533)
                  ·
                    refine ⟨33415267072057545650725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178214757717640243470533 33415267072057545650725)
                    ·
                      rfl

theorem cell22_97614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_97614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97614 prefixEnd_97614 := by exact prefixLift 97614
  have htrace : WordTrace (prefixWord ++ tailWord_97614) baseStart_97614 baseEnd_97614 := by
    simpa [prefixWord, tailWord_97614, baseEnd_97614] using wordTrace_append hprefix tailTrace_97614
  have hstable : (prefixWord ++ tailWord_97614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97614).length < 2 ^ (prefixWord ++ tailWord_97614).sum := by decide
  have hdescent : baseEnd_97614 < baseStart_97614 := by decide
  rcases family_descends (prefixWord ++ tailWord_97614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97622 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_97622 : Nat := 118140960795 + 97622 * 2 ^ 59
def prefixEnd_97622 : Nat := 4983230072969 + 3 ^ 40 * 97622 * 2
def baseEnd_97622 : Nat := 33418005635548191450701

theorem tailTrace_97622 : CollatzResearch.WordTrace tailWord_97622 prefixEnd_97622 33418005635548191450701 := by
  unfold tailWord_97622
  simp only [CollatzResearch.WordTrace]
  refine ⟨222535428271227584708945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2373711234893094236895413 222535428271227584708945)
  ·
    refine ⟨166901571203420688531709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222535428271227584708945 166901571203420688531709)
    ·
      refine ⟨62588089201282758199391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166901571203420688531709 62588089201282758199391)
      ·
        refine ⟨93882133801924137299087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62588089201282758199391 93882133801924137299087)
        ·
          refine ⟨140823200702886205948631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93882133801924137299087 140823200702886205948631)
          ·
            refine ⟨211234801054329308922947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140823200702886205948631 211234801054329308922947)
            ·
              refine ⟨316852201581493963384421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211234801054329308922947 316852201581493963384421)
              ·
                refine ⟨59409787796530118134579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316852201581493963384421 59409787796530118134579)
                ·
                  refine ⟨89114681694795177201869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59409787796530118134579 89114681694795177201869)
                  ·
                    refine ⟨33418005635548191450701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89114681694795177201869 33418005635548191450701)
                    ·
                      rfl

theorem cell22_97622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_97622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97622 prefixEnd_97622 := by exact prefixLift 97622
  have htrace : WordTrace (prefixWord ++ tailWord_97622) baseStart_97622 baseEnd_97622 := by
    simpa [prefixWord, tailWord_97622, baseEnd_97622] using wordTrace_append hprefix tailTrace_97622
  have hstable : (prefixWord ++ tailWord_97622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97622).length < 2 ^ (prefixWord ++ tailWord_97622).sum := by decide
  have hdescent : baseEnd_97622 < baseStart_97622 := by decide
  rcases family_descends (prefixWord ++ tailWord_97622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97644 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_97644 : Nat := 118140960795 + 97644 * 2 ^ 59
def prefixEnd_97644 : Nat := 4983230072969 + 3 ^ 40 * 97644 * 2
def baseEnd_97644 : Nat := 33425536685147467400633

theorem tailTrace_97644 : CollatzResearch.WordTrace tailWord_97644 prefixEnd_97644 33425536685147467400633 := by
  unfold tailWord_97644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780684629129969556321993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2374246172173292741762657 1780684629129969556321993)
  ·
    refine ⟨1335513471847477167241495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1780684629129969556321993 1335513471847477167241495)
    ·
      refine ⟨2003270207771215750862243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335513471847477167241495 2003270207771215750862243)
      ·
        refine ⟨3004905311656823626293365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003270207771215750862243 3004905311656823626293365)
        ·
          refine ⟨281709872967827214965003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3004905311656823626293365 281709872967827214965003)
          ·
            refine ⟨422564809451740822447505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281709872967827214965003 422564809451740822447505)
            ·
              refine ⟨316923607088805616835629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422564809451740822447505 316923607088805616835629)
              ·
                refine ⟨118846352658302106313361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316923607088805616835629 118846352658302106313361)
                ·
                  refine ⟨89134764493726579735021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118846352658302106313361 89134764493726579735021)
                  ·
                    refine ⟨33425536685147467400633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89134764493726579735021 33425536685147467400633)
                    ·
                      rfl

theorem cell22_97644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_97644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97644 prefixEnd_97644 := by exact prefixLift 97644
  have htrace : WordTrace (prefixWord ++ tailWord_97644) baseStart_97644 baseEnd_97644 := by
    simpa [prefixWord, tailWord_97644, baseEnd_97644] using wordTrace_append hprefix tailTrace_97644
  have hstable : (prefixWord ++ tailWord_97644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97644).length < 2 ^ (prefixWord ++ tailWord_97644).sum := by decide
  have hdescent : baseEnd_97644 < baseStart_97644 := by decide
  rcases family_descends (prefixWord ++ tailWord_97644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97678 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_97678 : Nat := 118140960795 + 97678 * 2 ^ 59
def prefixEnd_97678 : Nat := 4983230072969 + 3 ^ 40 * 97678 * 2
def baseEnd_97678 : Nat := 33437175579982712050529

theorem tailTrace_97678 : CollatzResearch.WordTrace tailWord_97678 prefixEnd_97678 33437175579982712050529 := by
  unfold tailWord_97678
  simp only [CollatzResearch.WordTrace]
  refine ⟨445326167517095364922711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2375072893424508612921125 445326167517095364922711)
  ·
    refine ⟨667989251275643047384067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445326167517095364922711 667989251275643047384067)
    ·
      refine ⟨1001983876913464571076101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667989251275643047384067 1001983876913464571076101)
      ·
        refine ⟨187871976921274607076769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1001983876913464571076101 187871976921274607076769)
        ·
          refine ⟨140903982690955955307577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187871976921274607076769 140903982690955955307577)
          ·
            refine ⟨105677987018216966480683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140903982690955955307577 105677987018216966480683)
            ·
              refine ⟨158516980527325449721025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105677987018216966480683 158516980527325449721025)
              ·
                refine ⟨118887735395494087290769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158516980527325449721025 118887735395494087290769)
                ·
                  refine ⟨89165801546620565468077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118887735395494087290769 89165801546620565468077)
                  ·
                    refine ⟨33437175579982712050529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89165801546620565468077 33437175579982712050529)
                    ·
                      rfl

theorem cell22_97678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_97678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97678 prefixEnd_97678 := by exact prefixLift 97678
  have htrace : WordTrace (prefixWord ++ tailWord_97678) baseStart_97678 baseEnd_97678 := by
    simpa [prefixWord, tailWord_97678, baseEnd_97678] using wordTrace_append hprefix tailTrace_97678
  have hstable : (prefixWord ++ tailWord_97678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97678).length < 2 ^ (prefixWord ++ tailWord_97678).sum := by decide
  have hdescent : baseEnd_97678 < baseStart_97678 := by decide
  rcases family_descends (prefixWord ++ tailWord_97678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97689 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_97689 : Nat := 118140960795 + 97689 * 2 ^ 59
def prefixEnd_97689 : Nat := 4983230072969 + 3 ^ 40 * 97689 * 2
def baseEnd_97689 : Nat := 33440941104782350025495

theorem tailTrace_97689 : CollatzResearch.WordTrace tailWord_97689 prefixEnd_97689 33440941104782350025495 := by
  unfold tailWord_97689
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563010543096911798032121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2375340362064607865354747 3563010543096911798032121)
  ·
    refine ⟨2672257907322683848524091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3563010543096911798032121 2672257907322683848524091)
    ·
      refine ⟨4008386860984025772786137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2672257907322683848524091 4008386860984025772786137)
      ·
        refine ⟨3006290145738019329589603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4008386860984025772786137 3006290145738019329589603)
        ·
          refine ⟨4509435218607028994384405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006290145738019329589603 4509435218607028994384405)
          ·
            refine ⟨211379775872204484111769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4509435218607028994384405 211379775872204484111769)
            ·
              refine ⟨158534831904153363083827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211379775872204484111769 158534831904153363083827)
              ·
                refine ⟨237802247856230044625741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158534831904153363083827 237802247856230044625741)
                ·
                  refine ⟨89175842946086266734653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237802247856230044625741 89175842946086266734653)
                  ·
                    refine ⟨33440941104782350025495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89175842946086266734653 33440941104782350025495)
                    ·
                      rfl

theorem cell22_97689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_97689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97689 prefixEnd_97689 := by exact prefixLift 97689
  have htrace : WordTrace (prefixWord ++ tailWord_97689) baseStart_97689 baseEnd_97689 := by
    simpa [prefixWord, tailWord_97689, baseEnd_97689] using wordTrace_append hprefix tailTrace_97689
  have hstable : (prefixWord ++ tailWord_97689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97689).length < 2 ^ (prefixWord ++ tailWord_97689).sum := by decide
  have hdescent : baseEnd_97689 < baseStart_97689 := by decide
  rcases family_descends (prefixWord ++ tailWord_97689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97715 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_97715 : Nat := 118140960795 + 97715 * 2 ^ 59
def prefixEnd_97715 : Nat := 4983230072969 + 3 ^ 40 * 97715 * 2
def baseEnd_97715 : Nat := 33449841436126948875415

theorem tailTrace_97715 : CollatzResearch.WordTrace tailWord_97715 prefixEnd_97715 33449841436126948875415 := by
  unfold tailWord_97715
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563958841002718238478599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2375972560668478825652399 3563958841002718238478599)
  ·
    refine ⟨5345938261504077357717899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3563958841002718238478599 5345938261504077357717899)
    ·
      refine ⟨8018907392256116036576849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345938261504077357717899 8018907392256116036576849)
      ·
        refine ⟨6014180544192087027432637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8018907392256116036576849 6014180544192087027432637)
        ·
          refine ⟨2255317704072032635287239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6014180544192087027432637 2255317704072032635287239)
          ·
            refine ⟨3382976556108048952930859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255317704072032635287239 3382976556108048952930859)
            ·
              refine ⟨5074464834162073429396289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3382976556108048952930859 5074464834162073429396289)
              ·
                refine ⟨3805848625621555072047217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5074464834162073429396289 3805848625621555072047217)
                ·
                  refine ⟨2854386469216166304035413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3805848625621555072047217 2854386469216166304035413)
                  ·
                    refine ⟨33449841436126948875415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2854386469216166304035413 33449841436126948875415)
                    ·
                      rfl

theorem cell22_97715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_97715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97715 prefixEnd_97715 := by exact prefixLift 97715
  have htrace : WordTrace (prefixWord ++ tailWord_97715) baseStart_97715 baseEnd_97715 := by
    simpa [prefixWord, tailWord_97715, baseEnd_97715] using wordTrace_append hprefix tailTrace_97715
  have hstable : (prefixWord ++ tailWord_97715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97715).length < 2 ^ (prefixWord ++ tailWord_97715).sum := by decide
  have hdescent : baseEnd_97715 < baseStart_97715 := by decide
  rcases family_descends (prefixWord ++ tailWord_97715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97931 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 2, 3]
def baseStart_97931 : Nat := 118140960795 + 97931 * 2 ^ 59
def prefixEnd_97931 : Nat := 4983230072969 + 3 ^ 40 * 97931 * 2
def baseEnd_97931 : Nat := 33523782650374385474753

theorem tailTrace_97931 : CollatzResearch.WordTrace tailWord_97931 prefixEnd_97931 33523782650374385474753 := by
  unfold tailWord_97931
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571837008220187128341647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2381224672146791418894431 3571837008220187128341647)
  ·
    refine ⟨5357755512330280692512471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3571837008220187128341647 5357755512330280692512471)
    ·
      refine ⟨8036633268495421038768707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5357755512330280692512471 8036633268495421038768707)
      ·
        refine ⟨12054949902743131558153061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8036633268495421038768707 12054949902743131558153061)
        ·
          refine ⟨2260303106764337167153699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12054949902743131558153061 2260303106764337167153699)
          ·
            refine ⟨3390454660146505750730549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260303106764337167153699 3390454660146505750730549)
            ·
              refine ⟨317855124388734914130989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3390454660146505750730549 317855124388734914130989)
              ·
                refine ⟨119195671645775592799121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317855124388734914130989 119195671645775592799121)
                ·
                  refine ⟨89396753734331694599341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119195671645775592799121 89396753734331694599341)
                  ·
                    refine ⟨33523782650374385474753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89396753734331694599341 33523782650374385474753)
                    ·
                      rfl

theorem cell22_97931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 3].length) (baseStart_97931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97931 prefixEnd_97931 := by exact prefixLift 97931
  have htrace : WordTrace (prefixWord ++ tailWord_97931) baseStart_97931 baseEnd_97931 := by
    simpa [prefixWord, tailWord_97931, baseEnd_97931] using wordTrace_append hprefix tailTrace_97931
  have hstable : (prefixWord ++ tailWord_97931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97931).length < 2 ^ (prefixWord ++ tailWord_97931).sum := by decide
  have hdescent : baseEnd_97931 < baseStart_97931 := by decide
  rcases family_descends (prefixWord ++ tailWord_97931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_97944 : List Nat := [2, 1, 2, 4, 1, 2, 2, 8]
def baseStart_97944 : Nat := 118140960795 + 97944 * 2 ^ 59
def prefixEnd_97944 : Nat := 4983230072969 + 3 ^ 40 * 97944 * 2
def baseEnd_97944 : Nat := 3725359201782964988857

theorem tailTrace_97944 : CollatzResearch.WordTrace tailWord_97944 prefixEnd_97944 3725359201782964988857 := by
  unfold tailWord_97944
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786155578586545174282443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2381540771448726899043257 1786155578586545174282443)
  ·
    refine ⟨2679233367879817761423665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786155578586545174282443 2679233367879817761423665)
    ·
      refine ⟨2009425025909863321067749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2679233367879817761423665 2009425025909863321067749)
      ·
        refine ⟨376767192358099372700203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2009425025909863321067749 376767192358099372700203)
        ·
          refine ⟨565150788537149059050305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376767192358099372700203 565150788537149059050305)
          ·
            refine ⟨423863091402861794287729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565150788537149059050305 423863091402861794287729)
            ·
              refine ⟨317897318552146345715797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423863091402861794287729 317897318552146345715797)
              ·
                refine ⟨3725359201782964988857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 317897318552146345715797 3725359201782964988857)
                ·
                  rfl

theorem cell22_97944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_97944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_97944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_97944 prefixEnd_97944 := by exact prefixLift 97944
  have htrace : WordTrace (prefixWord ++ tailWord_97944) baseStart_97944 baseEnd_97944 := by
    simpa [prefixWord, tailWord_97944, baseEnd_97944] using wordTrace_append hprefix tailTrace_97944
  have hstable : (prefixWord ++ tailWord_97944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_97944).length < 2 ^ (prefixWord ++ tailWord_97944).sum := by decide
  have hdescent : baseEnd_97944 < baseStart_97944 := by decide
  rcases family_descends (prefixWord ++ tailWord_97944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98010 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_98010 : Nat := 118140960795 + 98010 * 2 ^ 59
def prefixEnd_98010 : Nat := 4983230072969 + 3 ^ 40 * 98010 * 2
def baseEnd_98010 : Nat := 33550825964844512749511

theorem tailTrace_98010 : CollatzResearch.WordTrace tailWord_98010 prefixEnd_98010 33550825964844512749511 := by
  unfold tailWord_98010
  simp only [CollatzResearch.WordTrace]
  refine ⟨893679593733495905116871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2383145583289322413644989 893679593733495905116871)
  ·
    refine ⟨1340519390600243857675307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 893679593733495905116871 1340519390600243857675307)
    ·
      refine ⟨2010779085900365786512961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340519390600243857675307 2010779085900365786512961)
      ·
        refine ⟨1508084314425274339884721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2010779085900365786512961 1508084314425274339884721)
        ·
          refine ⟨1131063235818955754913541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1508084314425274339884721 1131063235818955754913541)
          ·
            refine ⟨212074356716054204046289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1131063235818955754913541 212074356716054204046289)
            ·
              refine ⟨159055767537040653034717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212074356716054204046289 159055767537040653034717)
              ·
                refine ⟨59645912826390244888019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159055767537040653034717 59645912826390244888019)
                ·
                  refine ⟨89468869239585367332029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59645912826390244888019 89468869239585367332029)
                  ·
                    refine ⟨33550825964844512749511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89468869239585367332029 33550825964844512749511)
                    ·
                      rfl

theorem cell22_98010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_98010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98010 prefixEnd_98010 := by exact prefixLift 98010
  have htrace : WordTrace (prefixWord ++ tailWord_98010) baseStart_98010 baseEnd_98010 := by
    simpa [prefixWord, tailWord_98010, baseEnd_98010] using wordTrace_append hprefix tailTrace_98010
  have hstable : (prefixWord ++ tailWord_98010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98010).length < 2 ^ (prefixWord ++ tailWord_98010).sum := by decide
  have hdescent : baseEnd_98010 < baseStart_98010 := by decide
  rcases family_descends (prefixWord ++ tailWord_98010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98023 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 7]
def baseStart_98023 : Nat := 118140960795 + 98023 * 2 ^ 59
def prefixEnd_98023 : Nat := 4983230072969 + 3 ^ 40 * 98023 * 2
def baseEnd_98023 : Nat := 11185092043505604058157

theorem tailTrace_98023 : CollatzResearch.WordTrace tailWord_98023 prefixEnd_98023 11185092043505604058157 := by
  unfold tailWord_98023
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575192523886886840690723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2383461682591257893793815 3575192523886886840690723)
  ·
    refine ⟨5362788785830330261036085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575192523886886840690723 5362788785830330261036085)
    ·
      refine ⟨502761448671593461972133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5362788785830330261036085 502761448671593461972133)
      ·
        refine ⟨94267771625923774119775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 502761448671593461972133 94267771625923774119775)
        ·
          refine ⟨141401657438885661179663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94267771625923774119775 141401657438885661179663)
          ·
            refine ⟨212102486158328491769495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141401657438885661179663 212102486158328491769495)
            ·
              refine ⟨318153729237492737654243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212102486158328491769495 318153729237492737654243)
              ·
                refine ⟨477230593856239106481365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318153729237492737654243 477230593856239106481365)
                ·
                  refine ⟨11185092043505604058157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 477230593856239106481365 11185092043505604058157)
                  ·
                    rfl

theorem cell22_98023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 7].length) (baseStart_98023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98023 prefixEnd_98023 := by exact prefixLift 98023
  have htrace : WordTrace (prefixWord ++ tailWord_98023) baseStart_98023 baseEnd_98023 := by
    simpa [prefixWord, tailWord_98023, baseEnd_98023] using wordTrace_append hprefix tailTrace_98023
  have hstable : (prefixWord ++ tailWord_98023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98023).length < 2 ^ (prefixWord ++ tailWord_98023).sum := by decide
  have hdescent : baseEnd_98023 < baseStart_98023 := by decide
  rcases family_descends (prefixWord ++ tailWord_98023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98081 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_98081 : Nat := 118140960795 + 98081 * 2 ^ 59
def prefixEnd_98081 : Nat := 4983230072969 + 3 ^ 40 * 98081 * 2
def baseEnd_98081 : Nat := 33575130715823994224293

theorem tailTrace_98081 : CollatzResearch.WordTrace tailWord_98081 prefixEnd_98081 33575130715823994224293 := by
  unfold tailWord_98081
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577307957676762746302097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2384871971784508497534731 3577307957676762746302097)
  ·
    refine ⟨2682980968257572059726573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3577307957676762746302097 2682980968257572059726573)
    ·
      refine ⟨1006117863096589522397465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2682980968257572059726573 1006117863096589522397465)
      ·
        refine ⟨754588397322442141798099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1006117863096589522397465 754588397322442141798099)
        ·
          refine ⟨1131882595983663212697149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754588397322442141798099 1131882595983663212697149)
          ·
            refine ⟨424455973493873704761431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1131882595983663212697149 424455973493873704761431)
            ·
              refine ⟨636683960240810557142147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424455973493873704761431 636683960240810557142147)
              ·
                refine ⟨955025940361215835713221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636683960240810557142147 955025940361215835713221)
                ·
                  refine ⟨179067363817727969196229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955025940361215835713221 179067363817727969196229)
                  ·
                    refine ⟨33575130715823994224293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179067363817727969196229 33575130715823994224293)
                    ·
                      rfl

theorem cell22_98081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_98081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98081 prefixEnd_98081 := by exact prefixLift 98081
  have htrace : WordTrace (prefixWord ++ tailWord_98081) baseStart_98081 baseEnd_98081 := by
    simpa [prefixWord, tailWord_98081, baseEnd_98081] using wordTrace_append hprefix tailTrace_98081
  have hstable : (prefixWord ++ tailWord_98081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98081).length < 2 ^ (prefixWord ++ tailWord_98081).sum := by decide
  have hdescent : baseEnd_98081 < baseStart_98081 := by decide
  rcases family_descends (prefixWord ++ tailWord_98081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98085 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 4]
def baseStart_98085 : Nat := 118140960795 + 98085 * 2 ^ 59
def prefixEnd_98085 : Nat := 4983230072969 + 3 ^ 40 * 98085 * 2
def baseEnd_98085 : Nat := 11192166665856439041427

theorem tailTrace_98085 : CollatzResearch.WordTrace tailWord_98085 prefixEnd_98085 11192166665856439041427 := by
  unfold tailWord_98085
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577453849662271429447709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2384969233108180952965139 3577453849662271429447709)
  ·
    refine ⟨1341545193623351786042891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3577453849662271429447709 1341545193623351786042891)
    ·
      refine ⟨2012317790435027679064337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341545193623351786042891 2012317790435027679064337)
      ·
        refine ⟨1509238342826270759298253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2012317790435027679064337 1509238342826270759298253)
        ·
          refine ⟨565964378559851534736845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1509238342826270759298253 565964378559851534736845)
          ·
            refine ⟨212236641959944325526317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 565964378559851534736845 212236641959944325526317)
            ·
              refine ⟨79588740734979122072369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212236641959944325526317 79588740734979122072369)
              ·
                refine ⟨59691555551234341554277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79588740734979122072369 59691555551234341554277)
                ·
                  refine ⟨11192166665856439041427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59691555551234341554277 11192166665856439041427)
                  ·
                    rfl

theorem cell22_98085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_98085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98085 prefixEnd_98085 := by exact prefixLift 98085
  have htrace : WordTrace (prefixWord ++ tailWord_98085) baseStart_98085 baseEnd_98085 := by
    simpa [prefixWord, tailWord_98085, baseEnd_98085] using wordTrace_append hprefix tailTrace_98085
  have hstable : (prefixWord ++ tailWord_98085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98085).length < 2 ^ (prefixWord ++ tailWord_98085).sum := by decide
  have hdescent : baseEnd_98085 < baseStart_98085 := by decide
  rcases family_descends (prefixWord ++ tailWord_98085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98145 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 1, 3]
def baseStart_98145 : Nat := 118140960795 + 98145 * 2 ^ 59
def prefixEnd_98145 : Nat := 4983230072969 + 3 ^ 40 * 98145 * 2
def baseEnd_98145 : Nat := 33597039223749160624097

theorem tailTrace_98145 : CollatzResearch.WordTrace tailWord_98145 prefixEnd_98145 33597039223749160624097 := by
  unfold tailWord_98145
  simp only [CollatzResearch.WordTrace]
  refine ⟨3579642229444901676631889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2386428152963267784421259 3579642229444901676631889)
  ·
    refine ⟨2684731672083676257473917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3579642229444901676631889 2684731672083676257473917)
    ·
      refine ⟨1006774377031378596552719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2684731672083676257473917 1006774377031378596552719)
      ·
        refine ⟨1510161565547067894829079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006774377031378596552719 1510161565547067894829079)
        ·
          refine ⟨2265242348320601842243619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510161565547067894829079 2265242348320601842243619)
          ·
            refine ⟨3397863522480902763365429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265242348320601842243619 3397863522480902763365429)
            ·
              refine ⟨318549705232584634065509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3397863522480902763365429 318549705232584634065509)
              ·
                refine ⟨59728069731109618887283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318549705232584634065509 59728069731109618887283)
                ·
                  refine ⟨89592104596664428330925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59728069731109618887283 89592104596664428330925)
                  ·
                    refine ⟨33597039223749160624097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89592104596664428330925 33597039223749160624097)
                    ·
                      rfl

theorem cell22_98145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_98145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98145 prefixEnd_98145 := by exact prefixLift 98145
  have htrace : WordTrace (prefixWord ++ tailWord_98145) baseStart_98145 baseEnd_98145 := by
    simpa [prefixWord, tailWord_98145, baseEnd_98145] using wordTrace_append hprefix tailTrace_98145
  have hstable : (prefixWord ++ tailWord_98145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98145).length < 2 ^ (prefixWord ++ tailWord_98145).sum := by decide
  have hdescent : baseEnd_98145 < baseStart_98145 := by decide
  rcases family_descends (prefixWord ++ tailWord_98145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98156 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_98156 : Nat := 118140960795 + 98156 * 2 ^ 59
def prefixEnd_98156 : Nat := 4983230072969 + 3 ^ 40 * 98156 * 2
def baseEnd_98156 : Nat := 33600804748548798599063

theorem tailTrace_98156 : CollatzResearch.WordTrace tailWord_98156 prefixEnd_98156 33600804748548798599063 := by
  unfold tailWord_98156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790021716202525277641161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2386695621603367036854881 1790021716202525277641161)
  ·
    refine ⟨1342516287151893958230871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1790021716202525277641161 1342516287151893958230871)
    ·
      refine ⟨2013774430727840937346307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342516287151893958230871 2013774430727840937346307)
      ·
        refine ⟨3020661646091761406019461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013774430727840937346307 3020661646091761406019461)
        ·
          refine ⟨566374058642205263628649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3020661646091761406019461 566374058642205263628649)
          ·
            refine ⟨424780543981653947721487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566374058642205263628649 424780543981653947721487)
            ·
              refine ⟨637170815972480921582231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424780543981653947721487 637170815972480921582231)
              ·
                refine ⟨955756223958721382373347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637170815972480921582231 955756223958721382373347)
                ·
                  refine ⟨1433634335938082073560021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955756223958721382373347 1433634335938082073560021)
                  ·
                    refine ⟨33600804748548798599063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1433634335938082073560021 33600804748548798599063)
                    ·
                      rfl

theorem cell22_98156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_98156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98156 prefixEnd_98156 := by exact prefixLift 98156
  have htrace : WordTrace (prefixWord ++ tailWord_98156) baseStart_98156 baseEnd_98156 := by
    simpa [prefixWord, tailWord_98156, baseEnd_98156] using wordTrace_append hprefix tailTrace_98156
  have hstable : (prefixWord ++ tailWord_98156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98156).length < 2 ^ (prefixWord ++ tailWord_98156).sum := by decide
  have hdescent : baseEnd_98156 < baseStart_98156 := by decide
  rcases family_descends (prefixWord ++ tailWord_98156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98201 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_98201 : Nat := 118140960795 + 98201 * 2 ^ 59
def prefixEnd_98201 : Nat := 4983230072969 + 3 ^ 40 * 98201 * 2
def baseEnd_98201 : Nat := 33616209168183681223925

theorem tailTrace_98201 : CollatzResearch.WordTrace tailWord_98201 prefixEnd_98201 33616209168183681223925 := by
  unfold tailWord_98201
  simp only [CollatzResearch.WordTrace]
  refine ⟨3581684717242023240670457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2387789811494682160446971 3581684717242023240670457)
  ·
    refine ⟨2686263537931517430502843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3581684717242023240670457 2686263537931517430502843)
    ·
      refine ⟨4029395306897276145754265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686263537931517430502843 4029395306897276145754265)
      ·
        refine ⟨3022046480172957109315699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029395306897276145754265 3022046480172957109315699)
        ·
          refine ⟨4533069720259435663973549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022046480172957109315699 4533069720259435663973549)
          ·
            refine ⟨1699901145097288373990081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4533069720259435663973549 1699901145097288373990081)
            ·
              refine ⟨1274925858822966280492561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1699901145097288373990081 1274925858822966280492561)
              ·
                refine ⟨956194394117224710369421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274925858822966280492561 956194394117224710369421)
                ·
                  refine ⟨358572897793959266388533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956194394117224710369421 358572897793959266388533)
                  ·
                    refine ⟨33616209168183681223925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 358572897793959266388533 33616209168183681223925)
                    ·
                      rfl

theorem cell22_98201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_98201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98201 prefixEnd_98201 := by exact prefixLift 98201
  have htrace : WordTrace (prefixWord ++ tailWord_98201) baseStart_98201 baseEnd_98201 := by
    simpa [prefixWord, tailWord_98201, baseEnd_98201] using wordTrace_append hprefix tailTrace_98201
  have hstable : (prefixWord ++ tailWord_98201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98201).length < 2 ^ (prefixWord ++ tailWord_98201).sum := by decide
  have hdescent : baseEnd_98201 < baseStart_98201 := by decide
  rcases family_descends (prefixWord ++ tailWord_98201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98233 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_98233 : Nat := 118140960795 + 98233 * 2 ^ 59
def prefixEnd_98233 : Nat := 4983230072969 + 3 ^ 40 * 98233 * 2
def baseEnd_98233 : Nat := 33627163422146264423827

theorem tailTrace_98233 : CollatzResearch.WordTrace tailWord_98233 prefixEnd_98233 33627163422146264423827 := by
  unfold tailWord_98233
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582851853126092705835353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2388567902084061803890235 3582851853126092705835353)
  ·
    refine ⟨2687138889844569529376515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3582851853126092705835353 2687138889844569529376515)
    ·
      refine ⟨4030708334766854294064773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2687138889844569529376515 4030708334766854294064773)
      ·
        refine ⟨755757812768785180137145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4030708334766854294064773 755757812768785180137145)
        ·
          refine ⟨566818359576588885102859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755757812768785180137145 566818359576588885102859)
          ·
            refine ⟨850227539364883327654289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566818359576588885102859 850227539364883327654289)
            ·
              refine ⟨637670654523662495740717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850227539364883327654289 637670654523662495740717)
              ·
                refine ⟨239126495446373435902769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637670654523662495740717 239126495446373435902769)
                ·
                  refine ⟨179344871584780076927077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239126495446373435902769 179344871584780076927077)
                  ·
                    refine ⟨33627163422146264423827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179344871584780076927077 33627163422146264423827)
                    ·
                      rfl

theorem cell22_98233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_98233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98233 prefixEnd_98233 := by exact prefixLift 98233
  have htrace : WordTrace (prefixWord ++ tailWord_98233) baseStart_98233 baseEnd_98233 := by
    simpa [prefixWord, tailWord_98233, baseEnd_98233] using wordTrace_append hprefix tailTrace_98233
  have hstable : (prefixWord ++ tailWord_98233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98233).length < 2 ^ (prefixWord ++ tailWord_98233).sum := by decide
  have hdescent : baseEnd_98233 < baseStart_98233 := by decide
  rcases family_descends (prefixWord ++ tailWord_98233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98237 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 4]
def baseStart_98237 : Nat := 118140960795 + 98237 * 2 ^ 59
def prefixEnd_98237 : Nat := 4983230072969 + 3 ^ 40 * 98237 * 2
def baseEnd_98237 : Nat := 11209510901297195774605

theorem tailTrace_98237 : CollatzResearch.WordTrace tailWord_98237 prefixEnd_98237 11209510901297195774605 := by
  unfold tailWord_98237
  simp only [CollatzResearch.WordTrace]
  refine ⟨3582997745111601388980965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2388665163407734259320643 3582997745111601388980965)
  ·
    refine ⟨671812077208425260433931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3582997745111601388980965 671812077208425260433931)
    ·
      refine ⟨1007718115812637890650897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671812077208425260433931 1007718115812637890650897)
      ·
        refine ⟨755788586859478417988173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1007718115812637890650897 755788586859478417988173)
        ·
          refine ⟨283420720072304406745565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 755788586859478417988173 283420720072304406745565)
          ·
            refine ⟨106282770027114152529587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283420720072304406745565 106282770027114152529587)
            ·
              refine ⟨159424155040671228794381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106282770027114152529587 159424155040671228794381)
              ·
                refine ⟨59784058140251710797893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159424155040671228794381 59784058140251710797893)
                ·
                  refine ⟨11209510901297195774605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59784058140251710797893 11209510901297195774605)
                  ·
                    rfl

theorem cell22_98237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_98237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98237 prefixEnd_98237 := by exact prefixLift 98237
  have htrace : WordTrace (prefixWord ++ tailWord_98237) baseStart_98237 baseEnd_98237 := by
    simpa [prefixWord, tailWord_98237, baseEnd_98237] using wordTrace_append hprefix tailTrace_98237
  have hstable : (prefixWord ++ tailWord_98237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98237).length < 2 ^ (prefixWord ++ tailWord_98237).sum := by decide
  have hdescent : baseEnd_98237 < baseStart_98237 := by decide
  rcases family_descends (prefixWord ++ tailWord_98237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98248 : List Nat := [2, 1, 3, 1, 4, 3, 8]
def baseStart_98248 : Nat := 118140960795 + 98248 * 2 ^ 59
def prefixEnd_98248 : Nat := 4983230072969 + 3 ^ 40 * 98248 * 2
def baseEnd_98248 : Nat := 1245640675136712048103

theorem tailTrace_98248 : CollatzResearch.WordTrace tailWord_98248 prefixEnd_98248 1245640675136712048103 := by
  unfold tailWord_98248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791699474035875133815699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2388932632047833511754265 1791699474035875133815699)
  ·
    refine ⟨2687549211053812700723549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791699474035875133815699 2687549211053812700723549)
    ·
      refine ⟨1007830954145179762771331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2687549211053812700723549 1007830954145179762771331)
      ·
        refine ⟨1511746431217769644156997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007830954145179762771331 1511746431217769644156997)
        ·
          refine ⟨283452455853331808279437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1511746431217769644156997 283452455853331808279437)
          ·
            refine ⟨106294670944999428104789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283452455853331808279437 106294670944999428104789)
            ·
              refine ⟨1245640675136712048103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 106294670944999428104789 1245640675136712048103)
              ·
                rfl

theorem cell22_98248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 8].length) (baseStart_98248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98248 prefixEnd_98248 := by exact prefixLift 98248
  have htrace : WordTrace (prefixWord ++ tailWord_98248) baseStart_98248 baseEnd_98248 := by
    simpa [prefixWord, tailWord_98248, baseEnd_98248] using wordTrace_append hprefix tailTrace_98248
  have hstable : (prefixWord ++ tailWord_98248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98248).length < 2 ^ (prefixWord ++ tailWord_98248).sum := by decide
  have hdescent : baseEnd_98248 < baseStart_98248 := by decide
  rcases family_descends (prefixWord ++ tailWord_98248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98314 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_98314 : Nat := 118140960795 + 98314 * 2 ^ 59
def prefixEnd_98314 : Nat := 4983230072969 + 3 ^ 40 * 98314 * 2
def baseEnd_98314 : Nat := 33654891377489053148579

theorem tailTrace_98314 : CollatzResearch.WordTrace tailWord_98314 prefixEnd_98314 33654891377489053148579 := by
  unfold tailWord_98314
  simp only [CollatzResearch.WordTrace]
  refine ⟨896451541458160884883499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2390537443888429026355997 896451541458160884883499)
  ·
    refine ⟨1344677312187241327325249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 896451541458160884883499 1344677312187241327325249)
    ·
      refine ⟨1008507984140430995493937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1344677312187241327325249 1008507984140430995493937)
      ·
        refine ⟨756380988105323246620453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1008507984140430995493937 756380988105323246620453)
        ·
          refine ⟨141821435269748108741335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 756380988105323246620453 141821435269748108741335)
          ·
            refine ⟨212732152904622163112003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141821435269748108741335 212732152904622163112003)
            ·
              refine ⟨319098229356933244668005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212732152904622163112003 319098229356933244668005)
              ·
                refine ⟨59830918004424983375251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319098229356933244668005 59830918004424983375251)
                ·
                  refine ⟨89746377006637475062877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59830918004424983375251 89746377006637475062877)
                  ·
                    refine ⟨33654891377489053148579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89746377006637475062877 33654891377489053148579)
                    ·
                      rfl

theorem cell22_98314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_98314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98314 prefixEnd_98314 := by exact prefixLift 98314
  have htrace : WordTrace (prefixWord ++ tailWord_98314) baseStart_98314 baseEnd_98314 := by
    simpa [prefixWord, tailWord_98314, baseEnd_98314] using wordTrace_append hprefix tailTrace_98314
  have hstable : (prefixWord ++ tailWord_98314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98314).length < 2 ^ (prefixWord ++ tailWord_98314).sum := by decide
  have hdescent : baseEnd_98314 < baseStart_98314 := by decide
  rcases family_descends (prefixWord ++ tailWord_98314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98323 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 3, 4]
def baseStart_98323 : Nat := 118140960795 + 98323 * 2 ^ 59
def prefixEnd_98323 : Nat := 4983230072969 + 3 ^ 40 * 98323 * 2
def baseEnd_98323 : Nat := 33657972261416029673551

theorem tailTrace_98323 : CollatzResearch.WordTrace tailWord_98323 prefixEnd_98323 33657972261416029673551 := by
  unfold tailWord_98323
  simp only [CollatzResearch.WordTrace]
  refine ⟨3586134422800038076611623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2390756281866692051074415 3586134422800038076611623)
  ·
    refine ⟨5379201634200057114917435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3586134422800038076611623 5379201634200057114917435)
    ·
      refine ⟨8068802451300085672376153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379201634200057114917435 8068802451300085672376153)
      ·
        refine ⟨6051601838475064254282115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8068802451300085672376153 6051601838475064254282115)
        ·
          refine ⟨9077402757712596381423173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6051601838475064254282115 9077402757712596381423173)
          ·
            refine ⟨1702013017071111821516845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9077402757712596381423173 1702013017071111821516845)
            ·
              refine ⟨638254881401666933068817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1702013017071111821516845 638254881401666933068817)
              ·
                refine ⟨478691161051250199801613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638254881401666933068817 478691161051250199801613)
                ·
                  refine ⟨179509185394218824925605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478691161051250199801613 179509185394218824925605)
                  ·
                    refine ⟨33657972261416029673551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179509185394218824925605 33657972261416029673551)
                    ·
                      rfl

theorem cell22_98323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_98323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98323 prefixEnd_98323 := by exact prefixLift 98323
  have htrace : WordTrace (prefixWord ++ tailWord_98323) baseStart_98323 baseEnd_98323 := by
    simpa [prefixWord, tailWord_98323, baseEnd_98323] using wordTrace_append hprefix tailTrace_98323
  have hstable : (prefixWord ++ tailWord_98323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98323).length < 2 ^ (prefixWord ++ tailWord_98323).sum := by decide
  have hdescent : baseEnd_98323 < baseStart_98323 := by decide
  rcases family_descends (prefixWord ++ tailWord_98323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98325 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_98325 : Nat := 118140960795 + 98325 * 2 ^ 59
def prefixEnd_98325 : Nat := 4983230072969 + 3 ^ 40 * 98325 * 2
def baseEnd_98325 : Nat := 33658656902288691123545

theorem tailTrace_98325 : CollatzResearch.WordTrace tailWord_98325 prefixEnd_98325 33658656902288691123545 := by
  unfold tailWord_98325
  simp only [CollatzResearch.WordTrace]
  refine ⟨3586207368792792418184429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2390804912528528278789619 3586207368792792418184429)
  ·
    refine ⟨1344827763297297156819161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3586207368792792418184429 1344827763297297156819161)
    ·
      refine ⟨1008620822472972867614371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1344827763297297156819161 1008620822472972867614371)
      ·
        refine ⟨1512931233709459301421557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008620822472972867614371 1512931233709459301421557)
        ·
          refine ⟨141837303160261809508271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1512931233709459301421557 141837303160261809508271)
          ·
            refine ⟨212755954740392714262407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141837303160261809508271 212755954740392714262407)
            ·
              refine ⟨319133932110589071393611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212755954740392714262407 319133932110589071393611)
              ·
                refine ⟨478700898165883607090417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319133932110589071393611 478700898165883607090417)
                ·
                  refine ⟨359025673624412705317813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478700898165883607090417 359025673624412705317813)
                  ·
                    refine ⟨33658656902288691123545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 359025673624412705317813 33658656902288691123545)
                    ·
                      rfl

theorem cell22_98325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_98325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98325 prefixEnd_98325 := by exact prefixLift 98325
  have htrace : WordTrace (prefixWord ++ tailWord_98325) baseStart_98325 baseEnd_98325 := by
    simpa [prefixWord, tailWord_98325, baseEnd_98325] using wordTrace_append hprefix tailTrace_98325
  have hstable : (prefixWord ++ tailWord_98325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98325).length < 2 ^ (prefixWord ++ tailWord_98325).sum := by decide
  have hdescent : baseEnd_98325 < baseStart_98325 := by decide
  rcases family_descends (prefixWord ++ tailWord_98325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98355 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 4]
def baseStart_98355 : Nat := 118140960795 + 98355 * 2 ^ 59
def prefixEnd_98355 : Nat := 4983230072969 + 3 ^ 40 * 98355 * 2
def baseEnd_98355 : Nat := 11222975505126204291151

theorem tailTrace_98355 : CollatzResearch.WordTrace tailWord_98355 prefixEnd_98355 11222975505126204291151 := by
  unfold tailWord_98355
  simp only [CollatzResearch.WordTrace]
  refine ⟨3587301558684107541776519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2391534372456071694517679 3587301558684107541776519)
  ·
    refine ⟨5380952338026161312664779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3587301558684107541776519 5380952338026161312664779)
    ·
      refine ⟨8071428507039241968997169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5380952338026161312664779 8071428507039241968997169)
      ·
        refine ⟨6053571380279431476747877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8071428507039241968997169 6053571380279431476747877)
        ·
          refine ⟨1135044633802393401890227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6053571380279431476747877 1135044633802393401890227)
          ·
            refine ⟨1702566950703590102835341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135044633802393401890227 1702566950703590102835341)
            ·
              refine ⟨638462606513846288563253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1702566950703590102835341 638462606513846288563253)
              ·
                refine ⟨59855869360673089552805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638462606513846288563253 59855869360673089552805)
                ·
                  refine ⟨11222975505126204291151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59855869360673089552805 11222975505126204291151)
                  ·
                    rfl

theorem cell22_98355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 4].length) (baseStart_98355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98355 prefixEnd_98355 := by exact prefixLift 98355
  have htrace : WordTrace (prefixWord ++ tailWord_98355) baseStart_98355 baseEnd_98355 := by
    simpa [prefixWord, tailWord_98355, baseEnd_98355] using wordTrace_append hprefix tailTrace_98355
  have hstable : (prefixWord ++ tailWord_98355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98355).length < 2 ^ (prefixWord ++ tailWord_98355).sum := by decide
  have hdescent : baseEnd_98355 < baseStart_98355 := by decide
  rcases family_descends (prefixWord ++ tailWord_98355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98357 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_98357 : Nat := 118140960795 + 98357 * 2 ^ 59
def prefixEnd_98357 : Nat := 4983230072969 + 3 ^ 40 * 98357 * 2
def baseEnd_98357 : Nat := 33669611156251274323447

theorem tailTrace_98357 : CollatzResearch.WordTrace tailWord_98357 prefixEnd_98357 33669611156251274323447 := by
  unfold tailWord_98357
  simp only [CollatzResearch.WordTrace]
  refine ⟨3587374504676861883349325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2391583003117907922232883 3587374504676861883349325)
  ·
    refine ⟨1345265439253823206255997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3587374504676861883349325 1345265439253823206255997)
    ·
      refine ⟨504474539720183702345999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1345265439253823206255997 504474539720183702345999)
      ·
        refine ⟨756711809580275553518999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504474539720183702345999 756711809580275553518999)
        ·
          refine ⟨1135067714370413330278499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756711809580275553518999 1135067714370413330278499)
          ·
            refine ⟨1702601571555619995417749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135067714370413330278499 1702601571555619995417749)
            ·
              refine ⟨79809448666669687285207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1702601571555619995417749 79809448666669687285207)
              ·
                refine ⟨119714173000004530927811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79809448666669687285207 119714173000004530927811)
                ·
                  refine ⟨179571259500006796391717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119714173000004530927811 179571259500006796391717)
                  ·
                    refine ⟨33669611156251274323447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179571259500006796391717 33669611156251274323447)
                    ·
                      rfl

theorem cell22_98357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_98357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98357 prefixEnd_98357 := by exact prefixLift 98357
  have htrace : WordTrace (prefixWord ++ tailWord_98357) baseStart_98357 baseEnd_98357 := by
    simpa [prefixWord, tailWord_98357, baseEnd_98357] using wordTrace_append hprefix tailTrace_98357
  have hstable : (prefixWord ++ tailWord_98357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98357).length < 2 ^ (prefixWord ++ tailWord_98357).sum := by decide
  have hdescent : baseEnd_98357 < baseStart_98357 := by decide
  rcases family_descends (prefixWord ++ tailWord_98357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98400 : List Nat := [2, 1, 1, 3, 2, 3, 4, 6]
def baseStart_98400 : Nat := 118140960795 + 98400 * 2 ^ 59
def prefixEnd_98400 : Nat := 4983230072969 + 3 ^ 40 * 98400 * 2
def baseEnd_98400 : Nat := 3742703437223721722035

theorem tailTrace_98400 : CollatzResearch.WordTrace tailWord_98400 prefixEnd_98400 3742703437223721722035 := by
  unfold tailWord_98400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794471421760540113582327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2392628562347386818109769 1794471421760540113582327)
  ·
    refine ⟨2691707132640810170373491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1794471421760540113582327 2691707132640810170373491)
    ·
      refine ⟨4037560698961215255560237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691707132640810170373491 4037560698961215255560237)
      ·
        refine ⟨1514085262110455720835089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4037560698961215255560237 1514085262110455720835089)
        ·
          refine ⟨1135563946582841790626317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514085262110455720835089 1135563946582841790626317)
          ·
            refine ⟨425836479968565671484869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1135563946582841790626317 425836479968565671484869)
            ·
              refine ⟨79844339994106063403413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 425836479968565671484869 79844339994106063403413)
              ·
                refine ⟨3742703437223721722035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79844339994106063403413 3742703437223721722035)
                ·
                  rfl

theorem cell22_98400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_98400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98400 prefixEnd_98400 := by exact prefixLift 98400
  have htrace : WordTrace (prefixWord ++ tailWord_98400) baseStart_98400 baseEnd_98400 := by
    simpa [prefixWord, tailWord_98400, baseEnd_98400] using wordTrace_append hprefix tailTrace_98400
  have hstable : (prefixWord ++ tailWord_98400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98400).length < 2 ^ (prefixWord ++ tailWord_98400).sum := by decide
  have hdescent : baseEnd_98400 < baseStart_98400 := by decide
  rcases family_descends (prefixWord ++ tailWord_98400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98530 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_98530 : Nat := 118140960795 + 98530 * 2 ^ 59
def prefixEnd_98530 : Nat := 4983230072969 + 3 ^ 40 * 98530 * 2
def baseEnd_98530 : Nat := 11242944197245496582639

theorem tailTrace_98530 : CollatzResearch.WordTrace tailWord_98530 prefixEnd_98530 11242944197245496582639 := by
  unfold tailWord_98530
  simp only [CollatzResearch.WordTrace]
  refine ⟨898421083262528107349261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2395789555366741619598029 898421083262528107349261)
  ·
    refine ⟨336907906223448040255973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 898421083262528107349261 336907906223448040255973)
    ·
      refine ⟨63170232416896507547995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336907906223448040255973 63170232416896507547995)
      ·
        refine ⟨94755348625344761321993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63170232416896507547995 94755348625344761321993)
        ·
          refine ⟨71066511469008570991495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94755348625344761321993 71066511469008570991495)
          ·
            refine ⟨106599767203512856487243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71066511469008570991495 106599767203512856487243)
            ·
              refine ⟨159899650805269284730865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106599767203512856487243 159899650805269284730865)
              ·
                refine ⟨119924738103951963548149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159899650805269284730865 119924738103951963548149)
                ·
                  refine ⟨11242944197245496582639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119924738103951963548149 11242944197245496582639)
                  ·
                    rfl

theorem cell22_98530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_98530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98530 prefixEnd_98530 := by exact prefixLift 98530
  have htrace : WordTrace (prefixWord ++ tailWord_98530) baseStart_98530 baseEnd_98530 := by
    simpa [prefixWord, tailWord_98530, baseEnd_98530] using wordTrace_append hprefix tailTrace_98530
  have hstable : (prefixWord ++ tailWord_98530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98530).length < 2 ^ (prefixWord ++ tailWord_98530).sum := by decide
  have hdescent : baseEnd_98530 < baseStart_98530 := by decide
  rcases family_descends (prefixWord ++ tailWord_98530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98556 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_98556 : Nat := 118140960795 + 98556 * 2 ^ 59
def prefixEnd_98556 : Nat := 4983230072969 + 3 ^ 40 * 98556 * 2
def baseEnd_98556 : Nat := 33737732923081088597837

theorem tailTrace_98556 : CollatzResearch.WordTrace tailWord_98556 prefixEnd_98556 33737732923081088597837 := by
  unfold tailWord_98556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797316315477959434921761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2396421753970612579895681 1797316315477959434921761)
  ·
    refine ⟨1347987236608469576191321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1797316315477959434921761 1347987236608469576191321)
    ·
      refine ⟨1010990427456352182143491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1347987236608469576191321 1010990427456352182143491)
      ·
        refine ⟨1516485641184528273215237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010990427456352182143491 1516485641184528273215237)
        ·
          refine ⟨284341057722099051227857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1516485641184528273215237 284341057722099051227857)
          ·
            refine ⟨213255793291574288420893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284341057722099051227857 213255793291574288420893)
            ·
              refine ⟨79970922484340358157835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213255793291574288420893 79970922484340358157835)
              ·
                refine ⟨119956383726510537236753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79970922484340358157835 119956383726510537236753)
                ·
                  refine ⟨89967287794882902927565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119956383726510537236753 89967287794882902927565)
                  ·
                    refine ⟨33737732923081088597837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89967287794882902927565 33737732923081088597837)
                    ·
                      rfl

theorem cell22_98556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_98556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98556 prefixEnd_98556 := by exact prefixLift 98556
  have htrace : WordTrace (prefixWord ++ tailWord_98556) baseStart_98556 baseEnd_98556 := by
    simpa [prefixWord, tailWord_98556, baseEnd_98556] using wordTrace_append hprefix tailTrace_98556
  have hstable : (prefixWord ++ tailWord_98556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98556).length < 2 ^ (prefixWord ++ tailWord_98556).sum := by decide
  have hdescent : baseEnd_98556 < baseStart_98556 := by decide
  rcases family_descends (prefixWord ++ tailWord_98556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98652 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_98652 : Nat := 118140960795 + 98652 * 2 ^ 59
def prefixEnd_98652 : Nat := 4983230072969 + 3 ^ 40 * 98652 * 2
def baseEnd_98652 : Nat := 33770595684968838197543

theorem tailTrace_98652 : CollatzResearch.WordTrace tailWord_98652 prefixEnd_98652 33770595684968838197543 := by
  unfold tailWord_98652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1799067019304063632669105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2398756025738751510225473 1799067019304063632669105)
  ·
    refine ⟨1349300264478047724501829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1799067019304063632669105 1349300264478047724501829)
    ·
      refine ⟨252993799589633948344093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1349300264478047724501829 252993799589633948344093)
      ·
        refine ⟨94872674846112730629035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252993799589633948344093 94872674846112730629035)
        ·
          refine ⟨142309012269169095943553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94872674846112730629035 142309012269169095943553)
          ·
            refine ⟨106731759201876821957665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142309012269169095943553 106731759201876821957665)
            ·
              refine ⟨80048819401407616468249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106731759201876821957665 80048819401407616468249)
              ·
                refine ⟨60036614551055712351187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80048819401407616468249 60036614551055712351187)
                ·
                  refine ⟨90054921826583568526781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60036614551055712351187 90054921826583568526781)
                  ·
                    refine ⟨33770595684968838197543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90054921826583568526781 33770595684968838197543)
                    ·
                      rfl

theorem cell22_98652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_98652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98652 prefixEnd_98652 := by exact prefixLift 98652
  have htrace : WordTrace (prefixWord ++ tailWord_98652) baseStart_98652 baseEnd_98652 := by
    simpa [prefixWord, tailWord_98652, baseEnd_98652] using wordTrace_append hprefix tailTrace_98652
  have hstable : (prefixWord ++ tailWord_98652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98652).length < 2 ^ (prefixWord ++ tailWord_98652).sum := by decide
  have hdescent : baseEnd_98652 < baseStart_98652 := by decide
  rcases family_descends (prefixWord ++ tailWord_98652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98659 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 4]
def baseStart_98659 : Nat := 118140960795 + 98659 * 2 ^ 59
def prefixEnd_98659 : Nat := 4983230072969 + 3 ^ 40 * 98659 * 2
def baseEnd_98659 : Nat := 11257663976007717757507

theorem tailTrace_98659 : CollatzResearch.WordTrace tailWord_98659 prefixEnd_98659 11257663976007717757507 := by
  unfold tailWord_98659
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598389349582767460843031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2398926233055178307228687 3598389349582767460843031)
  ·
    refine ⟨5397584024374151191264547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3598389349582767460843031 5397584024374151191264547)
    ·
      refine ⟨8096376036561226786896821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5397584024374151191264547 8096376036561226786896821)
      ·
        refine ⟨759035253427615011271577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8096376036561226786896821 759035253427615011271577)
        ·
          refine ⟨569276440070711258453683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759035253427615011271577 569276440070711258453683)
          ·
            refine ⟨853914660106066887680525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569276440070711258453683 853914660106066887680525)
            ·
              refine ⟨320217997539775082880197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853914660106066887680525 320217997539775082880197)
              ·
                refine ⟨60040874538707828040037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320217997539775082880197 60040874538707828040037)
                ·
                  refine ⟨11257663976007717757507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60040874538707828040037 11257663976007717757507)
                  ·
                    rfl

theorem cell22_98659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 4].length) (baseStart_98659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98659 prefixEnd_98659 := by exact prefixLift 98659
  have htrace : WordTrace (prefixWord ++ tailWord_98659) baseStart_98659 baseEnd_98659 := by
    simpa [prefixWord, tailWord_98659, baseEnd_98659] using wordTrace_append hprefix tailTrace_98659
  have hstable : (prefixWord ++ tailWord_98659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98659).length < 2 ^ (prefixWord ++ tailWord_98659).sum := by decide
  have hdescent : baseEnd_98659 < baseStart_98659 := by decide
  rcases family_descends (prefixWord ++ tailWord_98659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98674 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_98674 : Nat := 118140960795 + 98674 * 2 ^ 59
def prefixEnd_98674 : Nat := 4983230072969 + 3 ^ 40 * 98674 * 2
def baseEnd_98674 : Nat := 33778126734568114147475

theorem tailTrace_98674 : CollatzResearch.WordTrace tailWord_98674 prefixEnd_98674 33778126734568114147475 := by
  unfold tailWord_98674
  simp only [CollatzResearch.WordTrace]
  refine ⟨899734111132106255659769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2399290963018950015092717 899734111132106255659769)
  ·
    refine ⟨674800583349079691744827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 899734111132106255659769 674800583349079691744827)
    ·
      refine ⟨1012200875023619537617241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674800583349079691744827 1012200875023619537617241)
      ·
        refine ⟨759150656267714653212931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1012200875023619537617241 759150656267714653212931)
        ·
          refine ⟨1138725984401571979819397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759150656267714653212931 1138725984401571979819397)
          ·
            refine ⟨213511122075294746216137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1138725984401571979819397 213511122075294746216137)
            ·
              refine ⟨160133341556471059662103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213511122075294746216137 160133341556471059662103)
              ·
                refine ⟨240200012334706589493155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160133341556471059662103 240200012334706589493155)
                ·
                  refine ⟨360300018502059884239733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240200012334706589493155 360300018502059884239733)
                  ·
                    refine ⟨33778126734568114147475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 360300018502059884239733 33778126734568114147475)
                    ·
                      rfl

theorem cell22_98674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_98674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98674 prefixEnd_98674 := by exact prefixLift 98674
  have htrace : WordTrace (prefixWord ++ tailWord_98674) baseStart_98674 baseEnd_98674 := by
    simpa [prefixWord, tailWord_98674, baseEnd_98674] using wordTrace_append hprefix tailTrace_98674
  have hstable : (prefixWord ++ tailWord_98674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98674).length < 2 ^ (prefixWord ++ tailWord_98674).sum := by decide
  have hdescent : baseEnd_98674 < baseStart_98674 := by decide
  rcases family_descends (prefixWord ++ tailWord_98674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98689 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_98689 : Nat := 118140960795 + 98689 * 2 ^ 59
def prefixEnd_98689 : Nat := 4983230072969 + 3 ^ 40 * 98689 * 2
def baseEnd_98689 : Nat := 33783261541113075022429

theorem tailTrace_98689 : CollatzResearch.WordTrace tailWord_98689 prefixEnd_98689 33783261541113075022429 := by
  unfold tailWord_98689
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599483539474082584435121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2399655692982721722956747 3599483539474082584435121)
  ·
    refine ⟨2699612654605561938326341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3599483539474082584435121 2699612654605561938326341)
    ·
      refine ⟨506177372738542863436189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2699612654605561938326341 506177372738542863436189)
      ·
        refine ⟨189816514776953573788571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506177372738542863436189 189816514776953573788571)
        ·
          refine ⟨284724772165430360682857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189816514776953573788571 284724772165430360682857)
          ·
            refine ⟨213543579124072770512143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284724772165430360682857 213543579124072770512143)
            ·
              refine ⟨320315368686109155768215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213543579124072770512143 320315368686109155768215)
              ·
                refine ⟨480473053029163733652323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320315368686109155768215 480473053029163733652323)
                ·
                  refine ⟨720709579543745600478485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480473053029163733652323 720709579543745600478485)
                  ·
                    refine ⟨33783261541113075022429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 720709579543745600478485 33783261541113075022429)
                    ·
                      rfl

theorem cell22_98689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_98689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98689 prefixEnd_98689 := by exact prefixLift 98689
  have htrace : WordTrace (prefixWord ++ tailWord_98689) baseStart_98689 baseEnd_98689 := by
    simpa [prefixWord, tailWord_98689, baseEnd_98689] using wordTrace_append hprefix tailTrace_98689
  have hstable : (prefixWord ++ tailWord_98689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98689).length < 2 ^ (prefixWord ++ tailWord_98689).sum := by decide
  have hdescent : baseEnd_98689 < baseStart_98689 := by decide
  rcases family_descends (prefixWord ++ tailWord_98689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98710 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_98710 : Nat := 118140960795 + 98710 * 2 ^ 59
def prefixEnd_98710 : Nat := 4983230072969 + 3 ^ 40 * 98710 * 2
def baseEnd_98710 : Nat := 11263483423425340082455

theorem tailTrace_98710 : CollatzResearch.WordTrace tailWord_98710 prefixEnd_98710 11263483423425340082455 := by
  unfold tailWord_98710
  simp only [CollatzResearch.WordTrace]
  refine ⟨225015592024875198184349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2400166314932002113966389 225015592024875198184349)
  ·
    refine ⟨84380847009328199319131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225015592024875198184349 84380847009328199319131)
    ·
      refine ⟨126571270513992298978697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84380847009328199319131 126571270513992298978697)
      ·
        refine ⟨94928452885494224234023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126571270513992298978697 94928452885494224234023)
        ·
          refine ⟨142392679328241336351035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94928452885494224234023 142392679328241336351035)
          ·
            refine ⟨213589018992362004526553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142392679328241336351035 213589018992362004526553)
            ·
              refine ⟨160191764244271503394915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213589018992362004526553 160191764244271503394915)
              ·
                refine ⟨240287646366407255092373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160191764244271503394915 240287646366407255092373)
                ·
                  refine ⟨11263483423425340082455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240287646366407255092373 11263483423425340082455)
                  ·
                    rfl

theorem cell22_98710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_98710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98710 prefixEnd_98710 := by exact prefixLift 98710
  have htrace : WordTrace (prefixWord ++ tailWord_98710) baseStart_98710 baseEnd_98710 := by
    simpa [prefixWord, tailWord_98710, baseEnd_98710] using wordTrace_append hprefix tailTrace_98710
  have hstable : (prefixWord ++ tailWord_98710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98710).length < 2 ^ (prefixWord ++ tailWord_98710).sum := by decide
  have hdescent : baseEnd_98710 < baseStart_98710 := by decide
  rcases family_descends (prefixWord ++ tailWord_98710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98770 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_98770 : Nat := 118140960795 + 98770 * 2 ^ 59
def prefixEnd_98770 : Nat := 4983230072969 + 3 ^ 40 * 98770 * 2
def baseEnd_98770 : Nat := 33810989496455863747181

theorem tailTrace_98770 : CollatzResearch.WordTrace tailWord_98770 prefixEnd_98770 33810989496455863747181 := by
  unfold tailWord_98770
  simp only [CollatzResearch.WordTrace]
  refine ⟨900609463045158354533441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2401625234787088945422509 900609463045158354533441)
  ·
    refine ⟨675457097283868765900081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 900609463045158354533441 675457097283868765900081)
    ·
      refine ⟨506592822962901574425061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675457097283868765900081 506592822962901574425061)
      ·
        refine ⟨94986154305544045204699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506592822962901574425061 94986154305544045204699)
        ·
          refine ⟨142479231458316067807049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94986154305544045204699 142479231458316067807049)
          ·
            refine ⟨106859423593737050855287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142479231458316067807049 106859423593737050855287)
            ·
              refine ⟨160289135390605576282931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106859423593737050855287 160289135390605576282931)
              ·
                refine ⟨240433703085908364424397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160289135390605576282931 240433703085908364424397)
                ·
                  refine ⟨90162638657215636659149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240433703085908364424397 90162638657215636659149)
                  ·
                    refine ⟨33810989496455863747181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90162638657215636659149 33810989496455863747181)
                    ·
                      rfl

theorem cell22_98770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_98770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98770 prefixEnd_98770 := by exact prefixLift 98770
  have htrace : WordTrace (prefixWord ++ tailWord_98770) baseStart_98770 baseEnd_98770 := by
    simpa [prefixWord, tailWord_98770, baseEnd_98770] using wordTrace_append hprefix tailTrace_98770
  have hstable : (prefixWord ++ tailWord_98770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98770).length < 2 ^ (prefixWord ++ tailWord_98770).sum := by decide
  have hdescent : baseEnd_98770 < baseStart_98770 := by decide
  rcases family_descends (prefixWord ++ tailWord_98770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98807 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_98807 : Nat := 118140960795 + 98807 * 2 ^ 59
def prefixEnd_98807 : Nat := 4983230072969 + 3 ^ 40 * 98807 * 2
def baseEnd_98807 : Nat := 33823655352600100572067

theorem tailTrace_98807 : CollatzResearch.WordTrace tailWord_98807 prefixEnd_98807 33823655352600100572067 := by
  unfold tailWord_98807
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603787353046588737230675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2402524902031059158153783 3603787353046588737230675)
  ·
    refine ⟨5405681029569883105846013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603787353046588737230675 5405681029569883105846013)
    ·
      refine ⟨2027130386088706164692255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5405681029569883105846013 2027130386088706164692255)
      ·
        refine ⟨3040695579133059247038383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027130386088706164692255 3040695579133059247038383)
        ·
          refine ⟨4561043368699588870557575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040695579133059247038383 4561043368699588870557575)
          ·
            refine ⟨6841565053049383305836363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561043368699588870557575 6841565053049383305836363)
            ·
              refine ⟨10262347579574074958754545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841565053049383305836363 10262347579574074958754545)
              ·
                refine ⟨7696760684680556219065909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10262347579574074958754545 7696760684680556219065909)
                ·
                  refine ⟨721571314188802145537429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7696760684680556219065909 721571314188802145537429)
                  ·
                    refine ⟨33823655352600100572067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 721571314188802145537429 33823655352600100572067)
                    ·
                      rfl

theorem cell22_98807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_98807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98807 prefixEnd_98807 := by exact prefixLift 98807
  have htrace : WordTrace (prefixWord ++ tailWord_98807) baseStart_98807 baseEnd_98807 := by
    simpa [prefixWord, tailWord_98807, baseEnd_98807] using wordTrace_append hprefix tailTrace_98807
  have hstable : (prefixWord ++ tailWord_98807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98807).length < 2 ^ (prefixWord ++ tailWord_98807).sum := by decide
  have hdescent : baseEnd_98807 < baseStart_98807 := by decide
  rcases family_descends (prefixWord ++ tailWord_98807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98809 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_98809 : Nat := 118140960795 + 98809 * 2 ^ 59
def prefixEnd_98809 : Nat := 4983230072969 + 3 ^ 40 * 98809 * 2
def baseEnd_98809 : Nat := 33824339993472762022061

theorem tailTrace_98809 : CollatzResearch.WordTrace tailWord_98809 prefixEnd_98809 33824339993472762022061 := by
  unfold tailWord_98809
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603860299039343078803481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2402573532692895385868987 3603860299039343078803481)
  ·
    refine ⟨2702895224279507309102611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3603860299039343078803481 2702895224279507309102611)
    ·
      refine ⟨4054342836419260963653917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2702895224279507309102611 4054342836419260963653917)
      ·
        refine ⟨1520378563657222861370219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4054342836419260963653917 1520378563657222861370219)
        ·
          refine ⟨2280567845485834292055329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520378563657222861370219 2280567845485834292055329)
          ·
            refine ⟨1710425884114375719041497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280567845485834292055329 1710425884114375719041497)
            ·
              refine ⟨1282819413085781789281123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710425884114375719041497 1282819413085781789281123)
              ·
                refine ⟨1924229119628672683921685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282819413085781789281123 1924229119628672683921685)
                ·
                  refine ⟨90198239982594032058829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1924229119628672683921685 90198239982594032058829)
                  ·
                    refine ⟨33824339993472762022061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90198239982594032058829 33824339993472762022061)
                    ·
                      rfl

theorem cell22_98809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_98809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98809 prefixEnd_98809 := by exact prefixLift 98809
  have htrace : WordTrace (prefixWord ++ tailWord_98809) baseStart_98809 baseEnd_98809 := by
    simpa [prefixWord, tailWord_98809, baseEnd_98809] using wordTrace_append hprefix tailTrace_98809
  have hstable : (prefixWord ++ tailWord_98809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98809).length < 2 ^ (prefixWord ++ tailWord_98809).sum := by decide
  have hdescent : baseEnd_98809 < baseStart_98809 := by decide
  rcases family_descends (prefixWord ++ tailWord_98809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98828 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 4]
def baseStart_98828 : Nat := 118140960795 + 98828 * 2 ^ 59
def prefixEnd_98828 : Nat := 4983230072969 + 3 ^ 40 * 98828 * 2
def baseEnd_98828 : Nat := 11276948027254348599001

theorem tailTrace_98828 : CollatzResearch.WordTrace tailWord_98828 prefixEnd_98828 11276948027254348599001 := by
  unfold tailWord_98828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802276642985254661872569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2403035523980339549163425 1802276642985254661872569)
  ·
    refine ⟨1351707482238940996404427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1802276642985254661872569 1351707482238940996404427)
    ·
      refine ⟨2027561223358411494606641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351707482238940996404427 2027561223358411494606641)
      ·
        refine ⟨1520670917518808620954981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027561223358411494606641 1520670917518808620954981)
        ·
          refine ⟨285125797034776616429059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1520670917518808620954981 285125797034776616429059)
          ·
            refine ⟨427688695552164924643589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285125797034776616429059 427688695552164924643589)
            ·
              refine ⟨80191630416030923370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 427688695552164924643589 80191630416030923370673)
              ·
                refine ⟨60143722812023192528005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80191630416030923370673 60143722812023192528005)
                ·
                  refine ⟨11276948027254348599001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60143722812023192528005 11276948027254348599001)
                  ·
                    rfl

theorem cell22_98828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_98828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98828 prefixEnd_98828 := by exact prefixLift 98828
  have htrace : WordTrace (prefixWord ++ tailWord_98828) baseStart_98828 baseEnd_98828 := by
    simpa [prefixWord, tailWord_98828, baseEnd_98828] using wordTrace_append hprefix tailTrace_98828
  have hstable : (prefixWord ++ tailWord_98828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98828).length < 2 ^ (prefixWord ++ tailWord_98828).sum := by decide
  have hdescent : baseEnd_98828 < baseStart_98828 := by decide
  rcases family_descends (prefixWord ++ tailWord_98828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98858 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_98858 : Nat := 118140960795 + 98858 * 2 ^ 59
def prefixEnd_98858 : Nat := 4983230072969 + 3 ^ 40 * 98858 * 2
def baseEnd_98858 : Nat := 33841113694852967546911

theorem tailTrace_98858 : CollatzResearch.WordTrace tailWord_98858 prefixEnd_98858 33841113694852967546911 := by
  unfold tailWord_98858
  simp only [CollatzResearch.WordTrace]
  refine ⟨901411868965456111834307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2403764983907882964891485 901411868965456111834307)
  ·
    refine ⟨1352117803448184167751461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 901411868965456111834307 1352117803448184167751461)
    ·
      refine ⟨253522088146534531453399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1352117803448184167751461 253522088146534531453399)
      ·
        refine ⟨380283132219801797180099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253522088146534531453399 380283132219801797180099)
        ·
          refine ⟨570424698329702695770149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380283132219801797180099 570424698329702695770149)
          ·
            refine ⟨106954630936819255456903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 570424698329702695770149 106954630936819255456903)
            ·
              refine ⟨160431946405228883185355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106954630936819255456903 160431946405228883185355)
              ·
                refine ⟨240647919607843324778033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160431946405228883185355 240647919607843324778033)
                ·
                  refine ⟨180485939705882493583525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240647919607843324778033 180485939705882493583525)
                  ·
                    refine ⟨33841113694852967546911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180485939705882493583525 33841113694852967546911)
                    ·
                      rfl

theorem cell22_98858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_98858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98858 prefixEnd_98858 := by exact prefixLift 98858
  have htrace : WordTrace (prefixWord ++ tailWord_98858) baseStart_98858 baseEnd_98858 := by
    simpa [prefixWord, tailWord_98858, baseEnd_98858] using wordTrace_append hprefix tailTrace_98858
  have hstable : (prefixWord ++ tailWord_98858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98858).length < 2 ^ (prefixWord ++ tailWord_98858).sum := by decide
  have hdescent : baseEnd_98858 < baseStart_98858 := by decide
  rcases family_descends (prefixWord ++ tailWord_98858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_98997 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 4]
def baseStart_98997 : Nat := 118140960795 + 98997 * 2 ^ 59
def prefixEnd_98997 : Nat := 4983230072969 + 3 ^ 40 * 98997 * 2
def baseEnd_98997 : Nat := 11296232078500979440495

theorem tailTrace_98997 : CollatzResearch.WordTrace tailWord_98997 prefixEnd_98997 11296232078500979440495 := by
  unfold tailWord_98997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610717222358251186647245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2407144814905500791098163 3610717222358251186647245)
  ·
    refine ⟨1354018958384344194992717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3610717222358251186647245 1354018958384344194992717)
    ·
      refine ⟨507757109394129073122269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1354018958384344194992717 507757109394129073122269)
      ·
        refine ⟨190408916022798402420851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507757109394129073122269 190408916022798402420851)
        ·
          refine ⟨285613374034197603631277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190408916022798402420851 285613374034197603631277)
          ·
            refine ⟨107105015262824101361729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285613374034197603631277 107105015262824101361729)
            ·
              refine ⟨80328761447118076021297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107105015262824101361729 80328761447118076021297)
              ·
                refine ⟨60246571085338557015973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80328761447118076021297 60246571085338557015973)
                ·
                  refine ⟨11296232078500979440495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60246571085338557015973 11296232078500979440495)
                  ·
                    rfl

theorem cell22_98997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_98997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_98997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_98997 prefixEnd_98997 := by exact prefixLift 98997
  have htrace : WordTrace (prefixWord ++ tailWord_98997) baseStart_98997 baseEnd_98997 := by
    simpa [prefixWord, tailWord_98997, baseEnd_98997] using wordTrace_append hprefix tailTrace_98997
  have hstable : (prefixWord ++ tailWord_98997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_98997).length < 2 ^ (prefixWord ++ tailWord_98997).sum := by decide
  have hdescent : baseEnd_98997 < baseStart_98997 := by decide
  rcases family_descends (prefixWord ++ tailWord_98997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99019 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 11]
def baseStart_99019 : Nat := 118140960795 + 99019 * 2 ^ 59
def prefixEnd_99019 : Nat := 4983230072969 + 3 ^ 40 * 99019 * 2
def baseEnd_99019 : Nat := 11298742428367404757139

theorem tailTrace_99019 : CollatzResearch.WordTrace tailWord_99019 prefixEnd_99019 11298742428367404757139 := by
  unfold tailWord_99019
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611519628278548943948111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2407679752185699295965407 3611519628278548943948111)
  ·
    refine ⟨5417279442417823415922167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3611519628278548943948111 5417279442417823415922167)
    ·
      refine ⟨8125919163626735123883251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5417279442417823415922167 8125919163626735123883251)
      ·
        refine ⟨12188878745440102685824877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8125919163626735123883251 12188878745440102685824877)
        ·
          refine ⟨4570829529540038507184329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12188878745440102685824877 4570829529540038507184329)
          ·
            refine ⟨3428122147155028880388247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570829529540038507184329 3428122147155028880388247)
            ·
              refine ⟨5142183220732543320582371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428122147155028880388247 5142183220732543320582371)
              ·
                refine ⟨7713274831098814980873557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5142183220732543320582371 7713274831098814980873557)
                ·
                  refine ⟨11298742428367404757139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 7713274831098814980873557 11298742428367404757139)
                  ·
                    rfl

theorem cell22_99019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_99019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99019 prefixEnd_99019 := by exact prefixLift 99019
  have htrace : WordTrace (prefixWord ++ tailWord_99019) baseStart_99019 baseEnd_99019 := by
    simpa [prefixWord, tailWord_99019, baseEnd_99019] using wordTrace_append hprefix tailTrace_99019
  have hstable : (prefixWord ++ tailWord_99019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99019).length < 2 ^ (prefixWord ++ tailWord_99019).sum := by decide
  have hdescent : baseEnd_99019 < baseStart_99019 := by decide
  rcases family_descends (prefixWord ++ tailWord_99019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99066 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_99066 : Nat := 118140960795 + 99066 * 2 ^ 59
def prefixEnd_99066 : Nat := 4983230072969 + 3 ^ 40 * 99066 * 2
def baseEnd_99066 : Nat := 33912316345609758346273

theorem tailTrace_99066 : CollatzResearch.WordTrace tailWord_99066 prefixEnd_99066 33912316345609758346273 := by
  unfold tailWord_99066
  simp only [CollatzResearch.WordTrace]
  refine ⟨903308464777068992727263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2408822572738850647272701 903308464777068992727263)
  ·
    refine ⟨1354962697165603489090895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 903308464777068992727263 1354962697165603489090895)
    ·
      refine ⟨2032444045748405233636343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354962697165603489090895 2032444045748405233636343)
      ·
        refine ⟨3048666068622607850454515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032444045748405233636343 3048666068622607850454515)
        ·
          refine ⟨4572999102933911775681773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048666068622607850454515 4572999102933911775681773)
          ·
            refine ⟨1714874663600216915880665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4572999102933911775681773 1714874663600216915880665)
            ·
              refine ⟨1286155997700162686910499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714874663600216915880665 1286155997700162686910499)
              ·
                refine ⟨1929233996550244030365749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286155997700162686910499 1929233996550244030365749)
                ·
                  refine ⟨180865687176585377846789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929233996550244030365749 180865687176585377846789)
                  ·
                    refine ⟨33912316345609758346273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180865687176585377846789 33912316345609758346273)
                    ·
                      rfl

theorem cell22_99066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_99066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99066 prefixEnd_99066 := by exact prefixLift 99066
  have htrace : WordTrace (prefixWord ++ tailWord_99066) baseStart_99066 baseEnd_99066 := by
    simpa [prefixWord, tailWord_99066, baseEnd_99066] using wordTrace_append hprefix tailTrace_99066
  have hstable : (prefixWord ++ tailWord_99066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99066).length < 2 ^ (prefixWord ++ tailWord_99066).sum := by decide
  have hdescent : baseEnd_99066 < baseStart_99066 := by decide
  rcases family_descends (prefixWord ++ tailWord_99066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99081 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 6]
def baseStart_99081 : Nat := 118140960795 + 99081 * 2 ^ 59
def prefixEnd_99081 : Nat := 4983230072969 + 3 ^ 40 * 99081 * 2
def baseEnd_99081 : Nat := 11305817050718239740409

theorem tailTrace_99081 : CollatzResearch.WordTrace tailWord_99081 prefixEnd_99081 11305817050718239740409 := by
  unfold tailWord_99081
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613780954053933532705097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2409187302702622355136731 3613780954053933532705097)
  ·
    refine ⟨2710335715540450149528823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3613780954053933532705097 2710335715540450149528823)
    ·
      refine ⟨4065503573310675224293235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710335715540450149528823 4065503573310675224293235)
      ·
        refine ⟨6098255359966012836439853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065503573310675224293235 6098255359966012836439853)
        ·
          refine ⟨2286845759987254813664945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6098255359966012836439853 2286845759987254813664945)
          ·
            refine ⟨1715134319990441110248709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2286845759987254813664945 1715134319990441110248709)
            ·
              refine ⟨321587684998207708171633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1715134319990441110248709 321587684998207708171633)
              ·
                refine ⟨241190763748655781128725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321587684998207708171633 241190763748655781128725)
                ·
                  refine ⟨11305817050718239740409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 241190763748655781128725 11305817050718239740409)
                  ·
                    rfl

theorem cell22_99081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_99081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99081 prefixEnd_99081 := by exact prefixLift 99081
  have htrace : WordTrace (prefixWord ++ tailWord_99081) baseStart_99081 baseEnd_99081 := by
    simpa [prefixWord, tailWord_99081, baseEnd_99081] using wordTrace_append hprefix tailTrace_99081
  have hstable : (prefixWord ++ tailWord_99081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99081).length < 2 ^ (prefixWord ++ tailWord_99081).sum := by decide
  have hdescent : baseEnd_99081 < baseStart_99081 := by decide
  rcases family_descends (prefixWord ++ tailWord_99081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99096 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_99096 : Nat := 118140960795 + 99096 * 2 ^ 59
def prefixEnd_99096 : Nat := 4983230072969 + 3 ^ 40 * 99096 * 2
def baseEnd_99096 : Nat := 33922585958699680096181

theorem tailTrace_99096 : CollatzResearch.WordTrace tailWord_99096 prefixEnd_99096 33922585958699680096181 := by
  unfold tailWord_99096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807164024499795547250571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2409552032666394063000761 1807164024499795547250571)
  ·
    refine ⟨2710746036749693320875857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1807164024499795547250571 2710746036749693320875857)
    ·
      refine ⟨2033059527562269990656893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2710746036749693320875857 2033059527562269990656893)
      ·
        refine ⟨762397322835851246496335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2033059527562269990656893 762397322835851246496335)
        ·
          refine ⟨1143595984253776869744503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762397322835851246496335 1143595984253776869744503)
          ·
            refine ⟨1715393976380665304616755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143595984253776869744503 1715393976380665304616755)
            ·
              refine ⟨2573090964570997956925133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715393976380665304616755 2573090964570997956925133)
              ·
                refine ⟨964909111714124233846925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573090964570997956925133 964909111714124233846925)
                ·
                  refine ⟨361840916892796587692597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964909111714124233846925 361840916892796587692597)
                  ·
                    refine ⟨33922585958699680096181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 361840916892796587692597 33922585958699680096181)
                    ·
                      rfl

theorem cell22_99096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_99096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99096 prefixEnd_99096 := by exact prefixLift 99096
  have htrace : WordTrace (prefixWord ++ tailWord_99096) baseStart_99096 baseEnd_99096 := by
    simpa [prefixWord, tailWord_99096, baseEnd_99096] using wordTrace_append hprefix tailTrace_99096
  have hstable : (prefixWord ++ tailWord_99096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99096).length < 2 ^ (prefixWord ++ tailWord_99096).sum := by decide
  have hdescent : baseEnd_99096 < baseStart_99096 := by decide
  rcases family_descends (prefixWord ++ tailWord_99096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99134 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_99134 : Nat := 118140960795 + 99134 * 2 ^ 59
def prefixEnd_99134 : Nat := 4983230072969 + 3 ^ 40 * 99134 * 2
def baseEnd_99134 : Nat := 33935594135280247646065

theorem tailTrace_99134 : CollatzResearch.WordTrace tailWord_99134 prefixEnd_99134 33935594135280247646065 := by
  unfold tailWord_99134
  simp only [CollatzResearch.WordTrace]
  refine ⟨451964252857740448048057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2410476015241282389589637 451964252857740448048057)
  ·
    refine ⟨338973189643305336036043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 451964252857740448048057 338973189643305336036043)
    ·
      refine ⟨508459784464958004054065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338973189643305336036043 508459784464958004054065)
      ·
        refine ⟨381344838348718503040549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508459784464958004054065 381344838348718503040549)
        ·
          refine ⟨71502157190384719320103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381344838348718503040549 71502157190384719320103)
          ·
            refine ⟨107253235785577078980155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71502157190384719320103 107253235785577078980155)
            ·
              refine ⟨160879853678365618470233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107253235785577078980155 160879853678365618470233)
              ·
                refine ⟨120659890258774213852675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160879853678365618470233 120659890258774213852675)
                ·
                  refine ⟨180989835388161320779013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120659890258774213852675 180989835388161320779013)
                  ·
                    refine ⟨33935594135280247646065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 180989835388161320779013 33935594135280247646065)
                    ·
                      rfl

theorem cell22_99134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_99134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99134 prefixEnd_99134 := by exact prefixLift 99134
  have htrace : WordTrace (prefixWord ++ tailWord_99134) baseStart_99134 baseEnd_99134 := by
    simpa [prefixWord, tailWord_99134, baseEnd_99134] using wordTrace_append hprefix tailTrace_99134
  have hstable : (prefixWord ++ tailWord_99134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99134).length < 2 ^ (prefixWord ++ tailWord_99134).sum := by decide
  have hdescent : baseEnd_99134 < baseStart_99134 := by decide
  rcases family_descends (prefixWord ++ tailWord_99134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99278 : List Nat := [4, 1, 1, 1, 2, 3, 10]
def baseStart_99278 : Nat := 118140960795 + 99278 * 2 ^ 59
def prefixEnd_99278 : Nat := 4983230072969 + 3 ^ 40 * 99278 * 2
def baseEnd_99278 : Nat := 1258699565855995260949

theorem tailTrace_99278 : CollatzResearch.WordTrace tailWord_99278 prefixEnd_99278 1258699565855995260949 := by
  unfold tailWord_99278
  simp only [CollatzResearch.WordTrace]
  refine ⟨452620766792529522203311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2413977422893490785084325 452620766792529522203311)
  ·
    refine ⟨678931150188794283304967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 452620766792529522203311 678931150188794283304967)
    ·
      refine ⟨1018396725283191424957451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678931150188794283304967 1018396725283191424957451)
      ·
        refine ⟨1527595087924787137436177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018396725283191424957451 1527595087924787137436177)
        ·
          refine ⟨1145696315943590353077133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1527595087924787137436177 1145696315943590353077133)
          ·
            refine ⟨429636118478846382403925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1145696315943590353077133 429636118478846382403925)
            ·
              refine ⟨1258699565855995260949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 429636118478846382403925 1258699565855995260949)
              ·
                rfl

theorem cell22_99278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 10].length) (baseStart_99278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99278 prefixEnd_99278 := by exact prefixLift 99278
  have htrace : WordTrace (prefixWord ++ tailWord_99278) baseStart_99278 baseEnd_99278 := by
    simpa [prefixWord, tailWord_99278, baseEnd_99278] using wordTrace_append hprefix tailTrace_99278
  have hstable : (prefixWord ++ tailWord_99278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99278).length < 2 ^ (prefixWord ++ tailWord_99278).sum := by decide
  have hdescent : baseEnd_99278 < baseStart_99278 := by decide
  rcases family_descends (prefixWord ++ tailWord_99278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99282 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_99282 : Nat := 118140960795 + 99282 * 2 ^ 59
def prefixEnd_99282 : Nat := 4983230072969 + 3 ^ 40 * 99282 * 2
def baseEnd_99282 : Nat := 33986257559857194945611

theorem tailTrace_99282 : CollatzResearch.WordTrace tailWord_99282 prefixEnd_99282 33986257559857194945611 := by
  unfold tailWord_99282
  simp only [CollatzResearch.WordTrace]
  refine ⟨905278006581436215193025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2414074684217163240514733 905278006581436215193025)
  ·
    refine ⟨678958504936077161394769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 905278006581436215193025 678958504936077161394769)
    ·
      refine ⟨509218878702057871046077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678958504936077161394769 509218878702057871046077)
      ·
        refine ⟨190957079513271701642279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509218878702057871046077 190957079513271701642279)
        ·
          refine ⟨286435619269907552463419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190957079513271701642279 286435619269907552463419)
          ·
            refine ⟨429653428904861328695129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286435619269907552463419 429653428904861328695129)
            ·
              refine ⟨322240071678645996521347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429653428904861328695129 322240071678645996521347)
              ·
                refine ⟨483360107517968994782021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322240071678645996521347 483360107517968994782021)
                ·
                  refine ⟨90630020159619186521629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483360107517968994782021 90630020159619186521629)
                  ·
                    refine ⟨33986257559857194945611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90630020159619186521629 33986257559857194945611)
                    ·
                      rfl

theorem cell22_99282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_99282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99282 prefixEnd_99282 := by exact prefixLift 99282
  have htrace : WordTrace (prefixWord ++ tailWord_99282) baseStart_99282 baseEnd_99282 := by
    simpa [prefixWord, tailWord_99282, baseEnd_99282] using wordTrace_append hprefix tailTrace_99282
  have hstable : (prefixWord ++ tailWord_99282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99282).length < 2 ^ (prefixWord ++ tailWord_99282).sum := by decide
  have hdescent : baseEnd_99282 < baseStart_99282 := by decide
  rcases family_descends (prefixWord ++ tailWord_99282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99284 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 4]
def baseStart_99284 : Nat := 118140960795 + 99284 * 2 ^ 59
def prefixEnd_99284 : Nat := 4983230072969 + 3 ^ 40 * 99284 * 2
def baseEnd_99284 : Nat := 11328980733576618798535

theorem tailTrace_99284 : CollatzResearch.WordTrace tailWord_99284 prefixEnd_99284 11328980733576618798535 := by
  unfold tailWord_99284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810592486159249601172453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2414123314878999468229937 1810592486159249601172453)
  ·
    refine ⟨339486091154859300219835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1810592486159249601172453 339486091154859300219835)
    ·
      refine ⟨509229136732288950329753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339486091154859300219835 509229136732288950329753)
      ·
        refine ⟨381921852549216712747315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509229136732288950329753 381921852549216712747315)
        ·
          refine ⟨572882778823825069120973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381921852549216712747315 572882778823825069120973)
          ·
            refine ⟨214831042058934400920365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572882778823825069120973 214831042058934400920365)
            ·
              refine ⟨80561640772100400345137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214831042058934400920365 80561640772100400345137)
              ·
                refine ⟨60421230579075300258853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80561640772100400345137 60421230579075300258853)
                ·
                  refine ⟨11328980733576618798535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60421230579075300258853 11328980733576618798535)
                  ·
                    rfl

theorem cell22_99284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_99284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99284 prefixEnd_99284 := by exact prefixLift 99284
  have htrace : WordTrace (prefixWord ++ tailWord_99284) baseStart_99284 baseEnd_99284 := by
    simpa [prefixWord, tailWord_99284, baseEnd_99284] using wordTrace_append hprefix tailTrace_99284
  have hstable : (prefixWord ++ tailWord_99284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99284).length < 2 ^ (prefixWord ++ tailWord_99284).sum := by decide
  have hdescent : baseEnd_99284 < baseStart_99284 := by decide
  rcases family_descends (prefixWord ++ tailWord_99284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99295 : List Nat := [1, 1, 2, 3, 5, 1, 2, 7]
def baseStart_99295 : Nat := 118140960795 + 99295 * 2 ^ 59
def prefixEnd_99295 : Nat := 4983230072969 + 3 ^ 40 * 99295 * 2
def baseEnd_99295 : Nat := 3776745302836610485619

theorem tailTrace_99295 : CollatzResearch.WordTrace tailWord_99295 prefixEnd_99295 3776745302836610485619 := by
  unfold tailWord_99295
  simp only [CollatzResearch.WordTrace]
  refine ⟨3621586175278648080995339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2414390783519098720663559 3621586175278648080995339)
  ·
    refine ⟨5432379262917972121493009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3621586175278648080995339 5432379262917972121493009)
    ·
      refine ⟨4074284447188479091119757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5432379262917972121493009 4074284447188479091119757)
      ·
        refine ⟨1527856667695679659169909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4074284447188479091119757 1527856667695679659169909)
        ·
          refine ⟨143236562596469968047179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1527856667695679659169909 143236562596469968047179)
          ·
            refine ⟨214854843894704952070769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143236562596469968047179 214854843894704952070769)
            ·
              refine ⟨161141132921028714053077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214854843894704952070769 161141132921028714053077)
              ·
                refine ⟨3776745302836610485619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161141132921028714053077 3776745302836610485619)
                ·
                  rfl

theorem cell22_99295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 7].length) (baseStart_99295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99295 prefixEnd_99295 := by exact prefixLift 99295
  have htrace : WordTrace (prefixWord ++ tailWord_99295) baseStart_99295 baseEnd_99295 := by
    simpa [prefixWord, tailWord_99295, baseEnd_99295] using wordTrace_append hprefix tailTrace_99295
  have hstable : (prefixWord ++ tailWord_99295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99295).length < 2 ^ (prefixWord ++ tailWord_99295).sum := by decide
  have hdescent : baseEnd_99295 < baseStart_99295 := by decide
  rcases family_descends (prefixWord ++ tailWord_99295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99314 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_99314 : Nat := 118140960795 + 99314 * 2 ^ 59
def prefixEnd_99314 : Nat := 4983230072969 + 3 ^ 40 * 99314 * 2
def baseEnd_99314 : Nat := 33997211813819778145513

theorem tailTrace_99314 : CollatzResearch.WordTrace tailWord_99314 prefixEnd_99314 33997211813819778145513 := by
  unfold tailWord_99314
  simp only [CollatzResearch.WordTrace]
  refine ⟨905569790552453581484249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2414852774806542883957997 905569790552453581484249)
  ·
    refine ⟨679177342914340186113187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 905569790552453581484249 679177342914340186113187)
    ·
      refine ⟨1018766014371510279169781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679177342914340186113187 1018766014371510279169781)
      ·
        refine ⟨95509313847329088672167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1018766014371510279169781 95509313847329088672167)
        ·
          refine ⟨143263970770993633008251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95509313847329088672167 143263970770993633008251)
          ·
            refine ⟨214895956156490449512377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143263970770993633008251 214895956156490449512377)
            ·
              refine ⟨161171967117367837134283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214895956156490449512377 161171967117367837134283)
              ·
                refine ⟨241757950676051755701425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161171967117367837134283 241757950676051755701425)
                ·
                  refine ⟨181318463007038816776069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241757950676051755701425 181318463007038816776069)
                  ·
                    refine ⟨33997211813819778145513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181318463007038816776069 33997211813819778145513)
                    ·
                      rfl

theorem cell22_99314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_99314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99314 prefixEnd_99314 := by exact prefixLift 99314
  have htrace : WordTrace (prefixWord ++ tailWord_99314) baseStart_99314 baseEnd_99314 := by
    simpa [prefixWord, tailWord_99314, baseEnd_99314] using wordTrace_append hprefix tailTrace_99314
  have hstable : (prefixWord ++ tailWord_99314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99314).length < 2 ^ (prefixWord ++ tailWord_99314).sum := by decide
  have hdescent : baseEnd_99314 < baseStart_99314 := by decide
  rcases family_descends (prefixWord ++ tailWord_99314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99340 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_99340 : Nat := 118140960795 + 99340 * 2 ^ 59
def prefixEnd_99340 : Nat := 4983230072969 + 3 ^ 40 * 99340 * 2
def baseEnd_99340 : Nat := 11335370715054792331811

theorem tailTrace_99340 : CollatzResearch.WordTrace tailWord_99340 prefixEnd_99340 11335370715054792331811 := by
  unfold tailWord_99340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811613730057810383191737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2415484973410413844255649 1811613730057810383191737)
  ·
    refine ⟨1358710297543357787393803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1811613730057810383191737 1358710297543357787393803)
    ·
      refine ⟨2038065446315036681090705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358710297543357787393803 2038065446315036681090705)
      ·
        refine ⟨1528549084736277510818029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2038065446315036681090705 1528549084736277510818029)
        ·
          refine ⟨573205906776104066556761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1528549084736277510818029 573205906776104066556761)
          ·
            refine ⟨429904430082078049917571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573205906776104066556761 429904430082078049917571)
            ·
              refine ⟨644856645123117074876357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429904430082078049917571 644856645123117074876357)
              ·
                refine ⟨120910620960584451539317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644856645123117074876357 120910620960584451539317)
                ·
                  refine ⟨11335370715054792331811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120910620960584451539317 11335370715054792331811)
                  ·
                    rfl

theorem cell22_99340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_99340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99340 prefixEnd_99340 := by exact prefixLift 99340
  have htrace : WordTrace (prefixWord ++ tailWord_99340) baseStart_99340 baseEnd_99340 := by
    simpa [prefixWord, tailWord_99340, baseEnd_99340] using wordTrace_append hprefix tailTrace_99340
  have hstable : (prefixWord ++ tailWord_99340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99340).length < 2 ^ (prefixWord ++ tailWord_99340).sum := by decide
  have hdescent : baseEnd_99340 < baseStart_99340 := by decide
  rcases family_descends (prefixWord ++ tailWord_99340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99346 : List Nat := [3, 2, 5, 1, 1, 2, 1, 7]
def baseStart_99346 : Nat := 118140960795 + 99346 * 2 ^ 59
def prefixEnd_99346 : Nat := 4983230072969 + 3 ^ 40 * 99346 * 2
def baseEnd_99346 : Nat := 3778685118642484593935

theorem tailTrace_99346 : CollatzResearch.WordTrace tailWord_99346 prefixEnd_99346 3778685118642484593935 := by
  unfold tailWord_99346
  simp only [CollatzResearch.WordTrace]
  refine ⟨905861574523470947775473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2415630865395922527401261 905861574523470947775473)
  ·
    refine ⟨679396180892603210831605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 905861574523470947775473 679396180892603210831605)
    ·
      refine ⟨63693391958681551015463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 679396180892603210831605 63693391958681551015463)
      ·
        refine ⟨95540087938022326523195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63693391958681551015463 95540087938022326523195)
        ·
          refine ⟨143310131907033489784793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95540087938022326523195 143310131907033489784793)
          ·
            refine ⟨107482598930275117338595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143310131907033489784793 107482598930275117338595)
            ·
              refine ⟨161223898395412676007893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107482598930275117338595 161223898395412676007893)
              ·
                refine ⟨3778685118642484593935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161223898395412676007893 3778685118642484593935)
                ·
                  rfl

theorem cell22_99346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_99346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99346 prefixEnd_99346 := by exact prefixLift 99346
  have htrace : WordTrace (prefixWord ++ tailWord_99346) baseStart_99346 baseEnd_99346 := by
    simpa [prefixWord, tailWord_99346, baseEnd_99346] using wordTrace_append hprefix tailTrace_99346
  have hstable : (prefixWord ++ tailWord_99346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99346).length < 2 ^ (prefixWord ++ tailWord_99346).sum := by decide
  have hdescent : baseEnd_99346 < baseStart_99346 := by decide
  rcases family_descends (prefixWord ++ tailWord_99346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99402 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_99402 : Nat := 118140960795 + 99402 * 2 ^ 59
def prefixEnd_99402 : Nat := 4983230072969 + 3 ^ 40 * 99402 * 2
def baseEnd_99402 : Nat := 11342445337405627315081

theorem tailTrace_99402 : CollatzResearch.WordTrace tailWord_99402 prefixEnd_99402 11342445337405627315081 := by
  unfold tailWord_99402
  simp only [CollatzResearch.WordTrace]
  refine ⟨906372196472751338785115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2416992523927336903426973 906372196472751338785115)
  ·
    refine ⟨1359558294709127008177673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 906372196472751338785115 1359558294709127008177673)
    ·
      refine ⟨1019668721031845256133255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1359558294709127008177673 1019668721031845256133255)
      ·
        refine ⟨1529503081547767884199883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019668721031845256133255 1529503081547767884199883)
        ·
          refine ⟨2294254622321651826299825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529503081547767884199883 2294254622321651826299825)
          ·
            refine ⟨1720690966741238869724869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2294254622321651826299825 1720690966741238869724869)
            ·
              refine ⟨322629556263982288073413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1720690966741238869724869 322629556263982288073413)
              ·
                refine ⟨60493041799496679013765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322629556263982288073413 60493041799496679013765)
                ·
                  refine ⟨11342445337405627315081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60493041799496679013765 11342445337405627315081)
                  ·
                    rfl

theorem cell22_99402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_99402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99402 prefixEnd_99402 := by exact prefixLift 99402
  have htrace : WordTrace (prefixWord ++ tailWord_99402) baseStart_99402 baseEnd_99402 := by
    simpa [prefixWord, tailWord_99402, baseEnd_99402] using wordTrace_append hprefix tailTrace_99402
  have hstable : (prefixWord ++ tailWord_99402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99402).length < 2 ^ (prefixWord ++ tailWord_99402).sum := by decide
  have hdescent : baseEnd_99402 < baseStart_99402 := by decide
  rcases family_descends (prefixWord ++ tailWord_99402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99421 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_99421 : Nat := 118140960795 + 99421 * 2 ^ 59
def prefixEnd_99421 : Nat := 4983230072969 + 3 ^ 40 * 99421 * 2
def baseEnd_99421 : Nat := 34033840100507165720185

theorem tailTrace_99421 : CollatzResearch.WordTrace tailWord_99421 prefixEnd_99421 34033840100507165720185 := by
  unfold tailWord_99421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626181772822171600082117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2417454515214781066721411 3626181772822171600082117)
  ·
    refine ⟨679909082404157175015397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3626181772822171600082117 679909082404157175015397)
    ·
      refine ⟨127482952950779470315387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 679909082404157175015397 127482952950779470315387)
      ·
        refine ⟨191224429426169205473081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127482952950779470315387 191224429426169205473081)
        ·
          refine ⟨143418322069626904104811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191224429426169205473081 143418322069626904104811)
          ·
            refine ⟨215127483104440356157217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143418322069626904104811 215127483104440356157217)
            ·
              refine ⟨161345612328330267117913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215127483104440356157217 161345612328330267117913)
              ·
                refine ⟨121009209246247700338435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161345612328330267117913 121009209246247700338435)
                ·
                  refine ⟨181513813869371550507653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121009209246247700338435 181513813869371550507653)
                  ·
                    refine ⟨34033840100507165720185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181513813869371550507653 34033840100507165720185)
                    ·
                      rfl

theorem cell22_99421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_99421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99421 prefixEnd_99421 := by exact prefixLift 99421
  have htrace : WordTrace (prefixWord ++ tailWord_99421) baseStart_99421 baseEnd_99421 := by
    simpa [prefixWord, tailWord_99421, baseEnd_99421] using wordTrace_append hprefix tailTrace_99421
  have hstable : (prefixWord ++ tailWord_99421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99421).length < 2 ^ (prefixWord ++ tailWord_99421).sum := by decide
  have hdescent : baseEnd_99421 < baseStart_99421 := by decide
  rcases family_descends (prefixWord ++ tailWord_99421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99513 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 1, 3]
def baseStart_99513 : Nat := 118140960795 + 99513 * 2 ^ 59
def prefixEnd_99513 : Nat := 4983230072969 + 3 ^ 40 * 99513 * 2
def baseEnd_99513 : Nat := 34065333580649592419903

theorem tailTrace_99513 : CollatzResearch.WordTrace tailWord_99513 prefixEnd_99513 34065333580649592419903 := by
  unfold tailWord_99513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629537288488871312431193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2419691525659247541620795 3629537288488871312431193)
  ·
    refine ⟨2722152966366653484323395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3629537288488871312431193 2722152966366653484323395)
    ·
      refine ⟨4083229449549980226485093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722152966366653484323395 4083229449549980226485093)
      ·
        refine ⟨765605521790621292465955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4083229449549980226485093 765605521790621292465955)
        ·
          refine ⟨1148408282685931938698933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765605521790621292465955 1148408282685931938698933)
          ·
            refine ⟨107663276501806119253025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1148408282685931938698933 107663276501806119253025)
            ·
              refine ⟨80747457376354589439769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107663276501806119253025 80747457376354589439769)
              ·
                refine ⟨60560593032265942079827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80747457376354589439769 60560593032265942079827)
                ·
                  refine ⟨90840889548398913119741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60560593032265942079827 90840889548398913119741)
                  ·
                    refine ⟨34065333580649592419903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90840889548398913119741 34065333580649592419903)
                    ·
                      rfl

theorem cell22_99513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_99513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99513 prefixEnd_99513 := by exact prefixLift 99513
  have htrace : WordTrace (prefixWord ++ tailWord_99513) baseStart_99513 baseEnd_99513 := by
    simpa [prefixWord, tailWord_99513, baseEnd_99513] using wordTrace_append hprefix tailTrace_99513
  have hstable : (prefixWord ++ tailWord_99513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99513).length < 2 ^ (prefixWord ++ tailWord_99513).sum := by decide
  have hdescent : baseEnd_99513 < baseStart_99513 := by decide
  rcases family_descends (prefixWord ++ tailWord_99513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99524 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_99524 : Nat := 118140960795 + 99524 * 2 ^ 59
def prefixEnd_99524 : Nat := 4983230072969 + 3 ^ 40 * 99524 * 2
def baseEnd_99524 : Nat := 34069099105449230394869

theorem tailTrace_99524 : CollatzResearch.WordTrace tailWord_99524 prefixEnd_99524 34069099105449230394869 := by
  unfold tailWord_99524
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814969245724510095540813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2419958994299346794054417 1814969245724510095540813)
  ·
    refine ⟨680613467146691285827805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1814969245724510095540813 680613467146691285827805)
    ·
      refine ⟨255230050180009232185427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 680613467146691285827805 255230050180009232185427)
      ·
        refine ⟨382845075270013848278141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255230050180009232185427 382845075270013848278141)
        ·
          refine ⟨143566903226255193104303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382845075270013848278141 143566903226255193104303)
          ·
            refine ⟨215350354839382789656455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143566903226255193104303 215350354839382789656455)
            ·
              refine ⟨323025532259074184484683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215350354839382789656455 323025532259074184484683)
              ·
                refine ⟨484538298388611276727025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323025532259074184484683 484538298388611276727025)
                ·
                  refine ⟨363403723791458457545269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484538298388611276727025 363403723791458457545269)
                  ·
                    refine ⟨34069099105449230394869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 363403723791458457545269 34069099105449230394869)
                    ·
                      rfl

theorem cell22_99524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_99524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99524 prefixEnd_99524 := by exact prefixLift 99524
  have htrace : WordTrace (prefixWord ++ tailWord_99524) baseStart_99524 baseEnd_99524 := by
    simpa [prefixWord, tailWord_99524, baseEnd_99524] using wordTrace_append hprefix tailTrace_99524
  have hstable : (prefixWord ++ tailWord_99524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99524).length < 2 ^ (prefixWord ++ tailWord_99524).sum := by decide
  have hdescent : baseEnd_99524 < baseStart_99524 := by decide
  rcases family_descends (prefixWord ++ tailWord_99524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99552 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_99552 : Nat := 118140960795 + 99552 * 2 ^ 59
def prefixEnd_99552 : Nat := 4983230072969 + 3 ^ 40 * 99552 * 2
def baseEnd_99552 : Nat := 34078684077666490694783

theorem tailTrace_99552 : CollatzResearch.WordTrace tailWord_99552 prefixEnd_99552 34078684077666490694783 := by
  unfold tailWord_99552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815479867673790486550455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2420639823565053982067273 1815479867673790486550455)
  ·
    refine ⟨2723219801510685729825683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815479867673790486550455 2723219801510685729825683)
    ·
      refine ⟨4084829702266028594738525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723219801510685729825683 4084829702266028594738525)
      ·
        refine ⟨1531811138349760723026947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4084829702266028594738525 1531811138349760723026947)
        ·
          refine ⟨2297716707524641084540421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531811138349760723026947 2297716707524641084540421)
          ·
            refine ⟨430821882660870203351329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2297716707524641084540421 430821882660870203351329)
            ·
              refine ⟨323116411995652652513497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430821882660870203351329 323116411995652652513497)
              ·
                refine ⟨242337308996739489385123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323116411995652652513497 242337308996739489385123)
                ·
                  refine ⟨363505963495109234077685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 242337308996739489385123 363505963495109234077685)
                  ·
                    refine ⟨34078684077666490694783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 363505963495109234077685 34078684077666490694783)
                    ·
                      rfl

theorem cell22_99552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_99552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99552 prefixEnd_99552 := by exact prefixLift 99552
  have htrace : WordTrace (prefixWord ++ tailWord_99552) baseStart_99552 baseEnd_99552 := by
    simpa [prefixWord, tailWord_99552, baseEnd_99552] using wordTrace_append hprefix tailTrace_99552
  have hstable : (prefixWord ++ tailWord_99552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99552).length < 2 ^ (prefixWord ++ tailWord_99552).sum := by decide
  have hdescent : baseEnd_99552 < baseStart_99552 := by decide
  rcases family_descends (prefixWord ++ tailWord_99552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99642 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_99642 : Nat := 118140960795 + 99642 * 2 ^ 59
def prefixEnd_99642 : Nat := 4983230072969 + 3 ^ 40 * 99642 * 2
def baseEnd_99642 : Nat := 34109492916936255944507

theorem tailTrace_99642 : CollatzResearch.WordTrace tailWord_99642 prefixEnd_99642 34109492916936255944507 := by
  unfold tailWord_99642
  simp only [CollatzResearch.WordTrace]
  refine ⟨908560576255381585969295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2422828203347684229251453 908560576255381585969295)
  ·
    refine ⟨1362840864383072378953943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 908560576255381585969295 1362840864383072378953943)
    ·
      refine ⟨2044261296574608568430915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362840864383072378953943 2044261296574608568430915)
      ·
        refine ⟨3066391944861912852646373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044261296574608568430915 3066391944861912852646373)
        ·
          refine ⟨574948489661608659871195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3066391944861912852646373 574948489661608659871195)
          ·
            refine ⟨862422734492412989806793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574948489661608659871195 862422734492412989806793)
            ·
              refine ⟨646817050869309742355095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862422734492412989806793 646817050869309742355095)
              ·
                refine ⟨970225576303964613532643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646817050869309742355095 970225576303964613532643)
                ·
                  refine ⟨1455338364455946920298965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970225576303964613532643 1455338364455946920298965)
                  ·
                    refine ⟨34109492916936255944507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1455338364455946920298965 34109492916936255944507)
                    ·
                      rfl

theorem cell22_99642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_99642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99642 prefixEnd_99642 := by exact prefixLift 99642
  have htrace : WordTrace (prefixWord ++ tailWord_99642) baseStart_99642 baseEnd_99642 := by
    simpa [prefixWord, tailWord_99642, baseEnd_99642] using wordTrace_append hprefix tailTrace_99642
  have hstable : (prefixWord ++ tailWord_99642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99642).length < 2 ^ (prefixWord ++ tailWord_99642).sum := by decide
  have hdescent : baseEnd_99642 < baseStart_99642 := by decide
  rcases family_descends (prefixWord ++ tailWord_99642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99644 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_99644 : Nat := 118140960795 + 99644 * 2 ^ 59
def prefixEnd_99644 : Nat := 4983230072969 + 3 ^ 40 * 99644 * 2
def baseEnd_99644 : Nat := 11370059185936305798167

theorem tailTrace_99644 : CollatzResearch.WordTrace tailWord_99644 prefixEnd_99644 11370059185936305798167 := by
  unfold tailWord_99644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817157625507140342724993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2422876834009520456966657 1817157625507140342724993)
  ·
    refine ⟨1362868219130355257043745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1817157625507140342724993 1362868219130355257043745)
    ·
      refine ⟨1022151164347766442782809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1362868219130355257043745 1022151164347766442782809)
      ·
        refine ⟨766613373260824832087107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022151164347766442782809 766613373260824832087107)
        ·
          refine ⟨1149920059891237248130661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766613373260824832087107 1149920059891237248130661)
          ·
            refine ⟨215610011229606984024499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1149920059891237248130661 215610011229606984024499)
            ·
              refine ⟨323415016844410476036749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215610011229606984024499 323415016844410476036749)
              ·
                refine ⟨121280631316653928513781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323415016844410476036749 121280631316653928513781)
                ·
                  refine ⟨11370059185936305798167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121280631316653928513781 11370059185936305798167)
                  ·
                    rfl

theorem cell22_99644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_99644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99644 prefixEnd_99644 := by exact prefixLift 99644
  have htrace : WordTrace (prefixWord ++ tailWord_99644) baseStart_99644 baseEnd_99644 := by
    simpa [prefixWord, tailWord_99644, baseEnd_99644] using wordTrace_append hprefix tailTrace_99644
  have hstable : (prefixWord ++ tailWord_99644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99644).length < 2 ^ (prefixWord ++ tailWord_99644).sum := by decide
  have hdescent : baseEnd_99644 < baseStart_99644 := by decide
  rcases family_descends (prefixWord ++ tailWord_99644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99674 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_99674 : Nat := 118140960795 + 99674 * 2 ^ 59
def prefixEnd_99674 : Nat := 4983230072969 + 3 ^ 40 * 99674 * 2
def baseEnd_99674 : Nat := 34120447170898839144409

theorem tailTrace_99674 : CollatzResearch.WordTrace tailWord_99674 prefixEnd_99674 34120447170898839144409 := by
  unfold tailWord_99674
  simp only [CollatzResearch.WordTrace]
  refine ⟨908852360226398952260519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2423606293937063872694717 908852360226398952260519)
  ·
    refine ⟨1363278540339598428390779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 908852360226398952260519 1363278540339598428390779)
    ·
      refine ⟨2044917810509397642586169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363278540339598428390779 2044917810509397642586169)
      ·
        refine ⟨1533688357882048231939627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2044917810509397642586169 1533688357882048231939627)
        ·
          refine ⟨2300532536823072347909441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533688357882048231939627 2300532536823072347909441)
          ·
            refine ⟨1725399402617304260932081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300532536823072347909441 1725399402617304260932081)
            ·
              refine ⟨1294049551962978195699061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725399402617304260932081 1294049551962978195699061)
              ·
                refine ⟨121317145496529205846787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1294049551962978195699061 121317145496529205846787)
                ·
                  refine ⟨181975718244793808770181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121317145496529205846787 181975718244793808770181)
                  ·
                    refine ⟨34120447170898839144409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181975718244793808770181 34120447170898839144409)
                    ·
                      rfl

theorem cell22_99674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_99674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99674 prefixEnd_99674 := by exact prefixLift 99674
  have htrace : WordTrace (prefixWord ++ tailWord_99674) baseStart_99674 baseEnd_99674 := by
    simpa [prefixWord, tailWord_99674, baseEnd_99674] using wordTrace_append hprefix tailTrace_99674
  have hstable : (prefixWord ++ tailWord_99674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99674).length < 2 ^ (prefixWord ++ tailWord_99674).sum := by decide
  have hdescent : baseEnd_99674 < baseStart_99674 := by decide
  rcases family_descends (prefixWord ++ tailWord_99674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99717 : List Nat := [1, 3, 1, 1, 3, 1, 2, 10]
def baseStart_99717 : Nat := 118140960795 + 99717 * 2 ^ 59
def prefixEnd_99717 : Nat := 4983230072969 + 3 ^ 40 * 99717 * 2
def baseEnd_99717 : Nat := 3792796327740117813253

theorem tailTrace_99717 : CollatzResearch.WordTrace tailWord_99717 prefixEnd_99717 3792796327740117813253 := by
  unfold tailWord_99717
  simp only [CollatzResearch.WordTrace]
  refine ⟨3636977779749814152857405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2424651853166542768571603 3636977779749814152857405)
  ·
    refine ⟨1363866667406180307321527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3636977779749814152857405 1363866667406180307321527)
    ·
      refine ⟨2045800001109270460982291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363866667406180307321527 2045800001109270460982291)
      ·
        refine ⟨3068700001663905691473437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045800001109270460982291 3068700001663905691473437)
        ·
          refine ⟨1150762500623964634302539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3068700001663905691473437 1150762500623964634302539)
          ·
            refine ⟨1726143750935946951453809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150762500623964634302539 1726143750935946951453809)
            ·
              refine ⟨1294607813201960213590357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726143750935946951453809 1294607813201960213590357)
              ·
                refine ⟨3792796327740117813253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1294607813201960213590357 3792796327740117813253)
                ·
                  rfl

theorem cell22_99717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 10].length) (baseStart_99717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99717 prefixEnd_99717 := by exact prefixLift 99717
  have htrace : WordTrace (prefixWord ++ tailWord_99717) baseStart_99717 baseEnd_99717 := by
    simpa [prefixWord, tailWord_99717, baseEnd_99717] using wordTrace_append hprefix tailTrace_99717
  have hstable : (prefixWord ++ tailWord_99717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99717).length < 2 ^ (prefixWord ++ tailWord_99717).sum := by decide
  have hdescent : baseEnd_99717 < baseStart_99717 := by decide
  rcases family_descends (prefixWord ++ tailWord_99717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99719 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 1, 6]
def baseStart_99719 : Nat := 118140960795 + 99719 * 2 ^ 59
def prefixEnd_99719 : Nat := 4983230072969 + 3 ^ 40 * 99719 * 2
def baseEnd_99719 : Nat := 34135851590533721769271

theorem tailTrace_99719 : CollatzResearch.WordTrace tailWord_99719 prefixEnd_99719 34135851590533721769271 := by
  unfold tailWord_99719
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637050725742568494430211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2424700483828378996286807 3637050725742568494430211)
  ·
    refine ⟨5455576088613852741645317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3637050725742568494430211 5455576088613852741645317)
    ·
      refine ⟨1022920516615097389058497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5455576088613852741645317 1022920516615097389058497)
      ·
        refine ⟨767190387461323041793873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022920516615097389058497 767190387461323041793873)
        ·
          refine ⟨575392790595992281345405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767190387461323041793873 575392790595992281345405)
          ·
            refine ⟨215772296473497105504527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575392790595992281345405 215772296473497105504527)
            ·
              refine ⟨323658444710245658256791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215772296473497105504527 323658444710245658256791)
              ·
                refine ⟨485487667065368487385187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323658444710245658256791 485487667065368487385187)
                ·
                  refine ⟨728231500598052731077781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485487667065368487385187 728231500598052731077781)
                  ·
                    refine ⟨34135851590533721769271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 728231500598052731077781 34135851590533721769271)
                    ·
                      rfl

theorem cell22_99719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_99719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99719 prefixEnd_99719 := by exact prefixLift 99719
  have htrace : WordTrace (prefixWord ++ tailWord_99719) baseStart_99719 baseEnd_99719 := by
    simpa [prefixWord, tailWord_99719, baseEnd_99719] using wordTrace_append hprefix tailTrace_99719
  have hstable : (prefixWord ++ tailWord_99719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99719).length < 2 ^ (prefixWord ++ tailWord_99719).sum := by decide
  have hdescent : baseEnd_99719 < baseStart_99719 := by decide
  rcases family_descends (prefixWord ++ tailWord_99719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99813 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 5]
def baseStart_99813 : Nat := 118140960795 + 99813 * 2 ^ 59
def prefixEnd_99813 : Nat := 4983230072969 + 3 ^ 40 * 99813 * 2
def baseEnd_99813 : Nat := 11389343237182936639661

theorem tailTrace_99813 : CollatzResearch.WordTrace tailWord_99813 prefixEnd_99813 11389343237182936639661 := by
  unfold tailWord_99813
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640479187402022548352093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2426986124934681698901395 3640479187402022548352093)
  ·
    refine ⟨1365179695275758455632035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3640479187402022548352093 1365179695275758455632035)
    ·
      refine ⟨2047769542913637683448053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365179695275758455632035 2047769542913637683448053)
      ·
        refine ⟨191978394648153532823255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2047769542913637683448053 191978394648153532823255)
        ·
          refine ⟨287967591972230299234883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191978394648153532823255 287967591972230299234883)
          ·
            refine ⟨431951387958345448852325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287967591972230299234883 431951387958345448852325)
            ·
              refine ⟨80990885242189771659811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431951387958345448852325 80990885242189771659811)
              ·
                refine ⟨121486327863284657489717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80990885242189771659811 121486327863284657489717)
                ·
                  refine ⟨11389343237182936639661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121486327863284657489717 11389343237182936639661)
                  ·
                    rfl

theorem cell22_99813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_99813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99813 prefixEnd_99813 := by exact prefixLift 99813
  have htrace : WordTrace (prefixWord ++ tailWord_99813) baseStart_99813 baseEnd_99813 := by
    simpa [prefixWord, tailWord_99813, baseEnd_99813] using wordTrace_append hprefix tailTrace_99813
  have hstable : (prefixWord ++ tailWord_99813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99813).length < 2 ^ (prefixWord ++ tailWord_99813).sum := by decide
  have hdescent : baseEnd_99813 < baseStart_99813 := by decide
  rcases family_descends (prefixWord ++ tailWord_99813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99873 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_99873 : Nat := 118140960795 + 99873 * 2 ^ 59
def prefixEnd_99873 : Nat := 4983230072969 + 3 ^ 40 * 99873 * 2
def baseEnd_99873 : Nat := 34188568937728653418799

theorem tailTrace_99873 : CollatzResearch.WordTrace tailWord_99873 prefixEnd_99873 34188568937728653418799 := by
  unfold tailWord_99873
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642667567184652795536273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2428445044789768530357515 3642667567184652795536273)
  ·
    refine ⟨2732000675388489596652205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3642667567184652795536273 2732000675388489596652205)
    ·
      refine ⟨1024500253270683598744577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2732000675388489596652205 1024500253270683598744577)
      ·
        refine ⟨768375189953012699058433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024500253270683598744577 768375189953012699058433)
        ·
          refine ⟨576281392464759524293825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768375189953012699058433 576281392464759524293825)
          ·
            refine ⟨432211044348569643220369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576281392464759524293825 432211044348569643220369)
            ·
              refine ⟨324158283261427232415277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432211044348569643220369 324158283261427232415277)
              ·
                refine ⟨121559356223035212155729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 324158283261427232415277 121559356223035212155729)
                ·
                  refine ⟨91169517167276409116797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121559356223035212155729 91169517167276409116797)
                  ·
                    refine ⟨34188568937728653418799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91169517167276409116797 34188568937728653418799)
                    ·
                      rfl

theorem cell22_99873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_99873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99873 prefixEnd_99873 := by exact prefixLift 99873
  have htrace : WordTrace (prefixWord ++ tailWord_99873) baseStart_99873 baseEnd_99873 := by
    simpa [prefixWord, tailWord_99873, baseEnd_99873] using wordTrace_append hprefix tailTrace_99873
  have hstable : (prefixWord ++ tailWord_99873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99873).length < 2 ^ (prefixWord ++ tailWord_99873).sum := by decide
  have hdescent : baseEnd_99873 < baseStart_99873 := by decide
  rcases family_descends (prefixWord ++ tailWord_99873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99894 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_99894 : Nat := 118140960795 + 99894 * 2 ^ 59
def prefixEnd_99894 : Nat := 4983230072969 + 3 ^ 40 * 99894 * 2
def baseEnd_99894 : Nat := 34195757666891598643735

theorem tailTrace_99894 : CollatzResearch.WordTrace tailWord_99894 prefixEnd_99894 34195757666891598643735 := by
  unfold tailWord_99894
  simp only [CollatzResearch.WordTrace]
  refine ⟨227714593756785836378171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2428955666739048921367157 227714593756785836378171)
  ·
    refine ⟨341571890635178754567257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227714593756785836378171 341571890635178754567257)
    ·
      refine ⟨256178917976384065925443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341571890635178754567257 256178917976384065925443)
      ·
        refine ⟨384268376964576098888165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256178917976384065925443 384268376964576098888165)
        ·
          refine ⟨72050320680858018541531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384268376964576098888165 72050320680858018541531)
          ·
            refine ⟨108075481021287027812297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72050320680858018541531 108075481021287027812297)
            ·
              refine ⟨81056610765965270859223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108075481021287027812297 81056610765965270859223)
              ·
                refine ⟨121584916148947906288835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81056610765965270859223 121584916148947906288835)
                ·
                  refine ⟨182377374223421859433253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121584916148947906288835 182377374223421859433253)
                  ·
                    refine ⟨34195757666891598643735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 182377374223421859433253 34195757666891598643735)
                    ·
                      rfl

theorem cell22_99894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_99894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99894 prefixEnd_99894 := by exact prefixLift 99894
  have htrace : WordTrace (prefixWord ++ tailWord_99894) baseStart_99894 baseEnd_99894 := by
    simpa [prefixWord, tailWord_99894, baseEnd_99894] using wordTrace_append hprefix tailTrace_99894
  have hstable : (prefixWord ++ tailWord_99894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99894).length < 2 ^ (prefixWord ++ tailWord_99894).sum := by decide
  have hdescent : baseEnd_99894 < baseStart_99894 := by decide
  rcases family_descends (prefixWord ++ tailWord_99894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_99952 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 1, 3]
def baseStart_99952 : Nat := 118140960795 + 99952 * 2 ^ 59
def prefixEnd_99952 : Nat := 4983230072969 + 3 ^ 40 * 99952 * 2
def baseEnd_99952 : Nat := 34215612252198780693557

theorem tailTrace_99952 : CollatzResearch.WordTrace tailWord_99952 prefixEnd_99952 34215612252198780693557 := by
  unfold tailWord_99952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822774466949224643831055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2430365955932299525108073 1822774466949224643831055)
  ·
    refine ⟨2734161700423836965746583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822774466949224643831055 2734161700423836965746583)
    ·
      refine ⟨4101242550635755448619875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734161700423836965746583 4101242550635755448619875)
      ·
        refine ⟨6151863825953633172929813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101242550635755448619875 6151863825953633172929813)
        ·
          refine ⟨288368616841576554981085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6151863825953633172929813 288368616841576554981085)
          ·
            refine ⟨108138231315591208117907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288368616841576554981085 108138231315591208117907)
            ·
              refine ⟨162207346973386812176861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108138231315591208117907 162207346973386812176861)
              ·
                refine ⟨60827755115020054566323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162207346973386812176861 60827755115020054566323)
                ·
                  refine ⟨91241632672530081849485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60827755115020054566323 91241632672530081849485)
                  ·
                    refine ⟨34215612252198780693557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91241632672530081849485 34215612252198780693557)
                    ·
                      rfl

theorem cell22_99952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_99952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_99952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_99952 prefixEnd_99952 := by exact prefixLift 99952
  have htrace : WordTrace (prefixWord ++ tailWord_99952) baseStart_99952 baseEnd_99952 := by
    simpa [prefixWord, tailWord_99952, baseEnd_99952] using wordTrace_append hprefix tailTrace_99952
  have hstable : (prefixWord ++ tailWord_99952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_99952).length < 2 ^ (prefixWord ++ tailWord_99952).sum := by decide
  have hdescent : baseEnd_99952 < baseStart_99952 := by decide
  rcases family_descends (prefixWord ++ tailWord_99952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100021 : List Nat := [1, 3, 3, 3, 12]
def baseStart_100021 : Nat := 118140960795 + 100021 * 2 ^ 59
def prefixEnd_100021 : Nat := 4983230072969 + 3 ^ 40 * 100021 * 2
def baseEnd_100021 : Nat := 140902190791381072915

theorem tailTrace_100021 : CollatzResearch.WordTrace tailWord_100021 prefixEnd_100021 140902190791381072915 := by
  unfold tailWord_100021
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648065570648474071923917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2432043713765649381282611 3648065570648474071923917)
  ·
    refine ⟨1368024588993177776971469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3648065570648474071923917 1368024588993177776971469)
    ·
      refine ⟨513009220872441666364301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1368024588993177776971469 513009220872441666364301)
      ·
        refine ⟨192378457827165624886613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513009220872441666364301 192378457827165624886613)
        ·
          refine ⟨140902190791381072915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 192378457827165624886613 140902190791381072915)
          ·
            rfl

theorem cell22_100021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 12].length) (baseStart_100021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100021 prefixEnd_100021 := by exact prefixLift 100021
  have htrace : WordTrace (prefixWord ++ tailWord_100021) baseStart_100021 baseEnd_100021 := by
    simpa [prefixWord, tailWord_100021, baseEnd_100021] using wordTrace_append hprefix tailTrace_100021
  have hstable : (prefixWord ++ tailWord_100021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100021).length < 2 ^ (prefixWord ++ tailWord_100021).sum := by decide
  have hdescent : baseEnd_100021 < baseStart_100021 := by decide
  rcases family_descends (prefixWord ++ tailWord_100021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100023 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 2, 4]
def baseStart_100023 : Nat := 118140960795 + 100023 * 2 ^ 59
def prefixEnd_100023 : Nat := 4983230072969 + 3 ^ 40 * 100023 * 2
def baseEnd_100023 : Nat := 34239917003178262168339

theorem tailTrace_100023 : CollatzResearch.WordTrace tailWord_100023 prefixEnd_100023 34239917003178262168339 := by
  unfold tailWord_100023
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648138516641228413496723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2432092344427485608997815 3648138516641228413496723)
  ·
    refine ⟨5472207774961842620245085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648138516641228413496723 5472207774961842620245085)
    ·
      refine ⟨2052077915610690982591907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5472207774961842620245085 2052077915610690982591907)
      ·
        refine ⟨3078116873416036473887861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052077915610690982591907 3078116873416036473887861)
        ·
          refine ⟨288573456882753419426987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3078116873416036473887861 288573456882753419426987)
          ·
            refine ⟨432860185324130129140481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288573456882753419426987 432860185324130129140481)
            ·
              refine ⟨324645138993097596855361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432860185324130129140481 324645138993097596855361)
              ·
                refine ⟨243483854244823197641521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324645138993097596855361 243483854244823197641521)
                ·
                  refine ⟨182612890683617398231141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243483854244823197641521 182612890683617398231141)
                  ·
                    refine ⟨34239917003178262168339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 182612890683617398231141 34239917003178262168339)
                    ·
                      rfl

theorem cell22_100023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_100023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100023 prefixEnd_100023 := by exact prefixLift 100023
  have htrace : WordTrace (prefixWord ++ tailWord_100023) baseStart_100023 baseEnd_100023 := by
    simpa [prefixWord, tailWord_100023, baseEnd_100023] using wordTrace_append hprefix tailTrace_100023
  have hstable : (prefixWord ++ tailWord_100023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100023).length < 2 ^ (prefixWord ++ tailWord_100023).sum := by decide
  have hdescent : baseEnd_100023 < baseStart_100023 := by decide
  rcases family_descends (prefixWord ++ tailWord_100023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100083 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 5]
def baseStart_100083 : Nat := 118140960795 + 100083 * 2 ^ 59
def prefixEnd_100083 : Nat := 4983230072969 + 3 ^ 40 * 100083 * 2
def baseEnd_100083 : Nat := 11420152076452701889385

theorem tailTrace_100083 : CollatzResearch.WordTrace tailWord_100083 prefixEnd_100083 11420152076452701889385 := by
  unfold tailWord_100083
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650326896423858660680903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2433551264282572440453935 3650326896423858660680903)
  ·
    refine ⟨5475490344635787991021355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3650326896423858660680903 5475490344635787991021355)
    ·
      refine ⟨8213235516953681986532033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5475490344635787991021355 8213235516953681986532033)
      ·
        refine ⟨6159926637715261489899025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8213235516953681986532033 6159926637715261489899025)
        ·
          refine ⟨4619944978286446117424269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6159926637715261489899025 4619944978286446117424269)
          ·
            refine ⟨1732479366857417294034101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4619944978286446117424269 1732479366857417294034101)
            ·
              refine ⟨162419940642882871315697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1732479366857417294034101 162419940642882871315697)
              ·
                refine ⟨121814955482162153486773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162419940642882871315697 121814955482162153486773)
                ·
                  refine ⟨11420152076452701889385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121814955482162153486773 11420152076452701889385)
                  ·
                    rfl

theorem cell22_100083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 5].length) (baseStart_100083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100083 prefixEnd_100083 := by exact prefixLift 100083
  have htrace : WordTrace (prefixWord ++ tailWord_100083) baseStart_100083 baseEnd_100083 := by
    simpa [prefixWord, tailWord_100083, baseEnd_100083] using wordTrace_append hprefix tailTrace_100083
  have hstable : (prefixWord ++ tailWord_100083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100083).length < 2 ^ (prefixWord ++ tailWord_100083).sum := by decide
  have hdescent : baseEnd_100083 < baseStart_100083 := by decide
  rcases family_descends (prefixWord ++ tailWord_100083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100111 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 8]
def baseStart_100111 : Nat := 118140960795 + 100111 * 2 ^ 59
def prefixEnd_100111 : Nat := 4983230072969 + 3 ^ 40 * 100111 * 2
def baseEnd_100111 : Nat := 11423347067191788656023

theorem tailTrace_100111 : CollatzResearch.WordTrace tailWord_100111 prefixEnd_100111 11423347067191788656023 := by
  unfold tailWord_100111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651348140322419442700187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2434232093548279628466791 3651348140322419442700187)
  ·
    refine ⟨5477022210483629164050281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3651348140322419442700187 5477022210483629164050281)
    ·
      refine ⟨4107766657862721873037711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5477022210483629164050281 4107766657862721873037711)
      ·
        refine ⟨6161649986794082809556567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107766657862721873037711 6161649986794082809556567)
        ·
          refine ⟨9242474980191124214334851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161649986794082809556567 9242474980191124214334851)
          ·
            refine ⟨13863712470286686321502277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242474980191124214334851 13863712470286686321502277)
            ·
              refine ⟨2599446088178753685281677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13863712470286686321502277 2599446088178753685281677)
              ·
                refine ⟨974792283067032631980629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2599446088178753685281677 974792283067032631980629)
                ·
                  refine ⟨11423347067191788656023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 974792283067032631980629 11423347067191788656023)
                  ·
                    rfl

theorem cell22_100111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 8].length) (baseStart_100111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100111 prefixEnd_100111 := by exact prefixLift 100111
  have htrace : WordTrace (prefixWord ++ tailWord_100111) baseStart_100111 baseEnd_100111 := by
    simpa [prefixWord, tailWord_100111, baseEnd_100111] using wordTrace_append hprefix tailTrace_100111
  have hstable : (prefixWord ++ tailWord_100111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100111).length < 2 ^ (prefixWord ++ tailWord_100111).sum := by decide
  have hdescent : baseEnd_100111 < baseStart_100111 := by decide
  rcases family_descends (prefixWord ++ tailWord_100111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100130 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_100130 : Nat := 118140960795 + 100130 * 2 ^ 59
def prefixEnd_100130 : Nat := 4983230072969 + 3 ^ 40 * 100130 * 2
def baseEnd_100130 : Nat := 34276545289865649743011

theorem tailTrace_100130 : CollatzResearch.WordTrace tailWord_100130 prefixEnd_100130 34276545289865649743011 := by
  unfold tailWord_100130
  simp only [CollatzResearch.WordTrace]
  refine ⟨913010281813396421910461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2434694084835723791761229 913010281813396421910461)
  ·
    refine ⟨342378855680023658216423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 913010281813396421910461 342378855680023658216423)
    ·
      refine ⟨513568283520035487324635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342378855680023658216423 513568283520035487324635)
      ·
        refine ⟨770352425280053230986953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513568283520035487324635 770352425280053230986953)
        ·
          refine ⟨577764318960039923240215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770352425280053230986953 577764318960039923240215)
          ·
            refine ⟨866646478440059884860323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577764318960039923240215 866646478440059884860323)
            ·
              refine ⟨1299969717660089827290485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866646478440059884860323 1299969717660089827290485)
              ·
                refine ⟨121872161030633421308483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1299969717660089827290485 121872161030633421308483)
                ·
                  refine ⟨182808241545950131962725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121872161030633421308483 182808241545950131962725)
                  ·
                    refine ⟨34276545289865649743011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 182808241545950131962725 34276545289865649743011)
                    ·
                      rfl

theorem cell22_100130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_100130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100130 prefixEnd_100130 := by exact prefixLift 100130
  have htrace : WordTrace (prefixWord ++ tailWord_100130) baseStart_100130 baseEnd_100130 := by
    simpa [prefixWord, tailWord_100130, baseEnd_100130] using wordTrace_append hprefix tailTrace_100130
  have hstable : (prefixWord ++ tailWord_100130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100130).length < 2 ^ (prefixWord ++ tailWord_100130).sum := by decide
  have hdescent : baseEnd_100130 < baseStart_100130 := by decide
  rcases family_descends (prefixWord ++ tailWord_100130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100145 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 6]
def baseStart_100145 : Nat := 118140960795 + 100145 * 2 ^ 59
def prefixEnd_100145 : Nat := 4983230072969 + 3 ^ 40 * 100145 * 2
def baseEnd_100145 : Nat := 11427226698803536872655

theorem tailTrace_100145 : CollatzResearch.WordTrace tailWord_100145 prefixEnd_100145 11427226698803536872655 := by
  unfold tailWord_100145
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652588222199243249437889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2435058814799495499625259 3652588222199243249437889)
  ·
    refine ⟨2739441166649432437078417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3652588222199243249437889 2739441166649432437078417)
    ·
      refine ⟨2054580874987074327808813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2739441166649432437078417 2054580874987074327808813)
      ·
        refine ⟨770467828120152872928305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2054580874987074327808813 770467828120152872928305)
        ·
          refine ⟨577850871090114654696229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770467828120152872928305 577850871090114654696229)
          ·
            refine ⟨108347038329396497755543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 577850871090114654696229 108347038329396497755543)
            ·
              refine ⟨162520557494094746633315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108347038329396497755543 162520557494094746633315)
              ·
                refine ⟨243780836241142119949973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162520557494094746633315 243780836241142119949973)
                ·
                  refine ⟨11427226698803536872655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 243780836241142119949973 11427226698803536872655)
                  ·
                    rfl

theorem cell22_100145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_100145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100145 prefixEnd_100145 := by exact prefixLift 100145
  have htrace : WordTrace (prefixWord ++ tailWord_100145) baseStart_100145 baseEnd_100145 := by
    simpa [prefixWord, tailWord_100145, baseEnd_100145] using wordTrace_append hprefix tailTrace_100145
  have hstable : (prefixWord ++ tailWord_100145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100145).length < 2 ^ (prefixWord ++ tailWord_100145).sum := by decide
  have hdescent : baseEnd_100145 < baseStart_100145 := by decide
  rcases family_descends (prefixWord ++ tailWord_100145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100194 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_100194 : Nat := 118140960795 + 100194 * 2 ^ 59
def prefixEnd_100194 : Nat := 4983230072969 + 3 ^ 40 * 100194 * 2
def baseEnd_100194 : Nat := 34298453797790816142815

theorem tailTrace_100194 : CollatzResearch.WordTrace tailWord_100194 prefixEnd_100194 34298453797790816142815 := by
  unfold tailWord_100194
  simp only [CollatzResearch.WordTrace]
  refine ⟨913593849755431154492909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2436250266014483078647757 913593849755431154492909)
  ·
    refine ⟨342597693658286682934841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 913593849755431154492909 342597693658286682934841)
    ·
      refine ⟨256948270243715012201131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342597693658286682934841 256948270243715012201131)
      ·
        refine ⟨385422405365572518301697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256948270243715012201131 385422405365572518301697)
        ·
          refine ⟨289066804024179388726273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385422405365572518301697 289066804024179388726273)
          ·
            refine ⟨216800103018134541544705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289066804024179388726273 216800103018134541544705)
            ·
              refine ⟨162600077263600906158529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216800103018134541544705 162600077263600906158529)
              ·
                refine ⟨121950057947700679618897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162600077263600906158529 121950057947700679618897)
                ·
                  refine ⟨91462543460775509714173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121950057947700679618897 91462543460775509714173)
                  ·
                    refine ⟨34298453797790816142815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91462543460775509714173 34298453797790816142815)
                    ·
                      rfl

theorem cell22_100194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_100194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100194 prefixEnd_100194 := by exact prefixLift 100194
  have htrace : WordTrace (prefixWord ++ tailWord_100194) baseStart_100194 baseEnd_100194 := by
    simpa [prefixWord, tailWord_100194, baseEnd_100194] using wordTrace_append hprefix tailTrace_100194
  have hstable : (prefixWord ++ tailWord_100194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100194).length < 2 ^ (prefixWord ++ tailWord_100194).sum := by decide
  have hdescent : baseEnd_100194 < baseStart_100194 := by decide
  rcases family_descends (prefixWord ++ tailWord_100194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100196 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 4]
def baseStart_100196 : Nat := 118140960795 + 100196 * 2 ^ 59
def prefixEnd_100196 : Nat := 4983230072969 + 3 ^ 40 * 100196 * 2
def baseEnd_100196 : Nat := 11433046146221159197603

theorem tailTrace_100196 : CollatzResearch.WordTrace tailWord_100196 prefixEnd_100196 11433046146221159197603 := by
  unfold tailWord_100196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827224172507239479772221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2436298896676319306362961 1827224172507239479772221)
  ·
    refine ⟨685209064690214804914583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1827224172507239479772221 685209064690214804914583)
    ·
      refine ⟨1027813597035322207371875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685209064690214804914583 1027813597035322207371875)
      ·
        refine ⟨1541720395552983311057813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027813597035322207371875 1541720395552983311057813)
        ·
          refine ⟨72268143541546092705835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1541720395552983311057813 72268143541546092705835)
          ·
            refine ⟨108402215312319139058753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72268143541546092705835 108402215312319139058753)
            ·
              refine ⟨81301661484239354294065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108402215312319139058753 81301661484239354294065)
              ·
                refine ⟨60976246113179515720549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81301661484239354294065 60976246113179515720549)
                ·
                  refine ⟨11433046146221159197603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60976246113179515720549 11433046146221159197603)
                  ·
                    rfl

theorem cell22_100196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_100196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100196 prefixEnd_100196 := by exact prefixLift 100196
  have htrace : WordTrace (prefixWord ++ tailWord_100196) baseStart_100196 baseEnd_100196 := by
    simpa [prefixWord, tailWord_100196, baseEnd_100196] using wordTrace_append hprefix tailTrace_100196
  have hstable : (prefixWord ++ tailWord_100196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100196).length < 2 ^ (prefixWord ++ tailWord_100196).sum := by decide
  have hdescent : baseEnd_100196 < baseStart_100196 := by decide
  rcases family_descends (prefixWord ++ tailWord_100196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100233 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_100233 : Nat := 118140960795 + 100233 * 2 ^ 59
def prefixEnd_100233 : Nat := 4983230072969 + 3 ^ 40 * 100233 * 2
def baseEnd_100233 : Nat := 34311804294807714417695

theorem tailTrace_100233 : CollatzResearch.WordTrace tailWord_100233 prefixEnd_100233 34311804294807714417695 := by
  unfold tailWord_100233
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655797845880434278641353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2437198563920289519094235 3655797845880434278641353)
  ·
    refine ⟨2741848384410325708981015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3655797845880434278641353 2741848384410325708981015)
    ·
      refine ⟨4112772576615488563471523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2741848384410325708981015 4112772576615488563471523)
      ·
        refine ⟨6169158864923232845207285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112772576615488563471523 6169158864923232845207285)
        ·
          refine ⟨578358643586553079238183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6169158864923232845207285 578358643586553079238183)
          ·
            refine ⟨867537965379829618857275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578358643586553079238183 867537965379829618857275)
            ·
              refine ⟨1301306948069744428285913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867537965379829618857275 1301306948069744428285913)
              ·
                refine ⟨975980211052308321214435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301306948069744428285913 975980211052308321214435)
                ·
                  refine ⟨1463970316578462481821653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975980211052308321214435 1463970316578462481821653)
                  ·
                    refine ⟨34311804294807714417695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1463970316578462481821653 34311804294807714417695)
                    ·
                      rfl

theorem cell22_100233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_100233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100233 prefixEnd_100233 := by exact prefixLift 100233
  have htrace : WordTrace (prefixWord ++ tailWord_100233) baseStart_100233 baseEnd_100233 := by
    simpa [prefixWord, tailWord_100233, baseEnd_100233] using wordTrace_append hprefix tailTrace_100233
  have hstable : (prefixWord ++ tailWord_100233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100233).length < 2 ^ (prefixWord ++ tailWord_100233).sum := by decide
  have hdescent : baseEnd_100233 < baseStart_100233 := by decide
  rcases family_descends (prefixWord ++ tailWord_100233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100250 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_100250 : Nat := 118140960795 + 100250 * 2 ^ 59
def prefixEnd_100250 : Nat := 4983230072969 + 3 ^ 40 * 100250 * 2
def baseEnd_100250 : Nat := 34317623742225336742643

theorem tailTrace_100250 : CollatzResearch.WordTrace tailWord_100250 prefixEnd_100250 34317623742225336742643 := by
  unfold tailWord_100250
  simp only [CollatzResearch.WordTrace]
  refine ⟨914104471704711545502551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2437611924545897454673469 914104471704711545502551)
  ·
    refine ⟨1371156707557067318253827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914104471704711545502551 1371156707557067318253827)
    ·
      refine ⟨2056735061335600977380741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371156707557067318253827 2056735061335600977380741)
      ·
        refine ⟨385637824000425183258889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2056735061335600977380741 385637824000425183258889)
        ·
          refine ⟨289228368000318887444167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385637824000425183258889 289228368000318887444167)
          ·
            refine ⟨433842552000478331166251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289228368000318887444167 433842552000478331166251)
            ·
              refine ⟨650763828000717496749377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433842552000478331166251 650763828000717496749377)
              ·
                refine ⟨488072871000538122562033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650763828000717496749377 488072871000538122562033)
                ·
                  refine ⟨366054653250403591921525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488072871000538122562033 366054653250403591921525)
                  ·
                    refine ⟨34317623742225336742643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 366054653250403591921525 34317623742225336742643)
                    ·
                      rfl

theorem cell22_100250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_100250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100250 prefixEnd_100250 := by exact prefixLift 100250
  have htrace : WordTrace (prefixWord ++ tailWord_100250) baseStart_100250 baseEnd_100250 := by
    simpa [prefixWord, tailWord_100250, baseEnd_100250] using wordTrace_append hprefix tailTrace_100250
  have hstable : (prefixWord ++ tailWord_100250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100250).length < 2 ^ (prefixWord ++ tailWord_100250).sum := by decide
  have hdescent : baseEnd_100250 < baseStart_100250 := by decide
  rcases family_descends (prefixWord ++ tailWord_100250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100252 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_100252 : Nat := 118140960795 + 100252 * 2 ^ 59
def prefixEnd_100252 : Nat := 4983230072969 + 3 ^ 40 * 100252 * 2
def baseEnd_100252 : Nat := 11439436127699332730879

theorem tailTrace_100252 : CollatzResearch.WordTrace tailWord_100252 prefixEnd_100252 11439436127699332730879 := by
  unfold tailWord_100252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828245416405800261791505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2437660555207733682388673 1828245416405800261791505)
  ·
    refine ⟨1371184062304350196343629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1828245416405800261791505 1371184062304350196343629)
    ·
      refine ⟨514194023364131323628861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1371184062304350196343629 514194023364131323628861)
      ·
        refine ⟨192822758761549246360823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514194023364131323628861 192822758761549246360823)
        ·
          refine ⟨289234138142323869541235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192822758761549246360823 289234138142323869541235)
          ·
            refine ⟨433851207213485804311853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289234138142323869541235 433851207213485804311853)
            ·
              refine ⟨162694202705057176616945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433851207213485804311853 162694202705057176616945)
              ·
                refine ⟨122020652028792882462709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162694202705057176616945 122020652028792882462709)
                ·
                  refine ⟨11439436127699332730879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122020652028792882462709 11439436127699332730879)
                  ·
                    rfl

theorem cell22_100252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_100252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100252 prefixEnd_100252 := by exact prefixLift 100252
  have htrace : WordTrace (prefixWord ++ tailWord_100252) baseStart_100252 baseEnd_100252 := by
    simpa [prefixWord, tailWord_100252, baseEnd_100252] using wordTrace_append hprefix tailTrace_100252
  have hstable : (prefixWord ++ tailWord_100252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100252).length < 2 ^ (prefixWord ++ tailWord_100252).sum := by decide
  have hdescent : baseEnd_100252 < baseStart_100252 := by decide
  rcases family_descends (prefixWord ++ tailWord_100252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100312 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_100312 : Nat := 118140960795 + 100312 * 2 ^ 59
def prefixEnd_100312 : Nat := 4983230072969 + 3 ^ 40 * 100312 * 2
def baseEnd_100312 : Nat := 34338847609277841692453

theorem tailTrace_100312 : CollatzResearch.WordTrace tailWord_100312 prefixEnd_100312 34338847609277841692453 := by
  unfold tailWord_100312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829339606297115385383595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2439119475062820513844793 1829339606297115385383595)
  ·
    refine ⟨2744009409445673078075393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1829339606297115385383595 2744009409445673078075393)
    ·
      refine ⟨2058007057084254808556545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744009409445673078075393 2058007057084254808556545)
      ·
        refine ⟨1543505292813191106417409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058007057084254808556545 1543505292813191106417409)
        ·
          refine ⟨1157628969609893329813057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543505292813191106417409 1157628969609893329813057)
          ·
            refine ⟨868221727207419997359793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157628969609893329813057 868221727207419997359793)
            ·
              refine ⟨651166295405564998019845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868221727207419997359793 651166295405564998019845)
              ·
                refine ⟨122093680388543437128721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 651166295405564998019845 122093680388543437128721)
                ·
                  refine ⟨91570260291407577846541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122093680388543437128721 91570260291407577846541)
                  ·
                    refine ⟨34338847609277841692453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91570260291407577846541 34338847609277841692453)
                    ·
                      rfl

theorem cell22_100312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_100312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100312 prefixEnd_100312 := by exact prefixLift 100312
  have htrace : WordTrace (prefixWord ++ tailWord_100312) baseStart_100312 baseEnd_100312 := by
    simpa [prefixWord, tailWord_100312, baseEnd_100312] using wordTrace_append hprefix tailTrace_100312
  have hstable : (prefixWord ++ tailWord_100312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100312).length < 2 ^ (prefixWord ++ tailWord_100312).sum := by decide
  have hdescent : baseEnd_100312 < baseStart_100312 := by decide
  rcases family_descends (prefixWord ++ tailWord_100312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100314 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_100314 : Nat := 118140960795 + 100314 * 2 ^ 59
def prefixEnd_100314 : Nat := 4983230072969 + 3 ^ 40 * 100314 * 2
def baseEnd_100314 : Nat := 11446510750050167714149

theorem tailTrace_100314 : CollatzResearch.WordTrace tailWord_100314 prefixEnd_100314 11446510750050167714149 := by
  unfold tailWord_100314
  simp only [CollatzResearch.WordTrace]
  refine ⟨914688039646746278084999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2439168105724656741559997 914688039646746278084999)
  ·
    refine ⟨1372032059470119417127499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 914688039646746278084999 1372032059470119417127499)
    ·
      refine ⟨2058048089205179125691249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1372032059470119417127499 2058048089205179125691249)
      ·
        refine ⟨1543536066903884344268437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058048089205179125691249 1543536066903884344268437)
        ·
          refine ⟨72353253136119578637583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1543536066903884344268437 72353253136119578637583)
          ·
            refine ⟨108529879704179367956375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72353253136119578637583 108529879704179367956375)
            ·
              refine ⟨162794819556269051934563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108529879704179367956375 162794819556269051934563)
              ·
                refine ⟨244192229334403577901845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162794819556269051934563 244192229334403577901845)
                ·
                  refine ⟨11446510750050167714149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244192229334403577901845 11446510750050167714149)
                  ·
                    rfl

theorem cell22_100314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_100314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100314 prefixEnd_100314 := by exact prefixLift 100314
  have htrace : WordTrace (prefixWord ++ tailWord_100314) baseStart_100314 baseEnd_100314 := by
    simpa [prefixWord, tailWord_100314, baseEnd_100314] using wordTrace_append hprefix tailTrace_100314
  have hstable : (prefixWord ++ tailWord_100314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100314).length < 2 ^ (prefixWord ++ tailWord_100314).sum := by decide
  have hdescent : baseEnd_100314 < baseStart_100314 := by decide
  rcases family_descends (prefixWord ++ tailWord_100314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100333 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_100333 : Nat := 118140960795 + 100333 * 2 ^ 59
def prefixEnd_100333 : Nat := 4983230072969 + 3 ^ 40 * 100333 * 2
def baseEnd_100333 : Nat := 34346036338440786917389

theorem tailTrace_100333 : CollatzResearch.WordTrace tailWord_100333 prefixEnd_100333 34346036338440786917389 := by
  unfold tailWord_100333
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659445145518151357281653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2439630097012100904854435 3659445145518151357281653)
  ·
    refine ⟨343072982392326689745155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3659445145518151357281653 343072982392326689745155)
    ·
      refine ⟨514609473588490034617733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343072982392326689745155 514609473588490034617733)
      ·
        refine ⟨96489276297841881490825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 514609473588490034617733 96489276297841881490825)
        ·
          refine ⟨72366957223381411118119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96489276297841881490825 72366957223381411118119)
          ·
            refine ⟨108550435835072116677179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72366957223381411118119 108550435835072116677179)
            ·
              refine ⟨162825653752608175015769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108550435835072116677179 162825653752608175015769)
              ·
                refine ⟨122119240314456131261827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162825653752608175015769 122119240314456131261827)
                ·
                  refine ⟨183178860471684196892741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122119240314456131261827 183178860471684196892741)
                  ·
                    refine ⟨34346036338440786917389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183178860471684196892741 34346036338440786917389)
                    ·
                      rfl

theorem cell22_100333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_100333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100333 prefixEnd_100333 := by exact prefixLift 100333
  have htrace : WordTrace (prefixWord ++ tailWord_100333) baseStart_100333 baseEnd_100333 := by
    simpa [prefixWord, tailWord_100333, baseEnd_100333] using wordTrace_append hprefix tailTrace_100333
  have hstable : (prefixWord ++ tailWord_100333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100333).length < 2 ^ (prefixWord ++ tailWord_100333).sum := by decide
  have hdescent : baseEnd_100333 < baseStart_100333 := by decide
  rcases family_descends (prefixWord ++ tailWord_100333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100391 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 3, 3]
def baseStart_100391 : Nat := 118140960795 + 100391 * 2 ^ 59
def prefixEnd_100391 : Nat := 4983230072969 + 3 ^ 40 * 100391 * 2
def baseEnd_100391 : Nat := 34365890923747968967211

theorem tailTrace_100391 : CollatzResearch.WordTrace tailWord_100391 prefixEnd_100391 34365890923747968967211 := by
  unfold tailWord_100391
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661560579308027262893027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2441040386205351508595351 3661560579308027262893027)
  ·
    refine ⟨5492340868962040894339541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661560579308027262893027 5492340868962040894339541)
    ·
      refine ⟨128726739116297833461083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5492340868962040894339541 128726739116297833461083)
      ·
        refine ⟨193090108674446750191625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128726739116297833461083 193090108674446750191625)
        ·
          refine ⟨144817581505835062643719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193090108674446750191625 144817581505835062643719)
          ·
            refine ⟨217226372258752593965579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144817581505835062643719 217226372258752593965579)
            ·
              refine ⟨325839558388128890948369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217226372258752593965579 325839558388128890948369)
              ·
                refine ⟨244379668791096668211277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325839558388128890948369 244379668791096668211277)
                ·
                  refine ⟨91642375796661250579229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244379668791096668211277 91642375796661250579229)
                  ·
                    refine ⟨34365890923747968967211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91642375796661250579229 34365890923747968967211)
                    ·
                      rfl

theorem cell22_100391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_100391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100391 prefixEnd_100391 := by exact prefixLift 100391
  have htrace : WordTrace (prefixWord ++ tailWord_100391) baseStart_100391 baseEnd_100391 := by
    simpa [prefixWord, tailWord_100391, baseEnd_100391] using wordTrace_append hprefix tailTrace_100391
  have hstable : (prefixWord ++ tailWord_100391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100391).length < 2 ^ (prefixWord ++ tailWord_100391).sum := by decide
  have hdescent : baseEnd_100391 < baseStart_100391 := by decide
  rcases family_descends (prefixWord ++ tailWord_100391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100438 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_100438 : Nat := 118140960795 + 100438 * 2 ^ 59
def prefixEnd_100438 : Nat := 4983230072969 + 3 ^ 40 * 100438 * 2
def baseEnd_100438 : Nat := 11460659994751837680689

theorem tailTrace_100438 : CollatzResearch.WordTrace tailWord_100438 prefixEnd_100438 11460659994751837680689 := by
  unfold tailWord_100438
  simp only [CollatzResearch.WordTrace]
  refine ⟨228954675633609643115873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2442183206758502859902645 228954675633609643115873)
  ·
    refine ⟨171716006725207232336905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228954675633609643115873 171716006725207232336905)
    ·
      refine ⟨128787005043905424252679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171716006725207232336905 128787005043905424252679)
      ·
        refine ⟨193180507565858136379019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128787005043905424252679 193180507565858136379019)
        ·
          refine ⟨289770761348787204568529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193180507565858136379019 289770761348787204568529)
          ·
            refine ⟨217328071011590403426397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289770761348787204568529 217328071011590403426397)
            ·
              refine ⟨81498026629346401284899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217328071011590403426397 81498026629346401284899)
              ·
                refine ⟨122247039944019601927349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81498026629346401284899 122247039944019601927349)
                ·
                  refine ⟨11460659994751837680689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122247039944019601927349 11460659994751837680689)
                  ·
                    rfl

theorem cell22_100438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_100438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100438 prefixEnd_100438 := by exact prefixLift 100438
  have htrace : WordTrace (prefixWord ++ tailWord_100438) baseStart_100438 baseEnd_100438 := by
    simpa [prefixWord, tailWord_100438, baseEnd_100438] using wordTrace_append hprefix tailTrace_100438
  have hstable : (prefixWord ++ tailWord_100438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100438).length < 2 ^ (prefixWord ++ tailWord_100438).sum := by decide
  have hdescent : baseEnd_100438 < baseStart_100438 := by decide
  rcases family_descends (prefixWord ++ tailWord_100438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100462 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_100462 : Nat := 118140960795 + 100462 * 2 ^ 59
def prefixEnd_100462 : Nat := 4983230072969 + 3 ^ 40 * 100462 * 2
def baseEnd_100462 : Nat := 34390195674727450441993

theorem tailTrace_100462 : CollatzResearch.WordTrace tailWord_100462 prefixEnd_100462 34390195674727450441993 := by
  unfold tailWord_100462
  simp only [CollatzResearch.WordTrace]
  refine ⟨458018770256350798590955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2442766774700537592485093 458018770256350798590955)
  ·
    refine ⟨687028155384526197886433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458018770256350798590955 687028155384526197886433)
    ·
      refine ⟨515271116538394648414825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 687028155384526197886433 515271116538394648414825)
      ·
        refine ⟨386453337403795986311119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515271116538394648414825 386453337403795986311119)
        ·
          refine ⟨579680006105693979466679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386453337403795986311119 579680006105693979466679)
          ·
            refine ⟨869520009158540969200019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579680006105693979466679 869520009158540969200019)
            ·
              refine ⟨1304280013737811453800029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869520009158540969200019 1304280013737811453800029)
              ·
                refine ⟨489105005151679295175011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304280013737811453800029 489105005151679295175011)
                ·
                  refine ⟨733657507727518942762517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489105005151679295175011 733657507727518942762517)
                  ·
                    refine ⟨34390195674727450441993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 733657507727518942762517 34390195674727450441993)
                    ·
                      rfl

theorem cell22_100462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_100462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100462 prefixEnd_100462 := by exact prefixLift 100462
  have htrace : WordTrace (prefixWord ++ tailWord_100462) baseStart_100462 baseEnd_100462 := by
    simpa [prefixWord, tailWord_100462, baseEnd_100462] using wordTrace_append hprefix tailTrace_100462
  have hstable : (prefixWord ++ tailWord_100462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100462).length < 2 ^ (prefixWord ++ tailWord_100462).sum := by decide
  have hdescent : baseEnd_100462 < baseStart_100462 := by decide
  rcases family_descends (prefixWord ++ tailWord_100462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100466 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_100466 : Nat := 118140960795 + 100466 * 2 ^ 59
def prefixEnd_100466 : Nat := 4983230072969 + 3 ^ 40 * 100466 * 2
def baseEnd_100466 : Nat := 11463854985490924447327

theorem tailTrace_100466 : CollatzResearch.WordTrace tailWord_100466 prefixEnd_100466 11463854985490924447327 := by
  unfold tailWord_100466
  simp only [CollatzResearch.WordTrace]
  refine ⟨916074013509078767968313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2442864036024210047915501 916074013509078767968313)
  ·
    refine ⟨687055510131809075976235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 916074013509078767968313 687055510131809075976235)
    ·
      refine ⟨1030583265197713613964353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687055510131809075976235 1030583265197713613964353)
      ·
        refine ⟨772937448898285210473265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1030583265197713613964353 772937448898285210473265)
        ·
          refine ⟨579703086673713907854949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772937448898285210473265 579703086673713907854949)
          ·
            refine ⟨108694328751321357722803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 579703086673713907854949 108694328751321357722803)
            ·
              refine ⟨163041493126982036584205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108694328751321357722803 163041493126982036584205)
              ·
                refine ⟨61140559922618263719077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163041493126982036584205 61140559922618263719077)
                ·
                  refine ⟨11463854985490924447327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61140559922618263719077 11463854985490924447327)
                  ·
                    rfl

theorem cell22_100466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_100466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100466 prefixEnd_100466 := by exact prefixLift 100466
  have htrace : WordTrace (prefixWord ++ tailWord_100466) baseStart_100466 baseEnd_100466 := by
    simpa [prefixWord, tailWord_100466, baseEnd_100466] using wordTrace_append hprefix tailTrace_100466
  have hstable : (prefixWord ++ tailWord_100466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100466).length < 2 ^ (prefixWord ++ tailWord_100466).sum := by decide
  have hdescent : baseEnd_100466 < baseStart_100466 := by decide
  rcases family_descends (prefixWord ++ tailWord_100466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100477 : List Nat := [1, 4, 1, 1, 3, 4, 8]
def baseStart_100477 : Nat := 118140960795 + 100477 * 2 ^ 59
def prefixEnd_100477 : Nat := 4983230072969 + 3 ^ 40 * 100477 * 2
def baseEnd_100477 : Nat := 1273901128936015233961

theorem tailTrace_100477 : CollatzResearch.WordTrace tailWord_100477 prefixEnd_100477 1273901128936015233961 := by
  unfold tailWord_100477
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664697256996463950523685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2443131504664309300349123 3664697256996463950523685)
  ·
    refine ⟨687130735686836990723191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3664697256996463950523685 687130735686836990723191)
    ·
      refine ⟨1030696103530255486084787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687130735686836990723191 1030696103530255486084787)
      ·
        refine ⟨1546044155295383229127181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030696103530255486084787 1546044155295383229127181)
        ·
          refine ⟨579766558235768710922693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1546044155295383229127181 579766558235768710922693)
          ·
            refine ⟨108706229669206633298005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 579766558235768710922693 108706229669206633298005)
            ·
              refine ⟨1273901128936015233961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 108706229669206633298005 1273901128936015233961)
              ·
                rfl

theorem cell22_100477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 8].length) (baseStart_100477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100477 prefixEnd_100477 := by exact prefixLift 100477
  have htrace : WordTrace (prefixWord ++ tailWord_100477) baseStart_100477 baseEnd_100477 := by
    simpa [prefixWord, tailWord_100477, baseEnd_100477] using wordTrace_append hprefix tailTrace_100477
  have hstable : (prefixWord ++ tailWord_100477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100477).length < 2 ^ (prefixWord ++ tailWord_100477).sum := by decide
  have hdescent : baseEnd_100477 < baseStart_100477 := by decide
  rcases family_descends (prefixWord ++ tailWord_100477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100494 : List Nat := [4, 1, 1, 3, 3, 1, 2, 7]
def baseStart_100494 : Nat := 118140960795 + 100494 * 2 ^ 59
def prefixEnd_100494 : Nat := 4983230072969 + 3 ^ 40 * 100494 * 2
def baseEnd_100494 : Nat := 3822349992076670404655

theorem tailTrace_100494 : CollatzResearch.WordTrace tailWord_100494 prefixEnd_100494 3822349992076670404655 := by
  unfold tailWord_100494
  simp only [CollatzResearch.WordTrace]
  refine ⟨458164662241859481736567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2443544865289917235928357 458164662241859481736567)
  ·
    refine ⟨687246993362789222604851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 458164662241859481736567 687246993362789222604851)
    ·
      refine ⟨1030870490044183833907277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687246993362789222604851 1030870490044183833907277)
      ·
        refine ⟨386576433766568937715229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1030870490044183833907277 386576433766568937715229)
        ·
          refine ⟨144966162662463351643211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386576433766568937715229 144966162662463351643211)
          ·
            refine ⟨217449243993695027464817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144966162662463351643211 217449243993695027464817)
            ·
              refine ⟨163086932995271270598613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217449243993695027464817 163086932995271270598613)
              ·
                refine ⟨3822349992076670404655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 163086932995271270598613 3822349992076670404655)
                ·
                  rfl

theorem cell22_100494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_100494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100494 prefixEnd_100494 := by exact prefixLift 100494
  have htrace : WordTrace (prefixWord ++ tailWord_100494) baseStart_100494 baseEnd_100494 := by
    simpa [prefixWord, tailWord_100494, baseEnd_100494] using wordTrace_append hprefix tailTrace_100494
  have hstable : (prefixWord ++ tailWord_100494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100494).length < 2 ^ (prefixWord ++ tailWord_100494).sum := by decide
  have hdescent : baseEnd_100494 < baseStart_100494 := by decide
  rcases family_descends (prefixWord ++ tailWord_100494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100532 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_100532 : Nat := 118140960795 + 100532 * 2 ^ 59
def prefixEnd_100532 : Nat := 4983230072969 + 3 ^ 40 * 100532 * 2
def baseEnd_100532 : Nat := 34414158105270601191779

theorem tailTrace_100532 : CollatzResearch.WordTrace tailWord_100532 prefixEnd_100532 34414158105270601191779 := by
  unfold tailWord_100532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833351635898604171887925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2444468847864805562517233 1833351635898604171887925)
  ·
    refine ⟨171876715865494141114493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1833351635898604171887925 171876715865494141114493)
    ·
      refine ⟨64453768449560302917935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171876715865494141114493 64453768449560302917935)
      ·
        refine ⟨96680652674340454376903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64453768449560302917935 96680652674340454376903)
        ·
          refine ⟨145020979011510681565355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96680652674340454376903 145020979011510681565355)
          ·
            refine ⟨217531468517266022348033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145020979011510681565355 217531468517266022348033)
            ·
              refine ⟨163148601387949516761025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217531468517266022348033 163148601387949516761025)
              ·
                refine ⟨122361451040962137570769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163148601387949516761025 122361451040962137570769)
                ·
                  refine ⟨91771088280721603178077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122361451040962137570769 91771088280721603178077)
                  ·
                    refine ⟨34414158105270601191779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91771088280721603178077 34414158105270601191779)
                    ·
                      rfl

theorem cell22_100532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_100532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100532 prefixEnd_100532 := by exact prefixLift 100532
  have htrace : WordTrace (prefixWord ++ tailWord_100532) baseStart_100532 baseEnd_100532 := by
    simpa [prefixWord, tailWord_100532, baseEnd_100532] using wordTrace_append hprefix tailTrace_100532
  have hstable : (prefixWord ++ tailWord_100532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100532).length < 2 ^ (prefixWord ++ tailWord_100532).sum := by decide
  have hdescent : baseEnd_100532 < baseStart_100532 := by decide
  rcases family_descends (prefixWord ++ tailWord_100532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100537 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_100537 : Nat := 118140960795 + 100537 * 2 ^ 59
def prefixEnd_100537 : Nat := 4983230072969 + 3 ^ 40 * 100537 * 2
def baseEnd_100537 : Nat := 34415869707452254816763

theorem tailTrace_100537 : CollatzResearch.WordTrace tailWord_100537 prefixEnd_100537 34415869707452254816763 := by
  unfold tailWord_100537
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666885636779094197707865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2444590424519396131805243 3666885636779094197707865)
  ·
    refine ⟨2750164227584320648280899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3666885636779094197707865 2750164227584320648280899)
    ·
      refine ⟨4125246341376480972421349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750164227584320648280899 4125246341376480972421349)
      ·
        refine ⟨773483689008090182329003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4125246341376480972421349 773483689008090182329003)
        ·
          refine ⟨1160225533512135273493505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773483689008090182329003 1160225533512135273493505)
          ·
            refine ⟨870169150134101455120129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160225533512135273493505 870169150134101455120129)
            ·
              refine ⟨652626862600576091340097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870169150134101455120129 652626862600576091340097)
              ·
                refine ⟨489470146950432068505073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652626862600576091340097 489470146950432068505073)
                ·
                  refine ⟨367102610212824051378805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489470146950432068505073 367102610212824051378805)
                  ·
                    refine ⟨34415869707452254816763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 367102610212824051378805 34415869707452254816763)
                    ·
                      rfl

theorem cell22_100537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_100537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100537 prefixEnd_100537 := by exact prefixLift 100537
  have htrace : WordTrace (prefixWord ++ tailWord_100537) baseStart_100537 baseEnd_100537 := by
    simpa [prefixWord, tailWord_100537, baseEnd_100537] using wordTrace_append hprefix tailTrace_100537
  have hstable : (prefixWord ++ tailWord_100537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100537).length < 2 ^ (prefixWord ++ tailWord_100537).sum := by decide
  have hdescent : baseEnd_100537 < baseStart_100537 := by decide
  rcases family_descends (prefixWord ++ tailWord_100537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100616 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_100616 : Nat := 118140960795 + 100616 * 2 ^ 59
def prefixEnd_100616 : Nat := 4983230072969 + 3 ^ 40 * 100616 * 2
def baseEnd_100616 : Nat := 34442913021922382091521

theorem tailTrace_100616 : CollatzResearch.WordTrace tailWord_100616 prefixEnd_100616 34442913021922382091521 := by
  unfold tailWord_100616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834883501746445344916851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2446511335661927126555801 1834883501746445344916851)
  ·
    refine ⟨2752325252619668017375277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834883501746445344916851 2752325252619668017375277)
    ·
      refine ⟨1032121969732375506515729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2752325252619668017375277 1032121969732375506515729)
      ·
        refine ⟨774091477299281629886797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1032121969732375506515729 774091477299281629886797)
        ·
          refine ⟨290284303987230611207549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 774091477299281629886797 290284303987230611207549)
          ·
            refine ⟨108856613995211479202831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290284303987230611207549 108856613995211479202831)
            ·
              refine ⟨163284920992817218804247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108856613995211479202831 163284920992817218804247)
              ·
                refine ⟨244927381489225828206371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163284920992817218804247 244927381489225828206371)
                ·
                  refine ⟨367391072233838742309557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244927381489225828206371 367391072233838742309557)
                  ·
                    refine ⟨34442913021922382091521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 367391072233838742309557 34442913021922382091521)
                    ·
                      rfl

theorem cell22_100616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_100616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100616 prefixEnd_100616 := by exact prefixLift 100616
  have htrace : WordTrace (prefixWord ++ tailWord_100616) baseStart_100616 baseEnd_100616 := by
    simpa [prefixWord, tailWord_100616, baseEnd_100616] using wordTrace_append hprefix tailTrace_100616
  have hstable : (prefixWord ++ tailWord_100616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100616).length < 2 ^ (prefixWord ++ tailWord_100616).sum := by decide
  have hdescent : baseEnd_100616 < baseStart_100616 := by decide
  rcases family_descends (prefixWord ++ tailWord_100616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100629 : List Nat := [1, 3, 2, 1, 2, 1, 6, 6]
def baseStart_100629 : Nat := 118140960795 + 100629 * 2 ^ 59
def prefixEnd_100629 : Nat := 4983230072969 + 3 ^ 40 * 100629 * 2
def baseEnd_100629 : Nat := 3827484798621631279609

theorem tailTrace_100629 : CollatzResearch.WordTrace tailWord_100629 prefixEnd_100629 3827484798621631279609 := by
  unfold tailWord_100629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3670241152445793910056941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2446827434963862606704627 3670241152445793910056941)
  ·
    refine ⟨1376340432167172716271353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3670241152445793910056941 1376340432167172716271353)
    ·
      refine ⟨1032255324125379537203515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1376340432167172716271353 1032255324125379537203515)
      ·
        refine ⟨1548382986188069305805273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032255324125379537203515 1548382986188069305805273)
        ·
          refine ⟨1161287239641051979353955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1548382986188069305805273 1161287239641051979353955)
          ·
            refine ⟨1741930859461577969030933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161287239641051979353955 1741930859461577969030933)
            ·
              refine ⟨81653009037261467298325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1741930859461577969030933 81653009037261467298325)
              ·
                refine ⟨3827484798621631279609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81653009037261467298325 3827484798621631279609)
                ·
                  rfl

theorem cell22_100629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 6].length) (baseStart_100629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100629 prefixEnd_100629 := by exact prefixLift 100629
  have htrace : WordTrace (prefixWord ++ tailWord_100629) baseStart_100629 baseEnd_100629 := by
    simpa [prefixWord, tailWord_100629, baseEnd_100629] using wordTrace_append hprefix tailTrace_100629
  have hstable : (prefixWord ++ tailWord_100629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100629).length < 2 ^ (prefixWord ++ tailWord_100629).sum := by decide
  have hdescent : baseEnd_100629 < baseStart_100629 := by decide
  rcases family_descends (prefixWord ++ tailWord_100629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100712 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 1, 3]
def baseStart_100712 : Nat := 118140960795 + 100712 * 2 ^ 59
def prefixEnd_100712 : Nat := 4983230072969 + 3 ^ 40 * 100712 * 2
def baseEnd_100712 : Nat := 34475775783810131691227

theorem tailTrace_100712 : CollatzResearch.WordTrace tailWord_100712 prefixEnd_100712 34475775783810131691227 := by
  unfold tailWord_100712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1836634205572549542664195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2448845607430066056885593 1836634205572549542664195)
  ·
    refine ⟨2754951308358824313996293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1836634205572549542664195 2754951308358824313996293)
    ·
      refine ⟨516553370317279558874305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2754951308358824313996293 516553370317279558874305)
      ·
        refine ⟨387415027737959669155729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516553370317279558874305 387415027737959669155729)
        ·
          refine ⟨290561270803469751866797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387415027737959669155729 290561270803469751866797)
          ·
            refine ⟨108960476551301156950049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290561270803469751866797 108960476551301156950049)
            ·
              refine ⟨81720357413475867712537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108960476551301156950049 81720357413475867712537)
              ·
                refine ⟨61290268060106900784403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81720357413475867712537 61290268060106900784403)
                ·
                  refine ⟨91935402090160351176605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61290268060106900784403 91935402090160351176605)
                  ·
                    refine ⟨34475775783810131691227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91935402090160351176605 34475775783810131691227)
                    ·
                      rfl

theorem cell22_100712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_100712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100712 prefixEnd_100712 := by exact prefixLift 100712
  have htrace : WordTrace (prefixWord ++ tailWord_100712) baseStart_100712 baseEnd_100712 := by
    simpa [prefixWord, tailWord_100712, baseEnd_100712] using wordTrace_append hprefix tailTrace_100712
  have hstable : (prefixWord ++ tailWord_100712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100712).length < 2 ^ (prefixWord ++ tailWord_100712).sum := by decide
  have hdescent : baseEnd_100712 < baseStart_100712 := by decide
  rcases family_descends (prefixWord ++ tailWord_100712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100768 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 2, 3]
def baseStart_100768 : Nat := 118140960795 + 100768 * 2 ^ 59
def prefixEnd_100768 : Nat := 4983230072969 + 3 ^ 40 * 100768 * 2
def baseEnd_100768 : Nat := 34494945728244652291055

theorem tailTrace_100768 : CollatzResearch.WordTrace tailWord_100768 prefixEnd_100768 34494945728244652291055 := by
  unfold tailWord_100768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1837655449471110324683479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2450207265961480432911305 1837655449471110324683479)
  ·
    refine ⟨2756483174206665487025219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1837655449471110324683479 2756483174206665487025219)
    ·
      refine ⟨4134724761309998230537829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2756483174206665487025219 4134724761309998230537829)
      ·
        refine ⟨775260892745624668225843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4134724761309998230537829 775260892745624668225843)
        ·
          refine ⟨1162891339118437002338765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775260892745624668225843 1162891339118437002338765)
          ·
            refine ⟨436084252169413875877037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1162891339118437002338765 436084252169413875877037)
            ·
              refine ⟨163531594563530203453889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436084252169413875877037 163531594563530203453889)
              ·
                refine ⟨122648695922647652590417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163531594563530203453889 122648695922647652590417)
                ·
                  refine ⟨91986521941985739442813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122648695922647652590417 91986521941985739442813)
                  ·
                    refine ⟨34494945728244652291055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91986521941985739442813 34494945728244652291055)
                    ·
                      rfl

theorem cell22_100768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 3].length) (baseStart_100768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100768 prefixEnd_100768 := by exact prefixLift 100768
  have htrace : WordTrace (prefixWord ++ tailWord_100768) baseStart_100768 baseEnd_100768 := by
    simpa [prefixWord, tailWord_100768, baseEnd_100768] using wordTrace_append hprefix tailTrace_100768
  have hstable : (prefixWord ++ tailWord_100768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100768).length < 2 ^ (prefixWord ++ tailWord_100768).sum := by decide
  have hdescent : baseEnd_100768 < baseStart_100768 := by decide
  rcases family_descends (prefixWord ++ tailWord_100768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100785 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 2, 3]
def baseStart_100785 : Nat := 118140960795 + 100785 * 2 ^ 59
def prefixEnd_100785 : Nat := 4983230072969 + 3 ^ 40 * 100785 * 2
def baseEnd_100785 : Nat := 34500765175662274616003

theorem tailTrace_100785 : CollatzResearch.WordTrace tailWord_100785 prefixEnd_100785 34500765175662274616003 := by
  unfold tailWord_100785
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675930939880632552735809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2450620626587088368490539 3675930939880632552735809)
  ·
    refine ⟨2756948204910474414551857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3675930939880632552735809 2756948204910474414551857)
    ·
      refine ⟨2067711153682855810913893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2756948204910474414551857 2067711153682855810913893)
      ·
        refine ⟨387695841315535464546355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2067711153682855810913893 387695841315535464546355)
        ·
          refine ⟨581543761973303196819533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387695841315535464546355 581543761973303196819533)
          ·
            refine ⟨218078910739988698807325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 581543761973303196819533 218078910739988698807325)
            ·
              refine ⟨81779591527495762052747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218078910739988698807325 81779591527495762052747)
              ·
                refine ⟨122669387291243643079121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81779591527495762052747 122669387291243643079121)
                ·
                  refine ⟨92002040468432732309341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122669387291243643079121 92002040468432732309341)
                  ·
                    refine ⟨34500765175662274616003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92002040468432732309341 34500765175662274616003)
                    ·
                      rfl

theorem cell22_100785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_100785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100785 prefixEnd_100785 := by exact prefixLift 100785
  have htrace : WordTrace (prefixWord ++ tailWord_100785) baseStart_100785 baseEnd_100785 := by
    simpa [prefixWord, tailWord_100785, baseEnd_100785] using wordTrace_append hprefix tailTrace_100785
  have hstable : (prefixWord ++ tailWord_100785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100785).length < 2 ^ (prefixWord ++ tailWord_100785).sum := by decide
  have hdescent : baseEnd_100785 < baseStart_100785 := by decide
  rcases family_descends (prefixWord ++ tailWord_100785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100794 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_100794 : Nat := 118140960795 + 100794 * 2 ^ 59
def prefixEnd_100794 : Nat := 4983230072969 + 3 ^ 40 * 100794 * 2
def baseEnd_100794 : Nat := 34503846059589251140975

theorem tailTrace_100794 : CollatzResearch.WordTrace tailWord_100794 prefixEnd_100794 34503846059589251140975 := by
  unfold tailWord_100794
  simp only [CollatzResearch.WordTrace]
  refine ⟨919064799212006772453359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2450839464565351393208957 919064799212006772453359)
  ·
    refine ⟨1378597198818010158680039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 919064799212006772453359 1378597198818010158680039)
    ·
      refine ⟨2067895798227015238020059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378597198818010158680039 2067895798227015238020059)
      ·
        refine ⟨3101843697340522857030089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067895798227015238020059 3101843697340522857030089)
        ·
          refine ⟨2326382773005392142772567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3101843697340522857030089 2326382773005392142772567)
          ·
            refine ⟨3489574159508088214158851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326382773005392142772567 3489574159508088214158851)
            ·
              refine ⟨5234361239262132321238277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489574159508088214158851 5234361239262132321238277)
              ·
                refine ⟨981442732361649810232177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5234361239262132321238277 981442732361649810232177)
                ·
                  refine ⟨736082049271237357674133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 981442732361649810232177 736082049271237357674133)
                  ·
                    refine ⟨34503846059589251140975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 736082049271237357674133 34503846059589251140975)
                    ·
                      rfl

theorem cell22_100794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_100794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100794 prefixEnd_100794 := by exact prefixLift 100794
  have htrace : WordTrace (prefixWord ++ tailWord_100794) baseStart_100794 baseEnd_100794 := by
    simpa [prefixWord, tailWord_100794, baseEnd_100794] using wordTrace_append hprefix tailTrace_100794
  have hstable : (prefixWord ++ tailWord_100794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100794).length < 2 ^ (prefixWord ++ tailWord_100794).sum := by decide
  have hdescent : baseEnd_100794 < baseStart_100794 := by decide
  rcases family_descends (prefixWord ++ tailWord_100794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100809 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 7]
def baseStart_100809 : Nat := 118140960795 + 100809 * 2 ^ 59
def prefixEnd_100809 : Nat := 4983230072969 + 3 ^ 40 * 100809 * 2
def baseEnd_100809 : Nat := 11502993622044737338643

theorem tailTrace_100809 : CollatzResearch.WordTrace tailWord_100809 prefixEnd_100809 11502993622044737338643 := by
  unfold tailWord_100809
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676806291793684651609481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2451204194529123101072987 3676806291793684651609481)
  ·
    refine ⟨2757604718845263488707111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3676806291793684651609481 2757604718845263488707111)
    ·
      refine ⟨4136407078267895233060667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757604718845263488707111 4136407078267895233060667)
      ·
        refine ⟨6204610617401842849591001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136407078267895233060667 6204610617401842849591001)
        ·
          refine ⟨4653457963051382137193251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6204610617401842849591001 4653457963051382137193251)
          ·
            refine ⟨6980186944577073205789877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653457963051382137193251 6980186944577073205789877)
            ·
              refine ⟨654392526054100613042801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6980186944577073205789877 654392526054100613042801)
              ·
                refine ⟨490794394540575459782101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654392526054100613042801 490794394540575459782101)
                ·
                  refine ⟨11502993622044737338643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 490794394540575459782101 11502993622044737338643)
                  ·
                    rfl

theorem cell22_100809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_100809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100809 prefixEnd_100809 := by exact prefixLift 100809
  have htrace : WordTrace (prefixWord ++ tailWord_100809) baseStart_100809 baseEnd_100809 := by
    simpa [prefixWord, tailWord_100809, baseEnd_100809] using wordTrace_append hprefix tailTrace_100809
  have hstable : (prefixWord ++ tailWord_100809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100809).length < 2 ^ (prefixWord ++ tailWord_100809).sum := by decide
  have hdescent : baseEnd_100809 < baseStart_100809 := by decide
  rcases family_descends (prefixWord ++ tailWord_100809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100826 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_100826 : Nat := 118140960795 + 100826 * 2 ^ 59
def prefixEnd_100826 : Nat := 4983230072969 + 3 ^ 40 * 100826 * 2
def baseEnd_100826 : Nat := 11504933437850611446959

theorem tailTrace_100826 : CollatzResearch.WordTrace tailWord_100826 prefixEnd_100826 11504933437850611446959 := by
  unfold tailWord_100826
  simp only [CollatzResearch.WordTrace]
  refine ⟨919356583183024138744583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2451617555154731036652221 919356583183024138744583)
  ·
    refine ⟨1379034874774536208116875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 919356583183024138744583 1379034874774536208116875)
    ·
      refine ⟨2068552312161804312175313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379034874774536208116875 2068552312161804312175313)
      ·
        refine ⟨1551414234121353234131485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2068552312161804312175313 1551414234121353234131485)
        ·
          refine ⟨581780337795507462799307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1551414234121353234131485 581780337795507462799307)
          ·
            refine ⟨872670506693261194198961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581780337795507462799307 872670506693261194198961)
            ·
              refine ⟨654502880019945895649221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872670506693261194198961 654502880019945895649221)
              ·
                refine ⟨122719290003739855434229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654502880019945895649221 122719290003739855434229)
                ·
                  refine ⟨11504933437850611446959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122719290003739855434229 11504933437850611446959)
                  ·
                    rfl

theorem cell22_100826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_100826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100826 prefixEnd_100826 := by exact prefixLift 100826
  have htrace : WordTrace (prefixWord ++ tailWord_100826) baseStart_100826 baseEnd_100826 := by
    simpa [prefixWord, tailWord_100826, baseEnd_100826] using wordTrace_append hprefix tailTrace_100826
  have hstable : (prefixWord ++ tailWord_100826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100826).length < 2 ^ (prefixWord ++ tailWord_100826).sum := by decide
  have hdescent : baseEnd_100826 < baseStart_100826 := by decide
  rcases family_descends (prefixWord ++ tailWord_100826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100856 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_100856 : Nat := 118140960795 + 100856 * 2 ^ 59
def prefixEnd_100856 : Nat := 4983230072969 + 3 ^ 40 * 100856 * 2
def baseEnd_100856 : Nat := 34525069926641756090785

theorem tailTrace_100856 : CollatzResearch.WordTrace tailWord_100856 prefixEnd_100856 34525069926641756090785 := by
  unfold tailWord_100856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839260261311705839285211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2452347015082274452380281 1839260261311705839285211)
  ·
    refine ⟨2758890391967558758927817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1839260261311705839285211 2758890391967558758927817)
    ·
      refine ⟨2069167793975669069195863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2758890391967558758927817 2069167793975669069195863)
      ·
        refine ⟨3103751690963503603793795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069167793975669069195863 3103751690963503603793795)
        ·
          refine ⟨4655627536445255405690693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103751690963503603793795 4655627536445255405690693)
          ·
            refine ⟨872930163083485388567005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4655627536445255405690693 872930163083485388567005)
            ·
              refine ⟨327348811156307020712627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872930163083485388567005 327348811156307020712627)
              ·
                refine ⟨491023216734460531068941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327348811156307020712627 491023216734460531068941)
                ·
                  refine ⟨184133706275422699150853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491023216734460531068941 184133706275422699150853)
                  ·
                    refine ⟨34525069926641756090785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184133706275422699150853 34525069926641756090785)
                    ·
                      rfl

theorem cell22_100856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_100856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100856 prefixEnd_100856 := by exact prefixLift 100856
  have htrace : WordTrace (prefixWord ++ tailWord_100856) baseStart_100856 baseEnd_100856 := by
    simpa [prefixWord, tailWord_100856, baseEnd_100856] using wordTrace_append hprefix tailTrace_100856
  have hstable : (prefixWord ++ tailWord_100856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100856).length < 2 ^ (prefixWord ++ tailWord_100856).sum := by decide
  have hdescent : baseEnd_100856 < baseStart_100856 := by decide
  rcases family_descends (prefixWord ++ tailWord_100856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100877 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 5]
def baseStart_100877 : Nat := 118140960795 + 100877 * 2 ^ 59
def prefixEnd_100877 : Nat := 4983230072969 + 3 ^ 40 * 100877 * 2
def baseEnd_100877 : Nat := 11510752885268233771907

theorem tailTrace_100877 : CollatzResearch.WordTrace tailWord_100877 prefixEnd_100877 11510752885268233771907 := by
  unfold tailWord_100877
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679286455547332265084885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2452857637031554843389923 3679286455547332265084885)
  ·
    refine ⟨86233276301890599962927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3679286455547332265084885 86233276301890599962927)
    ·
      refine ⟨129349914452835899944391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86233276301890599962927 129349914452835899944391)
      ·
        refine ⟨194024871679253849916587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129349914452835899944391 194024871679253849916587)
        ·
          refine ⟨291037307518880774874881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194024871679253849916587 291037307518880774874881)
          ·
            refine ⟨218277980639160581156161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291037307518880774874881 218277980639160581156161)
            ·
              refine ⟨163708485479370435867121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218277980639160581156161 163708485479370435867121)
              ·
                refine ⟨122781364109527826900341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163708485479370435867121 122781364109527826900341)
                ·
                  refine ⟨11510752885268233771907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122781364109527826900341 11510752885268233771907)
                  ·
                    rfl

theorem cell22_100877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_100877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100877 prefixEnd_100877 := by exact prefixLift 100877
  have htrace : WordTrace (prefixWord ++ tailWord_100877) baseStart_100877 baseEnd_100877 := by
    simpa [prefixWord, tailWord_100877, baseEnd_100877] using wordTrace_append hprefix tailTrace_100877
  have hstable : (prefixWord ++ tailWord_100877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100877).length < 2 ^ (prefixWord ++ tailWord_100877).sum := by decide
  have hdescent : baseEnd_100877 < baseStart_100877 := by decide
  rcases family_descends (prefixWord ++ tailWord_100877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100901 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_100901 : Nat := 118140960795 + 100901 * 2 ^ 59
def prefixEnd_100901 : Nat := 4983230072969 + 3 ^ 40 * 100901 * 2
def baseEnd_100901 : Nat := 34540474346276638715647

theorem tailTrace_100901 : CollatzResearch.WordTrace tailWord_100901 prefixEnd_100901 34540474346276638715647 := by
  unfold tailWord_100901
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680161807460384363958557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2453441204973589575972371 3680161807460384363958557)
  ·
    refine ⟨1380060677797644136484459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3680161807460384363958557 1380060677797644136484459)
    ·
      refine ⟨2070091016696466204726689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380060677797644136484459 2070091016696466204726689)
      ·
        refine ⟨1552568262522349653545017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070091016696466204726689 1552568262522349653545017)
        ·
          refine ⟨1164426196891762240158763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552568262522349653545017 1164426196891762240158763)
          ·
            refine ⟨1746639295337643360238145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164426196891762240158763 1746639295337643360238145)
            ·
              refine ⟨1309979471503232520178609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746639295337643360238145 1309979471503232520178609)
              ·
                refine ⟨982484603627424390133957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309979471503232520178609 982484603627424390133957)
                ·
                  refine ⟨184215863180142073150117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 982484603627424390133957 184215863180142073150117)
                  ·
                    refine ⟨34540474346276638715647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184215863180142073150117 34540474346276638715647)
                    ·
                      rfl

theorem cell22_100901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_100901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_100901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_100901 prefixEnd_100901 := by exact prefixLift 100901
  have htrace : WordTrace (prefixWord ++ tailWord_100901) baseStart_100901 baseEnd_100901 := by
    simpa [prefixWord, tailWord_100901, baseEnd_100901] using wordTrace_append hprefix tailTrace_100901
  have hstable : (prefixWord ++ tailWord_100901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100901).length < 2 ^ (prefixWord ++ tailWord_100901).sum := by decide
  have hdescent : baseEnd_100901 < baseStart_100901 := by decide
  rcases family_descends (prefixWord ++ tailWord_100901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101012 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 5]
def baseStart_101012 : Nat := 118140960795 + 101012 * 2 ^ 59
def prefixEnd_101012 : Nat := 4983230072969 + 3 ^ 40 * 101012 * 2
def baseEnd_101012 : Nat := 11526157304903116396769

theorem tailTrace_101012 : CollatzResearch.WordTrace tailWord_101012 prefixEnd_101012 11526157304903116396769 := by
  unfold tailWord_101012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842105155029125160624645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2456140206705500214166193 1842105155029125160624645)
  ·
    refine ⟨345394716567960967617121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1842105155029125160624645 345394716567960967617121)
    ·
      refine ⟨259046037425970725712841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345394716567960967617121 259046037425970725712841)
      ·
        refine ⟨194284528069478044284631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259046037425970725712841 194284528069478044284631)
        ·
          refine ⟨291426792104217066426947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194284528069478044284631 291426792104217066426947)
          ·
            refine ⟨437140188156325599640421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291426792104217066426947 437140188156325599640421)
            ·
              refine ⟨81963785279311049932579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 437140188156325599640421 81963785279311049932579)
              ·
                refine ⟨122945677918966574898869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81963785279311049932579 122945677918966574898869)
                ·
                  refine ⟨11526157304903116396769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122945677918966574898869 11526157304903116396769)
                  ·
                    rfl

theorem cell22_101012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_101012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101012 prefixEnd_101012 := by exact prefixLift 101012
  have htrace : WordTrace (prefixWord ++ tailWord_101012) baseStart_101012 baseEnd_101012 := by
    simpa [prefixWord, tailWord_101012, baseEnd_101012] using wordTrace_append hprefix tailTrace_101012
  have hstable : (prefixWord ++ tailWord_101012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101012).length < 2 ^ (prefixWord ++ tailWord_101012).sum := by decide
  have hdescent : baseEnd_101012 < baseStart_101012 := by decide
  rcases family_descends (prefixWord ++ tailWord_101012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101025 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_101025 : Nat := 118140960795 + 101025 * 2 ^ 59
def prefixEnd_101025 : Nat := 4983230072969 + 3 ^ 40 * 101025 * 2
def baseEnd_101025 : Nat := 34582922080381648615267

theorem tailTrace_101025 : CollatzResearch.WordTrace tailWord_101025 prefixEnd_101025 34582922080381648615267 := by
  unfold tailWord_101025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3684684459011153541472529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2456456306007435694315019 3684684459011153541472529)
  ·
    refine ⟨2763513344258365156104397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3684684459011153541472529 2763513344258365156104397)
    ·
      refine ⟨1036317504096886933539149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2763513344258365156104397 1036317504096886933539149)
      ·
        refine ⟨388619064036332600077181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1036317504096886933539149 388619064036332600077181)
        ·
          refine ⟨145732149013624725028943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388619064036332600077181 145732149013624725028943)
          ·
            refine ⟨218598223520437087543415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145732149013624725028943 218598223520437087543415)
            ·
              refine ⟨327897335280655631315123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218598223520437087543415 327897335280655631315123)
              ·
                refine ⟨491846002920983446972685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327897335280655631315123 491846002920983446972685)
                ·
                  refine ⟨184442251095368792614757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491846002920983446972685 184442251095368792614757)
                  ·
                    refine ⟨34582922080381648615267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184442251095368792614757 34582922080381648615267)
                    ·
                      rfl

theorem cell22_101025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_101025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101025 prefixEnd_101025 := by exact prefixLift 101025
  have htrace : WordTrace (prefixWord ++ tailWord_101025) baseStart_101025 baseEnd_101025 := by
    simpa [prefixWord, tailWord_101025, baseEnd_101025] using wordTrace_append hprefix tailTrace_101025
  have hstable : (prefixWord ++ tailWord_101025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101025).length < 2 ^ (prefixWord ++ tailWord_101025).sum := by decide
  have hdescent : baseEnd_101025 < baseStart_101025 := by decide
  rcases family_descends (prefixWord ++ tailWord_101025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101055 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 2, 3]
def baseStart_101055 : Nat := 118140960795 + 101055 * 2 ^ 59
def prefixEnd_101055 : Nat := 4983230072969 + 3 ^ 40 * 101055 * 2
def baseEnd_101055 : Nat := 34593191693471570365175

theorem tailTrace_101055 : CollatzResearch.WordTrace tailWord_101055 prefixEnd_101055 34593191693471570365175 := by
  unfold tailWord_101055
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685778648902468665064619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2457185765934979110043079 3685778648902468665064619)
  ·
    refine ⟨5528667973353702997596929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685778648902468665064619 5528667973353702997596929)
    ·
      refine ⟨4146500980015277248197697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5528667973353702997596929 4146500980015277248197697)
      ·
        refine ⟨3109875735011457936148273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4146500980015277248197697 3109875735011457936148273)
        ·
          refine ⟨2332406801258593452111205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109875735011457936148273 2332406801258593452111205)
          ·
            refine ⟨437326275235986272270851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2332406801258593452111205 437326275235986272270851)
            ·
              refine ⟨655989412853979408406277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437326275235986272270851 655989412853979408406277)
              ·
                refine ⟨122998014910121139076177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655989412853979408406277 122998014910121139076177)
                ·
                  refine ⟨92248511182590854307133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122998014910121139076177 92248511182590854307133)
                  ·
                    refine ⟨34593191693471570365175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92248511182590854307133 34593191693471570365175)
                    ·
                      rfl

theorem cell22_101055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_101055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101055 prefixEnd_101055 := by exact prefixLift 101055
  have htrace : WordTrace (prefixWord ++ tailWord_101055) baseStart_101055 baseEnd_101055 := by
    simpa [prefixWord, tailWord_101055, baseEnd_101055] using wordTrace_append hprefix tailTrace_101055
  have hstable : (prefixWord ++ tailWord_101055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101055).length < 2 ^ (prefixWord ++ tailWord_101055).sum := by decide
  have hdescent : baseEnd_101055 < baseStart_101055 := by decide
  rcases family_descends (prefixWord ++ tailWord_101055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101117 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_101117 : Nat := 118140960795 + 101117 * 2 ^ 59
def prefixEnd_101117 : Nat := 4983230072969 + 3 ^ 40 * 101117 * 2
def baseEnd_101117 : Nat := 34614415560524075314985

theorem tailTrace_101117 : CollatzResearch.WordTrace tailWord_101117 prefixEnd_101117 34614415560524075314985 := by
  unfold tailWord_101117
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688039974677853253821605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2458693316451902169214403 3688039974677853253821605)
  ·
    refine ⟨691507495252097485091551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3688039974677853253821605 691507495252097485091551)
    ·
      refine ⟨1037261242878146227637327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691507495252097485091551 1037261242878146227637327)
      ·
        refine ⟨1555891864317219341455991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037261242878146227637327 1555891864317219341455991)
        ·
          refine ⟨2333837796475829012183987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555891864317219341455991 2333837796475829012183987)
          ·
            refine ⟨3500756694713743518275981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333837796475829012183987 3500756694713743518275981)
            ·
              refine ⟨1312783760517653819353493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3500756694713743518275981 1312783760517653819353493)
              ·
                refine ⟨61536738774265022782195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1312783760517653819353493 61536738774265022782195)
                ·
                  refine ⟨92305108161397534173293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61536738774265022782195 92305108161397534173293)
                  ·
                    refine ⟨34614415560524075314985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92305108161397534173293 34614415560524075314985)
                    ·
                      rfl

theorem cell22_101117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_101117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101117 prefixEnd_101117 := by exact prefixLift 101117
  have htrace : WordTrace (prefixWord ++ tailWord_101117) baseStart_101117 baseEnd_101117 := by
    simpa [prefixWord, tailWord_101117, baseEnd_101117] using wordTrace_append hprefix tailTrace_101117
  have hstable : (prefixWord ++ tailWord_101117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101117).length < 2 ^ (prefixWord ++ tailWord_101117).sum := by decide
  have hdescent : baseEnd_101117 < baseStart_101117 := by decide
  rcases family_descends (prefixWord ++ tailWord_101117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101181 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 5]
def baseStart_101181 : Nat := 118140960795 + 101181 * 2 ^ 59
def prefixEnd_101181 : Nat := 4983230072969 + 3 ^ 40 * 101181 * 2
def baseEnd_101181 : Nat := 11545441356149747238263

theorem tailTrace_101181 : CollatzResearch.WordTrace tailWord_101181 prefixEnd_101181 11545441356149747238263 := by
  unfold tailWord_101181
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690374246445992184151397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2460249497630661456100931 3690374246445992184151397)
  ·
    refine ⟨691945171208623534528387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3690374246445992184151397 691945171208623534528387)
    ·
      refine ⟨1037917756812935301792581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691945171208623534528387 1037917756812935301792581)
      ·
        refine ⟨194609579402425369086109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1037917756812935301792581 194609579402425369086109)
        ·
          refine ⟨72978592275909513407291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194609579402425369086109 72978592275909513407291)
          ·
            refine ⟨109467888413864270110937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72978592275909513407291 109467888413864270110937)
            ·
              refine ⟨82100916310398202583203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109467888413864270110937 82100916310398202583203)
              ·
                refine ⟨123151374465597303874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82100916310398202583203 123151374465597303874805)
                ·
                  refine ⟨11545441356149747238263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123151374465597303874805 11545441356149747238263)
                  ·
                    rfl

theorem cell22_101181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_101181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101181 prefixEnd_101181 := by exact prefixLift 101181
  have htrace : WordTrace (prefixWord ++ tailWord_101181) baseStart_101181 baseEnd_101181 := by
    simpa [prefixWord, tailWord_101181, baseEnd_101181] using wordTrace_append hprefix tailTrace_101181
  have hstable : (prefixWord ++ tailWord_101181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101181).length < 2 ^ (prefixWord ++ tailWord_101181).sum := by decide
  have hdescent : baseEnd_101181 < baseStart_101181 := by decide
  rcases family_descends (prefixWord ++ tailWord_101181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101224 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 2, 3]
def baseStart_101224 : Nat := 118140960795 + 101224 * 2 ^ 59
def prefixEnd_101224 : Nat := 4983230072969 + 3 ^ 40 * 101224 * 2
def baseEnd_101224 : Nat := 34651043847211462889657

theorem tailTrace_101224 : CollatzResearch.WordTrace tailWord_101224 prefixEnd_101224 34651043847211462889657 := by
  unfold tailWord_101224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1845971292645105263983363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2461295056860140351977817 1845971292645105263983363)
  ·
    refine ⟨2768956938967657895975045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1845971292645105263983363 2768956938967657895975045)
    ·
      refine ⟨519179426056435855495321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2768956938967657895975045 519179426056435855495321)
      ·
        refine ⟨389384569542326891621491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519179426056435855495321 389384569542326891621491)
        ·
          refine ⟨584076854313490337432237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389384569542326891621491 584076854313490337432237)
          ·
            refine ⟨219028820367558876537089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 584076854313490337432237 219028820367558876537089)
            ·
              refine ⟨164271615275669157402817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219028820367558876537089 164271615275669157402817)
              ·
                refine ⟨123203711456751868052113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164271615275669157402817 123203711456751868052113)
                ·
                  refine ⟨92402783592563901039085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123203711456751868052113 92402783592563901039085)
                  ·
                    refine ⟨34651043847211462889657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92402783592563901039085 34651043847211462889657)
                    ·
                      rfl

theorem cell22_101224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_101224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101224 prefixEnd_101224 := by exact prefixLift 101224
  have htrace : WordTrace (prefixWord ++ tailWord_101224) baseStart_101224 baseEnd_101224 := by
    simpa [prefixWord, tailWord_101224, baseEnd_101224] using wordTrace_append hprefix tailTrace_101224
  have hstable : (prefixWord ++ tailWord_101224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101224).length < 2 ^ (prefixWord ++ tailWord_101224).sum := by decide
  have hdescent : baseEnd_101224 < baseStart_101224 := by decide
  rcases family_descends (prefixWord ++ tailWord_101224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101237 : List Nat := [1, 3, 4, 1, 1, 4, 1, 7]
def baseStart_101237 : Nat := 118140960795 + 101237 * 2 ^ 59
def prefixEnd_101237 : Nat := 4983230072969 + 3 ^ 40 * 101237 * 2
def baseEnd_101237 : Nat := 3850610445875973590513

theorem tailTrace_101237 : CollatzResearch.WordTrace tailWord_101237 prefixEnd_101237 3850610445875973590513 := by
  unfold tailWord_101237
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692416734243113748189965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2461611156162075832126643 3692416734243113748189965)
  ·
    refine ⟨1384656275341167655571237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3692416734243113748189965 1384656275341167655571237)
    ·
      refine ⟨259623051626468935419607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1384656275341167655571237 259623051626468935419607)
      ·
        refine ⟨389434577439703403129411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259623051626468935419607 389434577439703403129411)
        ·
          refine ⟨584151866159555104694117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389434577439703403129411 584151866159555104694117)
          ·
            refine ⟨109528474904916582130147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 584151866159555104694117 109528474904916582130147)
            ·
              refine ⟨164292712357374873195221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109528474904916582130147 164292712357374873195221)
              ·
                refine ⟨3850610445875973590513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 164292712357374873195221 3850610445875973590513)
                ·
                  rfl

theorem cell22_101237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 7].length) (baseStart_101237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101237 prefixEnd_101237 := by exact prefixLift 101237
  have htrace : WordTrace (prefixWord ++ tailWord_101237) baseStart_101237 baseEnd_101237 := by
    simpa [prefixWord, tailWord_101237, baseEnd_101237] using wordTrace_append hprefix tailTrace_101237
  have hstable : (prefixWord ++ tailWord_101237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101237).length < 2 ^ (prefixWord ++ tailWord_101237).sum := by decide
  have hdescent : baseEnd_101237 < baseStart_101237 := by decide
  rcases family_descends (prefixWord ++ tailWord_101237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101269 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_101269 : Nat := 118140960795 + 101269 * 2 ^ 59
def prefixEnd_101269 : Nat := 4983230072969 + 3 ^ 40 * 101269 * 2
def baseEnd_101269 : Nat := 34666448266846345514519

theorem tailTrace_101269 : CollatzResearch.WordTrace tailWord_101269 prefixEnd_101269 34666448266846345514519 := by
  unfold tailWord_101269
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693583870127183213354861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2462389246751455475569907 3693583870127183213354861)
  ·
    refine ⟨1385093951297693705008073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3693583870127183213354861 1385093951297693705008073)
    ·
      refine ⟨1038820463473270278756055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1385093951297693705008073 1038820463473270278756055)
      ·
        refine ⟨1558230695209905418134083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038820463473270278756055 1558230695209905418134083)
        ·
          refine ⟨2337346042814858127201125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558230695209905418134083 2337346042814858127201125)
          ·
            refine ⟨438252383027785898850211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2337346042814858127201125 438252383027785898850211)
            ·
              refine ⟨657378574541678848275317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438252383027785898850211 657378574541678848275317)
              ·
                refine ⟨61629241363282392025811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 657378574541678848275317 61629241363282392025811)
                ·
                  refine ⟨92443862044923588038717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61629241363282392025811 92443862044923588038717)
                  ·
                    refine ⟨34666448266846345514519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92443862044923588038717 34666448266846345514519)
                    ·
                      rfl

theorem cell22_101269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_101269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101269 prefixEnd_101269 := by exact prefixLift 101269
  have htrace : WordTrace (prefixWord ++ tailWord_101269) baseStart_101269 baseEnd_101269 := by
    simpa [prefixWord, tailWord_101269, baseEnd_101269] using wordTrace_append hprefix tailTrace_101269
  have hstable : (prefixWord ++ tailWord_101269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101269).length < 2 ^ (prefixWord ++ tailWord_101269).sum := by decide
  have hdescent : baseEnd_101269 < baseStart_101269 := by decide
  rcases family_descends (prefixWord ++ tailWord_101269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101280 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_101280 : Nat := 118140960795 + 101280 * 2 ^ 59
def prefixEnd_101280 : Nat := 4983230072969 + 3 ^ 40 * 101280 * 2
def baseEnd_101280 : Nat := 34670213791645983489485

theorem tailTrace_101280 : CollatzResearch.WordTrace tailWord_101280 prefixEnd_101280 34670213791645983489485 := by
  unfold tailWord_101280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846992536543666046002647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2462656715391554728003529 1846992536543666046002647)
  ·
    refine ⟨2770488804815499069003971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1846992536543666046002647 2770488804815499069003971)
    ·
      refine ⟨4155733207223248603505957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2770488804815499069003971 4155733207223248603505957)
      ·
        refine ⟨779199976354359113157367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4155733207223248603505957 779199976354359113157367)
        ·
          refine ⟨1168799964531538669736051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779199976354359113157367 1168799964531538669736051)
          ·
            refine ⟨1753199946797308004604077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168799964531538669736051 1753199946797308004604077)
            ·
              refine ⟨657449980048990501726529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1753199946797308004604077 657449980048990501726529)
              ·
                refine ⟨493087485036742876294897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657449980048990501726529 493087485036742876294897)
                ·
                  refine ⟨369815613777557157221173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493087485036742876294897 369815613777557157221173)
                  ·
                    refine ⟨34670213791645983489485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 369815613777557157221173 34670213791645983489485)
                    ·
                      rfl

theorem cell22_101280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_101280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101280 prefixEnd_101280 := by exact prefixLift 101280
  have htrace : WordTrace (prefixWord ++ tailWord_101280) baseStart_101280 baseEnd_101280 := by
    simpa [prefixWord, tailWord_101280, baseEnd_101280] using wordTrace_append hprefix tailTrace_101280
  have hstable : (prefixWord ++ tailWord_101280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101280).length < 2 ^ (prefixWord ++ tailWord_101280).sum := by decide
  have hdescent : baseEnd_101280 < baseStart_101280 := by decide
  rcases family_descends (prefixWord ++ tailWord_101280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101282 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_101282 : Nat := 118140960795 + 101282 * 2 ^ 59
def prefixEnd_101282 : Nat := 4983230072969 + 3 ^ 40 * 101282 * 2
def baseEnd_101282 : Nat := 11556966144172881646493

theorem tailTrace_101282 : CollatzResearch.WordTrace tailWord_101282 prefixEnd_101282 11556966144172881646493 := by
  unfold tailWord_101282
  simp only [CollatzResearch.WordTrace]
  refine ⟨923514504770021608394525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2462705346053390955718733 923514504770021608394525)
  ·
    refine ⟨346317939288758103147947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 923514504770021608394525 346317939288758103147947)
    ·
      refine ⟨519476908933137154721921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346317939288758103147947 519476908933137154721921)
      ·
        refine ⟨389607681699852866041441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519476908933137154721921 389607681699852866041441)
        ·
          refine ⟨292205761274889649531081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389607681699852866041441 292205761274889649531081)
          ·
            refine ⟨219154320956167237148311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292205761274889649531081 219154320956167237148311)
            ·
              refine ⟨328731481434250855722467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219154320956167237148311 328731481434250855722467)
              ·
                refine ⟨493097222151376283583701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328731481434250855722467 493097222151376283583701)
                ·
                  refine ⟨11556966144172881646493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 493097222151376283583701 11556966144172881646493)
                  ·
                    rfl

theorem cell22_101282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_101282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101282 prefixEnd_101282 := by exact prefixLift 101282
  have htrace : WordTrace (prefixWord ++ tailWord_101282) baseStart_101282 baseEnd_101282 := by
    simpa [prefixWord, tailWord_101282, baseEnd_101282] using wordTrace_append hprefix tailTrace_101282
  have hstable : (prefixWord ++ tailWord_101282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101282).length < 2 ^ (prefixWord ++ tailWord_101282).sum := by decide
  have hdescent : baseEnd_101282 < baseStart_101282 := by decide
  rcases family_descends (prefixWord ++ tailWord_101282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101295 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 3, 4]
def baseStart_101295 : Nat := 118140960795 + 101295 * 2 ^ 59
def prefixEnd_101295 : Nat := 4983230072969 + 3 ^ 40 * 101295 * 2
def baseEnd_101295 : Nat := 34675348598190944364439

theorem tailTrace_101295 : CollatzResearch.WordTrace tailWord_101295 prefixEnd_101295 34675348598190944364439 := by
  unfold tailWord_101295
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694532168032989653801339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2463021445355326435867559 3694532168032989653801339)
  ·
    refine ⟨5541798252049484480702009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3694532168032989653801339 5541798252049484480702009)
    ·
      refine ⟨4156348689037113360526507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5541798252049484480702009 4156348689037113360526507)
      ·
        refine ⟨6234523033555670040789761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156348689037113360526507 6234523033555670040789761)
        ·
          refine ⟨4675892275166752530592321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6234523033555670040789761 4675892275166752530592321)
          ·
            refine ⟨3506919206375064397944241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4675892275166752530592321 3506919206375064397944241)
            ·
              refine ⟨2630189404781298298458181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506919206375064397944241 2630189404781298298458181)
              ·
                refine ⟨493160513396493430960909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2630189404781298298458181 493160513396493430960909)
                ·
                  refine ⟨184935192523685036610341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 493160513396493430960909 184935192523685036610341)
                  ·
                    refine ⟨34675348598190944364439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184935192523685036610341 34675348598190944364439)
                    ·
                      rfl

theorem cell22_101295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_101295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101295 prefixEnd_101295 := by exact prefixLift 101295
  have htrace : WordTrace (prefixWord ++ tailWord_101295) baseStart_101295 baseEnd_101295 := by
    simpa [prefixWord, tailWord_101295, baseEnd_101295] using wordTrace_append hprefix tailTrace_101295
  have hstable : (prefixWord ++ tailWord_101295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101295).length < 2 ^ (prefixWord ++ tailWord_101295).sum := by decide
  have hdescent : baseEnd_101295 < baseStart_101295 := by decide
  rcases family_descends (prefixWord ++ tailWord_101295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101312 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_101312 : Nat := 118140960795 + 101312 * 2 ^ 59
def prefixEnd_101312 : Nat := 4983230072969 + 3 ^ 40 * 101312 * 2
def baseEnd_101312 : Nat := 34681168045608566689387

theorem tailTrace_101312 : CollatzResearch.WordTrace tailWord_101312 prefixEnd_101312 34681168045608566689387 := by
  unfold tailWord_101312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847576104485700778585095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2463434805980934371446793 1847576104485700778585095)
  ·
    refine ⟨2771364156728551167877643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1847576104485700778585095 2771364156728551167877643)
    ·
      refine ⟨4157046235092826751816465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771364156728551167877643 4157046235092826751816465)
      ·
        refine ⟨3117784676319620063862349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157046235092826751816465 3117784676319620063862349)
        ·
          refine ⟨1169169253619857523948381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3117784676319620063862349 1169169253619857523948381)
          ·
            refine ⟨438438470107446571480643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169169253619857523948381 438438470107446571480643)
            ·
              refine ⟨657657705161169857220965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438438470107446571480643 657657705161169857220965)
              ·
                refine ⟨123310819717719348228931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 657657705161169857220965 123310819717719348228931)
                ·
                  refine ⟨184966229576579022343397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123310819717719348228931 184966229576579022343397)
                  ·
                    refine ⟨34681168045608566689387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184966229576579022343397 34681168045608566689387)
                    ·
                      rfl

theorem cell22_101312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_101312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101312 prefixEnd_101312 := by exact prefixLift 101312
  have htrace : WordTrace (prefixWord ++ tailWord_101312) baseStart_101312 baseEnd_101312 := by
    simpa [prefixWord, tailWord_101312, baseEnd_101312] using wordTrace_append hprefix tailTrace_101312
  have hstable : (prefixWord ++ tailWord_101312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101312).length < 2 ^ (prefixWord ++ tailWord_101312).sum := by decide
  have hdescent : baseEnd_101312 < baseStart_101312 := by decide
  rcases family_descends (prefixWord ++ tailWord_101312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101359 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 2, 3]
def baseStart_101359 : Nat := 118140960795 + 101359 * 2 ^ 59
def prefixEnd_101359 : Nat := 4983230072969 + 3 ^ 40 * 101359 * 2
def baseEnd_101359 : Nat := 34697257106116110764243

theorem tailTrace_101359 : CollatzResearch.WordTrace tailWord_101359 prefixEnd_101359 34697257106116110764243 := by
  unfold tailWord_101359
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696866439801128584131131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2464577626534085722754087 3696866439801128584131131)
  ·
    refine ⟨5545299659701692876196697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3696866439801128584131131 5545299659701692876196697)
    ·
      refine ⟨4158974744776269657147523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5545299659701692876196697 4158974744776269657147523)
      ·
        refine ⟨6238462117164404485721285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4158974744776269657147523 6238462117164404485721285)
        ·
          refine ⟨1169711646968325841072741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6238462117164404485721285 1169711646968325841072741)
          ·
            refine ⟨219320933806561095201139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1169711646968325841072741 219320933806561095201139)
            ·
              refine ⟨328981400709841642801709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219320933806561095201139 328981400709841642801709)
              ·
                refine ⟨123368025266190616050641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328981400709841642801709 123368025266190616050641)
                ·
                  refine ⟨92526018949642962037981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123368025266190616050641 92526018949642962037981)
                  ·
                    refine ⟨34697257106116110764243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92526018949642962037981 34697257106116110764243)
                    ·
                      rfl

theorem cell22_101359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_101359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101359 prefixEnd_101359 := by exact prefixLift 101359
  have htrace : WordTrace (prefixWord ++ tailWord_101359) baseStart_101359 baseEnd_101359 := by
    simpa [prefixWord, tailWord_101359, baseEnd_101359] using wordTrace_append hprefix tailTrace_101359
  have hstable : (prefixWord ++ tailWord_101359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101359).length < 2 ^ (prefixWord ++ tailWord_101359).sum := by decide
  have hdescent : baseEnd_101359 < baseStart_101359 := by decide
  rcases family_descends (prefixWord ++ tailWord_101359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101370 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_101370 : Nat := 118140960795 + 101370 * 2 ^ 59
def prefixEnd_101370 : Nat := 4983230072969 + 3 ^ 40 * 101370 * 2
def baseEnd_101370 : Nat := 34701022630915748739209

theorem tailTrace_101370 : CollatzResearch.WordTrace tailWord_101370 prefixEnd_101370 34701022630915748739209 := by
  unfold tailWord_101370
  simp only [CollatzResearch.WordTrace]
  refine ⟨924316910690319365695391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2464845095174184975187709 924316910690319365695391)
  ·
    refine ⟨1386475366035479048543087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924316910690319365695391 1386475366035479048543087)
    ·
      refine ⟨2079713049053218572814631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386475366035479048543087 2079713049053218572814631)
      ·
        refine ⟨3119569573579827859221947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079713049053218572814631 3119569573579827859221947)
        ·
          refine ⟨4679354360369741788832921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119569573579827859221947 4679354360369741788832921)
          ·
            refine ⟨3509515770277306341624691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4679354360369741788832921 3509515770277306341624691)
            ·
              refine ⟨5264273655415959512437037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3509515770277306341624691 5264273655415959512437037)
              ·
                refine ⟨1974102620780984817163889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5264273655415959512437037 1974102620780984817163889)
                ·
                  refine ⟨1480576965585738612872917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974102620780984817163889 1480576965585738612872917)
                  ·
                    refine ⟨34701022630915748739209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1480576965585738612872917 34701022630915748739209)
                    ·
                      rfl

theorem cell22_101370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_101370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101370 prefixEnd_101370 := by exact prefixLift 101370
  have htrace : WordTrace (prefixWord ++ tailWord_101370) baseStart_101370 baseEnd_101370 := by
    simpa [prefixWord, tailWord_101370, baseEnd_101370] using wordTrace_append hprefix tailTrace_101370
  have hstable : (prefixWord ++ tailWord_101370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101370).length < 2 ^ (prefixWord ++ tailWord_101370).sum := by decide
  have hdescent : baseEnd_101370 < baseStart_101370 := by decide
  rcases family_descends (prefixWord ++ tailWord_101370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101385 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_101385 : Nat := 118140960795 + 101385 * 2 ^ 59
def prefixEnd_101385 : Nat := 4983230072969 + 3 ^ 40 * 101385 * 2
def baseEnd_101385 : Nat := 34706157437460709614163

theorem tailTrace_101385 : CollatzResearch.WordTrace tailWord_101385 prefixEnd_101385 34706157437460709614163 := by
  unfold tailWord_101385
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697814737706935024577609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2465209825137956683051739 3697814737706935024577609)
  ·
    refine ⟨2773361053280201268433207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3697814737706935024577609 2773361053280201268433207)
    ·
      refine ⟨4160041579920301902649811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773361053280201268433207 4160041579920301902649811)
      ·
        refine ⟨6240062369880452853974717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160041579920301902649811 6240062369880452853974717)
        ·
          refine ⟨2340023388705169820240519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6240062369880452853974717 2340023388705169820240519)
          ·
            refine ⟨3510035083057754730360779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340023388705169820240519 3510035083057754730360779)
            ·
              refine ⟨5265052624586632095541169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510035083057754730360779 5265052624586632095541169)
              ·
                refine ⟨3948789468439974071655877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265052624586632095541169 3948789468439974071655877)
                ·
                  refine ⟨740398025332495138435477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3948789468439974071655877 740398025332495138435477)
                  ·
                    refine ⟨34706157437460709614163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 740398025332495138435477 34706157437460709614163)
                    ·
                      rfl

theorem cell22_101385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_101385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101385 prefixEnd_101385 := by exact prefixLift 101385
  have htrace : WordTrace (prefixWord ++ tailWord_101385) baseStart_101385 baseEnd_101385 := by
    simpa [prefixWord, tailWord_101385, baseEnd_101385] using wordTrace_append hprefix tailTrace_101385
  have hstable : (prefixWord ++ tailWord_101385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101385).length < 2 ^ (prefixWord ++ tailWord_101385).sum := by decide
  have hdescent : baseEnd_101385 < baseStart_101385 := by decide
  rcases family_descends (prefixWord ++ tailWord_101385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101438 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_101438 : Nat := 118140960795 + 101438 * 2 ^ 59
def prefixEnd_101438 : Nat := 4983230072969 + 3 ^ 40 * 101438 * 2
def baseEnd_101438 : Nat := 34724300420586238039001

theorem tailTrace_101438 : CollatzResearch.WordTrace tailWord_101438 prefixEnd_101438 34724300420586238039001 := by
  unfold tailWord_101438
  simp only [CollatzResearch.WordTrace]
  refine ⟨462468475814365634532121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2466498537676616717504645 462468475814365634532121)
  ·
    refine ⟨346851356860774225899091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 462468475814365634532121 346851356860774225899091)
    ·
      refine ⟨520277035291161338848637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346851356860774225899091 520277035291161338848637)
      ·
        refine ⟨195103888234185502068239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 520277035291161338848637 195103888234185502068239)
        ·
          refine ⟨292655832351278253102359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195103888234185502068239 292655832351278253102359)
          ·
            refine ⟨438983748526917379653539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292655832351278253102359 438983748526917379653539)
            ·
              refine ⟨658475622790376069480309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438983748526917379653539 658475622790376069480309)
              ·
                refine ⟨61732089636597756513779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 658475622790376069480309 61732089636597756513779)
                ·
                  refine ⟨92598134454896634770669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61732089636597756513779 92598134454896634770669)
                  ·
                    refine ⟨34724300420586238039001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92598134454896634770669 34724300420586238039001)
                    ·
                      rfl

theorem cell22_101438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_101438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101438 prefixEnd_101438 := by exact prefixLift 101438
  have htrace : WordTrace (prefixWord ++ tailWord_101438) baseStart_101438 baseEnd_101438 := by
    simpa [prefixWord, tailWord_101438, baseEnd_101438] using wordTrace_append hprefix tailTrace_101438
  have hstable : (prefixWord ++ tailWord_101438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101438).length < 2 ^ (prefixWord ++ tailWord_101438).sum := by decide
  have hdescent : baseEnd_101438 < baseStart_101438 := by decide
  rcases family_descends (prefixWord ++ tailWord_101438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101494 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_101494 : Nat := 118140960795 + 101494 * 2 ^ 59
def prefixEnd_101494 : Nat := 4983230072969 + 3 ^ 40 * 101494 * 2
def baseEnd_101494 : Nat := 34743470365020758638829

theorem tailTrace_101494 : CollatzResearch.WordTrace tailWord_101494 prefixEnd_101494 34743470365020758638829 := by
  unfold tailWord_101494
  simp only [CollatzResearch.WordTrace]
  refine ⟨231361893394502915018471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2467860196208031093530357 231361893394502915018471)
  ·
    refine ⟨347042840091754372527707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231361893394502915018471 347042840091754372527707)
    ·
      refine ⟨520564260137631558791561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347042840091754372527707 520564260137631558791561)
      ·
        refine ⟨390423195103223669093671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520564260137631558791561 390423195103223669093671)
        ·
          refine ⟨585634792654835503640507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390423195103223669093671 585634792654835503640507)
          ·
            refine ⟨878452188982253255460761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585634792654835503640507 878452188982253255460761)
            ·
              refine ⟨658839141736689941595571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878452188982253255460761 658839141736689941595571)
              ·
                refine ⟨988258712605034912393357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658839141736689941595571 988258712605034912393357)
                ·
                  refine ⟨370597017226888092147509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988258712605034912393357 370597017226888092147509)
                  ·
                    refine ⟨34743470365020758638829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 370597017226888092147509 34743470365020758638829)
                    ·
                      rfl

theorem cell22_101494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_101494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101494 prefixEnd_101494 := by exact prefixLift 101494
  have htrace : WordTrace (prefixWord ++ tailWord_101494) baseStart_101494 baseEnd_101494 := by
    simpa [prefixWord, tailWord_101494, baseEnd_101494] using wordTrace_append hprefix tailTrace_101494
  have hstable : (prefixWord ++ tailWord_101494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101494).length < 2 ^ (prefixWord ++ tailWord_101494).sum := by decide
  have hdescent : baseEnd_101494 < baseStart_101494 := by decide
  rcases family_descends (prefixWord ++ tailWord_101494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101528 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 2, 3]
def baseStart_101528 : Nat := 118140960795 + 101528 * 2 ^ 59
def prefixEnd_101528 : Nat := 4983230072969 + 3 ^ 40 * 101528 * 2
def baseEnd_101528 : Nat := 34755109259856003288725

theorem tailTrace_101528 : CollatzResearch.WordTrace tailWord_101528 prefixEnd_101528 34755109259856003288725 := by
  unfold tailWord_101528
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851515188094435223516619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2468686917459246964688825 1851515188094435223516619)
  ·
    refine ⟨2777272782141652835274929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1851515188094435223516619 2777272782141652835274929)
    ·
      refine ⟨2082954586606239626456197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2777272782141652835274929 2082954586606239626456197)
      ·
        refine ⟨390553984988669929960537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2082954586606239626456197 390553984988669929960537)
        ·
          refine ⟨292915488741502447470403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390553984988669929960537 292915488741502447470403)
          ·
            refine ⟨439373233112253671205605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292915488741502447470403 439373233112253671205605)
            ·
              refine ⟨82382481208547563351051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439373233112253671205605 82382481208547563351051)
              ·
                refine ⟨123573721812821345026577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82382481208547563351051 123573721812821345026577)
                ·
                  refine ⟨92680291359616008769933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123573721812821345026577 92680291359616008769933)
                  ·
                    refine ⟨34755109259856003288725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92680291359616008769933 34755109259856003288725)
                    ·
                      rfl

theorem cell22_101528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_101528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101528 prefixEnd_101528 := by exact prefixLift 101528
  have htrace : WordTrace (prefixWord ++ tailWord_101528) baseStart_101528 baseEnd_101528 := by
    simpa [prefixWord, tailWord_101528, baseEnd_101528] using wordTrace_append hprefix tailTrace_101528
  have hstable : (prefixWord ++ tailWord_101528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101528).length < 2 ^ (prefixWord ++ tailWord_101528).sum := by decide
  have hdescent : baseEnd_101528 < baseStart_101528 := by decide
  rcases family_descends (prefixWord ++ tailWord_101528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101539 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 3, 3]
def baseStart_101539 : Nat := 118140960795 + 101539 * 2 ^ 59
def prefixEnd_101539 : Nat := 4983230072969 + 3 ^ 40 * 101539 * 2
def baseEnd_101539 : Nat := 34758874784655641263691

theorem tailTrace_101539 : CollatzResearch.WordTrace tailWord_101539 prefixEnd_101539 34758874784655641263691 := by
  unfold tailWord_101539
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703431579149019325683671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2468954386099346217122447 3703431579149019325683671)
  ·
    refine ⟨5555147368723528988525507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703431579149019325683671 5555147368723528988525507)
    ·
      refine ⟨8332721053085293482788261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555147368723528988525507 8332721053085293482788261)
      ·
        refine ⟨1562385197453492528022799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8332721053085293482788261 1562385197453492528022799)
        ·
          refine ⟨2343577796180238792034199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562385197453492528022799 2343577796180238792034199)
          ·
            refine ⟨3515366694270358188051299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343577796180238792034199 3515366694270358188051299)
            ·
              refine ⟨5273050041405537282076949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515366694270358188051299 5273050041405537282076949)
              ·
                refine ⟨247174220690884560097357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5273050041405537282076949 247174220690884560097357)
                ·
                  refine ⟨92690332759081710036509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247174220690884560097357 92690332759081710036509)
                  ·
                    refine ⟨34758874784655641263691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92690332759081710036509 34758874784655641263691)
                    ·
                      rfl

theorem cell22_101539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 3].length) (baseStart_101539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101539 prefixEnd_101539 := by exact prefixLift 101539
  have htrace : WordTrace (prefixWord ++ tailWord_101539) baseStart_101539 baseEnd_101539 := by
    simpa [prefixWord, tailWord_101539, baseEnd_101539] using wordTrace_append hprefix tailTrace_101539
  have hstable : (prefixWord ++ tailWord_101539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101539).length < 2 ^ (prefixWord ++ tailWord_101539).sum := by decide
  have hdescent : baseEnd_101539 < baseStart_101539 := by decide
  rcases family_descends (prefixWord ++ tailWord_101539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101558 : List Nat := [5, 1, 3, 2, 2, 9]
def baseStart_101558 : Nat := 118140960795 + 101558 * 2 ^ 59
def prefixEnd_101558 : Nat := 4983230072969 + 3 ^ 40 * 101558 * 2
def baseEnd_101558 : Nat := 429202208307974383193

theorem tailTrace_101558 : CollatzResearch.WordTrace tailWord_101558 prefixEnd_101558 429202208307974383193 := by
  unfold tailWord_101558
  simp only [CollatzResearch.WordTrace]
  refine ⟨231507785380011598164083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2469416377386790380416885 231507785380011598164083)
  ·
    refine ⟨347261678070017397246125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231507785380011598164083 347261678070017397246125)
    ·
      refine ⟨130223129276256523967297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347261678070017397246125 130223129276256523967297)
      ·
        refine ⟨97667346957192392975473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130223129276256523967297 97667346957192392975473)
        ·
          refine ⟨73250510217894294731605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97667346957192392975473 73250510217894294731605)
          ·
            refine ⟨429202208307974383193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 73250510217894294731605 429202208307974383193)
            ·
              rfl

theorem cell22_101558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 9].length) (baseStart_101558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101558 prefixEnd_101558 := by exact prefixLift 101558
  have htrace : WordTrace (prefixWord ++ tailWord_101558) baseStart_101558 baseEnd_101558 := by
    simpa [prefixWord, tailWord_101558, baseEnd_101558] using wordTrace_append hprefix tailTrace_101558
  have hstable : (prefixWord ++ tailWord_101558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101558).length < 2 ^ (prefixWord ++ tailWord_101558).sum := by decide
  have hdescent : baseEnd_101558 < baseStart_101558 := by decide
  rcases family_descends (prefixWord ++ tailWord_101558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101590 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_101590 : Nat := 118140960795 + 101590 * 2 ^ 59
def prefixEnd_101590 : Nat := 4983230072969 + 3 ^ 40 * 101590 * 2
def baseEnd_101590 : Nat := 34776333126908508238535

theorem tailTrace_101590 : CollatzResearch.WordTrace tailWord_101590 prefixEnd_101590 34776333126908508238535 := by
  unfold tailWord_101590
  simp only [CollatzResearch.WordTrace]
  refine ⟨231580731372765939736889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2470194467976170023860149 231580731372765939736889)
  ·
    refine ⟨173685548529574454802667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231580731372765939736889 173685548529574454802667)
    ·
      refine ⟨260528322794361682204001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173685548529574454802667 260528322794361682204001)
      ·
        refine ⟨195396242095771261653001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260528322794361682204001 195396242095771261653001)
        ·
          refine ⟨146547181571828446239751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195396242095771261653001 146547181571828446239751)
          ·
            refine ⟨219820772357742669359627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146547181571828446239751 219820772357742669359627)
            ·
              refine ⟨329731158536614004039441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219820772357742669359627 329731158536614004039441)
              ·
                refine ⟨247298368902460503029581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329731158536614004039441 247298368902460503029581)
                ·
                  refine ⟨92736888338422688636093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247298368902460503029581 92736888338422688636093)
                  ·
                    refine ⟨34776333126908508238535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92736888338422688636093 34776333126908508238535)
                    ·
                      rfl

theorem cell22_101590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_101590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101590 prefixEnd_101590 := by exact prefixLift 101590
  have htrace : WordTrace (prefixWord ++ tailWord_101590) baseStart_101590 baseEnd_101590 := by
    simpa [prefixWord, tailWord_101590, baseEnd_101590] using wordTrace_append hprefix tailTrace_101590
  have hstable : (prefixWord ++ tailWord_101590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101590).length < 2 ^ (prefixWord ++ tailWord_101590).sum := by decide
  have hdescent : baseEnd_101590 < baseStart_101590 := by decide
  rcases family_descends (prefixWord ++ tailWord_101590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101599 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 3, 4]
def baseStart_101599 : Nat := 118140960795 + 101599 * 2 ^ 59
def prefixEnd_101599 : Nat := 4983230072969 + 3 ^ 40 * 101599 * 2
def baseEnd_101599 : Nat := 34779414010835484763507

theorem tailTrace_101599 : CollatzResearch.WordTrace tailWord_101599 prefixEnd_101599 34779414010835484763507 := by
  unfold tailWord_101599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705619958931649572867851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2470413305954433048578567 3705619958931649572867851)
  ·
    refine ⟨5558429938397474359301777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3705619958931649572867851 5558429938397474359301777)
    ·
      refine ⟨4168822453798105769476333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5558429938397474359301777 4168822453798105769476333)
      ·
        refine ⟨1563308420174289663553625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4168822453798105769476333 1563308420174289663553625)
        ·
          refine ⟨1172481315130717247665219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1563308420174289663553625 1172481315130717247665219)
          ·
            refine ⟨1758721972696075871497829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172481315130717247665219 1758721972696075871497829)
            ·
              refine ⟨329760369880514225905843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1758721972696075871497829 329760369880514225905843)
              ·
                refine ⟨494640554820771338858765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329760369880514225905843 494640554820771338858765)
                ·
                  refine ⟨185490208057789252072037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 494640554820771338858765 185490208057789252072037)
                  ·
                    refine ⟨34779414010835484763507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185490208057789252072037 34779414010835484763507)
                    ·
                      rfl

theorem cell22_101599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_101599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101599 prefixEnd_101599 := by exact prefixLift 101599
  have htrace : WordTrace (prefixWord ++ tailWord_101599) baseStart_101599 baseEnd_101599 := by
    simpa [prefixWord, tailWord_101599, baseEnd_101599] using wordTrace_append hprefix tailTrace_101599
  have hstable : (prefixWord ++ tailWord_101599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101599).length < 2 ^ (prefixWord ++ tailWord_101599).sum := by decide
  have hdescent : baseEnd_101599 < baseStart_101599 := by decide
  rcases family_descends (prefixWord ++ tailWord_101599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101620 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 7]
def baseStart_101620 : Nat := 118140960795 + 101620 * 2 ^ 59
def prefixEnd_101620 : Nat := 4983230072969 + 3 ^ 40 * 101620 * 2
def baseEnd_101620 : Nat := 11595534246666143329481

theorem tailTrace_101620 : CollatzResearch.WordTrace tailWord_101620 prefixEnd_101620 11595534246666143329481 := by
  unfold tailWord_101620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853192945927785079691157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2470923927903713439588209 1853192945927785079691157)
  ·
    refine ⟨86868419340364925610523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1853192945927785079691157 86868419340364925610523)
    ·
      refine ⟨130302629010547388415785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86868419340364925610523 130302629010547388415785)
      ·
        refine ⟨97726971757910541311839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130302629010547388415785 97726971757910541311839)
        ·
          refine ⟨146590457636865811967759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97726971757910541311839 146590457636865811967759)
          ·
            refine ⟨219885686455298717951639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146590457636865811967759 219885686455298717951639)
            ·
              refine ⟨329828529682948076927459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219885686455298717951639 329828529682948076927459)
              ·
                refine ⟨494742794524422115391189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329828529682948076927459 494742794524422115391189)
                ·
                  refine ⟨11595534246666143329481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 494742794524422115391189 11595534246666143329481)
                  ·
                    rfl

theorem cell22_101620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_101620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101620 prefixEnd_101620 := by exact prefixLift 101620
  have htrace : WordTrace (prefixWord ++ tailWord_101620) baseStart_101620 baseEnd_101620 := by
    simpa [prefixWord, tailWord_101620, baseEnd_101620] using wordTrace_append hprefix tailTrace_101620
  have hstable : (prefixWord ++ tailWord_101620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101620).length < 2 ^ (prefixWord ++ tailWord_101620).sum := by decide
  have hdescent : baseEnd_101620 < baseStart_101620 := by decide
  rcases family_descends (prefixWord ++ tailWord_101620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101631 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 4]
def baseStart_101631 : Nat := 118140960795 + 101631 * 2 ^ 59
def prefixEnd_101631 : Nat := 4983230072969 + 3 ^ 40 * 101631 * 2
def baseEnd_101631 : Nat := 11596789421599355987803

theorem tailTrace_101631 : CollatzResearch.WordTrace tailWord_101631 prefixEnd_101631 11596789421599355987803 := by
  unfold tailWord_101631
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706787094815719038032747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2471191396543812692021831 3706787094815719038032747)
  ·
    refine ⟨5560180642223578557049121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3706787094815719038032747 5560180642223578557049121)
    ·
      refine ⟨4170135481667683917786841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5560180642223578557049121 4170135481667683917786841)
      ·
        refine ⟨3127601611250762938340131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4170135481667683917786841 3127601611250762938340131)
        ·
          refine ⟨4691402416876144407510197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127601611250762938340131 4691402416876144407510197)
          ·
            refine ⟨439818976582138538204081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4691402416876144407510197 439818976582138538204081)
            ·
              refine ⟨329864232436603903653061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439818976582138538204081 329864232436603903653061)
              ·
                refine ⟨61849543581863231934949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329864232436603903653061 61849543581863231934949)
                ·
                  refine ⟨11596789421599355987803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61849543581863231934949 11596789421599355987803)
                  ·
                    rfl

theorem cell22_101631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 4].length) (baseStart_101631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101631 prefixEnd_101631 := by exact prefixLift 101631
  have htrace : WordTrace (prefixWord ++ tailWord_101631) baseStart_101631 baseEnd_101631 := by
    simpa [prefixWord, tailWord_101631, baseEnd_101631] using wordTrace_append hprefix tailTrace_101631
  have hstable : (prefixWord ++ tailWord_101631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101631).length < 2 ^ (prefixWord ++ tailWord_101631).sum := by decide
  have hdescent : baseEnd_101631 < baseStart_101631 := by decide
  rcases family_descends (prefixWord ++ tailWord_101631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101644 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_101644 : Nat := 118140960795 + 101644 * 2 ^ 59
def prefixEnd_101644 : Nat := 4983230072969 + 3 ^ 40 * 101644 * 2
def baseEnd_101644 : Nat := 34794818430470367388369

theorem tailTrace_101644 : CollatzResearch.WordTrace tailWord_101644 prefixEnd_101644 34794818430470367388369 := by
  unfold tailWord_101644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853630621884311129127993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2471507495845748172170657 1853630621884311129127993)
  ·
    refine ⟨1390222966413233346845995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1853630621884311129127993 1390222966413233346845995)
    ·
      refine ⟨2085334449619850020268993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390222966413233346845995 2085334449619850020268993)
      ·
        refine ⟨1564000837214887515201745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085334449619850020268993 1564000837214887515201745)
        ·
          refine ⟨1173000627911165636401309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564000837214887515201745 1173000627911165636401309)
          ·
            refine ⟨439875235466687113650491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1173000627911165636401309 439875235466687113650491)
            ·
              refine ⟨659812853200030670475737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439875235466687113650491 659812853200030670475737)
              ·
                refine ⟨494859639900023002856803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659812853200030670475737 494859639900023002856803)
                ·
                  refine ⟨742289459850034504285205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494859639900023002856803 742289459850034504285205)
                  ·
                    refine ⟨34794818430470367388369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 742289459850034504285205 34794818430470367388369)
                    ·
                      rfl

theorem cell22_101644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_101644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101644 prefixEnd_101644 := by exact prefixLift 101644
  have htrace : WordTrace (prefixWord ++ tailWord_101644) baseStart_101644 baseEnd_101644 := by
    simpa [prefixWord, tailWord_101644, baseEnd_101644] using wordTrace_append hprefix tailTrace_101644
  have hstable : (prefixWord ++ tailWord_101644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101644).length < 2 ^ (prefixWord ++ tailWord_101644).sum := by decide
  have hdescent : baseEnd_101644 < baseStart_101644 := by decide
  rcases family_descends (prefixWord ++ tailWord_101644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101646 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_101646 : Nat := 118140960795 + 101646 * 2 ^ 59
def prefixEnd_101646 : Nat := 4983230072969 + 3 ^ 40 * 101646 * 2
def baseEnd_101646 : Nat := 34795503071343028838363

theorem tailTrace_101646 : CollatzResearch.WordTrace tailWord_101646 prefixEnd_101646 34795503071343028838363 := by
  unfold tailWord_101646
  simp only [CollatzResearch.WordTrace]
  refine ⟨463416773720172074978599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2471556126507584399885861 463416773720172074978599)
  ·
    refine ⟨695125160580258112467899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463416773720172074978599 695125160580258112467899)
    ·
      refine ⟨1042687740870387168701849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695125160580258112467899 1042687740870387168701849)
      ·
        refine ⟨782015805652790376526387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1042687740870387168701849 782015805652790376526387)
        ·
          refine ⟨1173023708479185564789581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782015805652790376526387 1173023708479185564789581)
          ·
            refine ⟨439883890679694586796093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1173023708479185564789581 439883890679694586796093)
            ·
              refine ⟨164956459004885470048535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439883890679694586796093 164956459004885470048535)
              ·
                refine ⟨247434688507328205072803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164956459004885470048535 247434688507328205072803)
                ·
                  refine ⟨371152032760992307609205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247434688507328205072803 371152032760992307609205)
                  ·
                    refine ⟨34795503071343028838363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 371152032760992307609205 34795503071343028838363)
                    ·
                      rfl

theorem cell22_101646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_101646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101646 prefixEnd_101646 := by exact prefixLift 101646
  have htrace : WordTrace (prefixWord ++ tailWord_101646) baseStart_101646 baseEnd_101646 := by
    simpa [prefixWord, tailWord_101646, baseEnd_101646] using wordTrace_append hprefix tailTrace_101646
  have hstable : (prefixWord ++ tailWord_101646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101646).length < 2 ^ (prefixWord ++ tailWord_101646).sum := by decide
  have hdescent : baseEnd_101646 < baseStart_101646 := by decide
  rcases family_descends (prefixWord ++ tailWord_101646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101661 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_101661 : Nat := 118140960795 + 101661 * 2 ^ 59
def prefixEnd_101661 : Nat := 4983230072969 + 3 ^ 40 * 101661 * 2
def baseEnd_101661 : Nat := 34800637877887989713317

theorem tailTrace_101661 : CollatzResearch.WordTrace tailWord_101661 prefixEnd_101661 34800637877887989713317 := by
  unfold tailWord_101661
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707881284707034161624837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2471920856471356107749891 3707881284707034161624837)
  ·
    refine ⟨695227740882568905304657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3707881284707034161624837 695227740882568905304657)
    ·
      refine ⟨521420805661926678978493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 695227740882568905304657 521420805661926678978493)
      ·
        refine ⟨195532802123222504616935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521420805661926678978493 195532802123222504616935)
        ·
          refine ⟨293299203184833756925403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195532802123222504616935 293299203184833756925403)
          ·
            refine ⟨439948804777250635388105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293299203184833756925403 439948804777250635388105)
            ·
              refine ⟨329961603582937976541079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439948804777250635388105 329961603582937976541079)
              ·
                refine ⟨494942405374406964811619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329961603582937976541079 494942405374406964811619)
                ·
                  refine ⟨742413608061610447217429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494942405374406964811619 742413608061610447217429)
                  ·
                    refine ⟨34800637877887989713317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 742413608061610447217429 34800637877887989713317)
                    ·
                      rfl

theorem cell22_101661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_101661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101661 prefixEnd_101661 := by exact prefixLift 101661
  have htrace : WordTrace (prefixWord ++ tailWord_101661) baseStart_101661 baseEnd_101661 := by
    simpa [prefixWord, tailWord_101661, baseEnd_101661] using wordTrace_append hprefix tailTrace_101661
  have hstable : (prefixWord ++ tailWord_101661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101661).length < 2 ^ (prefixWord ++ tailWord_101661).sum := by decide
  have hdescent : baseEnd_101661 < baseStart_101661 := by decide
  rcases family_descends (prefixWord ++ tailWord_101661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101693 : List Nat := [1, 4, 1, 5, 1, 1, 2, 7]
def baseStart_101693 : Nat := 118140960795 + 101693 * 2 ^ 59
def prefixEnd_101693 : Nat := 4983230072969 + 3 ^ 40 * 101693 * 2
def baseEnd_101693 : Nat := 3867954681316730323691

theorem tailTrace_101693 : CollatzResearch.WordTrace tailWord_101693 prefixEnd_101693 3867954681316730323691 := by
  unfold tailWord_101693
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709048420591103626789733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2472698947060735751193155 3709048420591103626789733)
  ·
    refine ⟨695446578860831930023075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3709048420591103626789733 695446578860831930023075)
    ·
      refine ⟨1043169868291247895034613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695446578860831930023075 1043169868291247895034613)
      ·
        refine ⟨97797175152304490159495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1043169868291247895034613 97797175152304490159495)
        ·
          refine ⟨146695762728456735239243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97797175152304490159495 146695762728456735239243)
          ·
            refine ⟨220043644092685102858865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146695762728456735239243 220043644092685102858865)
            ·
              refine ⟨165032733069513827144149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220043644092685102858865 165032733069513827144149)
              ·
                refine ⟨3867954681316730323691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165032733069513827144149 3867954681316730323691)
                ·
                  rfl

theorem cell22_101693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 7].length) (baseStart_101693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101693 prefixEnd_101693 := by exact prefixLift 101693
  have htrace : WordTrace (prefixWord ++ tailWord_101693) baseStart_101693 baseEnd_101693 := by
    simpa [prefixWord, tailWord_101693, baseEnd_101693] using wordTrace_append hprefix tailTrace_101693
  have hstable : (prefixWord ++ tailWord_101693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101693).length < 2 ^ (prefixWord ++ tailWord_101693).sum := by decide
  have hdescent : baseEnd_101693 < baseStart_101693 := by decide
  rcases family_descends (prefixWord ++ tailWord_101693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101697 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 2, 3]
def baseStart_101697 : Nat := 118140960795 + 101697 * 2 ^ 59
def prefixEnd_101697 : Nat := 4983230072969 + 3 ^ 40 * 101697 * 2
def baseEnd_101697 : Nat := 34812961413595895813207

theorem tailTrace_101697 : CollatzResearch.WordTrace tailWord_101697 prefixEnd_101697 34812961413595895813207 := by
  unfold tailWord_101697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709194312576612309935345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2472796208384408206623563 3709194312576612309935345)
  ·
    refine ⟨2781895734432459232451509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3709194312576612309935345 2781895734432459232451509)
    ·
      refine ⟨260802725103043053042329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2781895734432459232451509 260802725103043053042329)
      ·
        refine ⟨195602043827282289781747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260802725103043053042329 195602043827282289781747)
        ·
          refine ⟨293403065740923434672621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195602043827282289781747 293403065740923434672621)
          ·
            refine ⟨110026149652846288002233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293403065740923434672621 110026149652846288002233)
            ·
              refine ⟨82519612239634716001675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110026149652846288002233 82519612239634716001675)
              ·
                refine ⟨123779418359452074002513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82519612239634716001675 123779418359452074002513)
                ·
                  refine ⟨92834563769589055501885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123779418359452074002513 92834563769589055501885)
                  ·
                    refine ⟨34812961413595895813207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92834563769589055501885 34812961413595895813207)
                    ·
                      rfl

theorem cell22_101697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_101697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101697 prefixEnd_101697 := by exact prefixLift 101697
  have htrace : WordTrace (prefixWord ++ tailWord_101697) baseStart_101697 baseEnd_101697 := by
    simpa [prefixWord, tailWord_101697, baseEnd_101697] using wordTrace_append hprefix tailTrace_101697
  have hstable : (prefixWord ++ tailWord_101697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101697).length < 2 ^ (prefixWord ++ tailWord_101697).sum := by decide
  have hdescent : baseEnd_101697 < baseStart_101697 := by decide
  rcases family_descends (prefixWord ++ tailWord_101697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101781 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_101781 : Nat := 118140960795 + 101781 * 2 ^ 59
def prefixEnd_101781 : Nat := 4983230072969 + 3 ^ 40 * 101781 * 2
def baseEnd_101781 : Nat := 34841716330247676712949

theorem tailTrace_101781 : CollatzResearch.WordTrace tailWord_101781 prefixEnd_101781 34841716330247676712949 := by
  unfold tailWord_101781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712258044272294655993197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2474838696181529770662131 3712258044272294655993197)
  ·
    refine ⟨1392096766602110495997449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3712258044272294655993197 1392096766602110495997449)
    ·
      refine ⟨1044072574951582871998087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1392096766602110495997449 1044072574951582871998087)
      ·
        refine ⟨1566108862427374307997131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044072574951582871998087 1566108862427374307997131)
        ·
          refine ⟨2349163293641061461995697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566108862427374307997131 2349163293641061461995697)
          ·
            refine ⟨1761872470230796096496773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2349163293641061461995697 1761872470230796096496773)
            ·
              refine ⟨330351088168274268093145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1761872470230796096496773 330351088168274268093145)
              ·
                refine ⟨247763316126205701069859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330351088168274268093145 247763316126205701069859)
                ·
                  refine ⟨371644974189308551604789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247763316126205701069859 371644974189308551604789)
                  ·
                    refine ⟨34841716330247676712949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 371644974189308551604789 34841716330247676712949)
                    ·
                      rfl

theorem cell22_101781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_101781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101781 prefixEnd_101781 := by exact prefixLift 101781
  have htrace : WordTrace (prefixWord ++ tailWord_101781) baseStart_101781 baseEnd_101781 := by
    simpa [prefixWord, tailWord_101781, baseEnd_101781] using wordTrace_append hprefix tailTrace_101781
  have hstable : (prefixWord ++ tailWord_101781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101781).length < 2 ^ (prefixWord ++ tailWord_101781).sum := by decide
  have hdescent : baseEnd_101781 < baseStart_101781 := by decide
  rcases family_descends (prefixWord ++ tailWord_101781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101785 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 1, 4]
def baseStart_101785 : Nat := 118140960795 + 101785 * 2 ^ 59
def prefixEnd_101785 : Nat := 4983230072969 + 3 ^ 40 * 101785 * 2
def baseEnd_101785 : Nat := 34843085611992999612937

theorem tailTrace_101785 : CollatzResearch.WordTrace tailWord_101785 prefixEnd_101785 34843085611992999612937 := by
  unfold tailWord_101785
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712403936257803339138809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2474935957505202226092539 3712403936257803339138809)
  ·
    refine ⟨2784302952193352504354107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3712403936257803339138809 2784302952193352504354107)
    ·
      refine ⟨4176454428290028756531161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784302952193352504354107 4176454428290028756531161)
      ·
        refine ⟨3132340821217521567398371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4176454428290028756531161 3132340821217521567398371)
        ·
          refine ⟨4698511231826282351097557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132340821217521567398371 4698511231826282351097557)
          ·
            refine ⟨110121356995928492603849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4698511231826282351097557 110121356995928492603849)
            ·
              refine ⟨82591017746946369452887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110121356995928492603849 82591017746946369452887)
              ·
                refine ⟨123886526620419554179331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82591017746946369452887 123886526620419554179331)
                ·
                  refine ⟨185829789930629331268997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123886526620419554179331 185829789930629331268997)
                  ·
                    refine ⟨34843085611992999612937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185829789930629331268997 34843085611992999612937)
                    ·
                      rfl

theorem cell22_101785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_101785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101785 prefixEnd_101785 := by exact prefixLift 101785
  have htrace : WordTrace (prefixWord ++ tailWord_101785) baseStart_101785 baseEnd_101785 := by
    simpa [prefixWord, tailWord_101785, baseEnd_101785] using wordTrace_append hprefix tailTrace_101785
  have hstable : (prefixWord ++ tailWord_101785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101785).length < 2 ^ (prefixWord ++ tailWord_101785).sum := by decide
  have hdescent : baseEnd_101785 < baseStart_101785 := by decide
  rcases family_descends (prefixWord ++ tailWord_101785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101796 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_101796 : Nat := 118140960795 + 101796 * 2 ^ 59
def prefixEnd_101796 : Nat := 4983230072969 + 3 ^ 40 * 101796 * 2
def baseEnd_101796 : Nat := 34846851136792637587903

theorem tailTrace_101796 : CollatzResearch.WordTrace tailWord_101796 prefixEnd_101796 34846851136792637587903 := by
  unfold tailWord_101796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856402569608976108894621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2475203426145301478526161 1856402569608976108894621)
  ·
    refine ⟨696150963603366040835483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1856402569608976108894621 696150963603366040835483)
    ·
      refine ⟨1044226445405049061253225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696150963603366040835483 1044226445405049061253225)
      ·
        refine ⟨783169834053786795939919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044226445405049061253225 783169834053786795939919)
        ·
          refine ⟨1174754751080680193909879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783169834053786795939919 1174754751080680193909879)
          ·
            refine ⟨1762132126621020290864819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174754751080680193909879 1762132126621020290864819)
            ·
              refine ⟨2643198189931530436297229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762132126621020290864819 2643198189931530436297229)
              ·
                refine ⟨991199321224323913611461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2643198189931530436297229 991199321224323913611461)
                ·
                  refine ⟨185849872729560733802149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 991199321224323913611461 185849872729560733802149)
                  ·
                    refine ⟨34846851136792637587903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 185849872729560733802149 34846851136792637587903)
                    ·
                      rfl

theorem cell22_101796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_101796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101796 prefixEnd_101796 := by exact prefixLift 101796
  have htrace : WordTrace (prefixWord ++ tailWord_101796) baseStart_101796 baseEnd_101796 := by
    simpa [prefixWord, tailWord_101796, baseEnd_101796] using wordTrace_append hprefix tailTrace_101796
  have hstable : (prefixWord ++ tailWord_101796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101796).length < 2 ^ (prefixWord ++ tailWord_101796).sum := by decide
  have hdescent : baseEnd_101796 < baseStart_101796 := by decide
  rcases family_descends (prefixWord ++ tailWord_101796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101800 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_101800 : Nat := 118140960795 + 101800 * 2 ^ 59
def prefixEnd_101800 : Nat := 4983230072969 + 3 ^ 40 * 101800 * 2
def baseEnd_101800 : Nat := 11616073472845986829297

theorem tailTrace_101800 : CollatzResearch.WordTrace tailWord_101800 prefixEnd_101800 11616073472845986829297 := by
  unfold tailWord_101800
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856475515601730450467427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2475300687468973933956569 1856475515601730450467427)
  ·
    refine ⟨2784713273402595675701141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1856475515601730450467427 2784713273402595675701141)
    ·
      refine ⟨130533434690746672298491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2784713273402595675701141 130533434690746672298491)
      ·
        refine ⟨195800152036120008447737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130533434690746672298491 195800152036120008447737)
        ·
          refine ⟨146850114027090006335803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195800152036120008447737 146850114027090006335803)
          ·
            refine ⟨220275171040635009503705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146850114027090006335803 220275171040635009503705)
            ·
              refine ⟨165206378280476257127779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220275171040635009503705 165206378280476257127779)
              ·
                refine ⟨247809567420714385691669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165206378280476257127779 247809567420714385691669)
                ·
                  refine ⟨11616073472845986829297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247809567420714385691669 11616073472845986829297)
                  ·
                    rfl

theorem cell22_101800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_101800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101800 prefixEnd_101800 := by exact prefixLift 101800
  have htrace : WordTrace (prefixWord ++ tailWord_101800) baseStart_101800 baseEnd_101800 := by
    simpa [prefixWord, tailWord_101800, baseEnd_101800] using wordTrace_append hprefix tailTrace_101800
  have hstable : (prefixWord ++ tailWord_101800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101800).length < 2 ^ (prefixWord ++ tailWord_101800).sum := by decide
  have hdescent : baseEnd_101800 < baseStart_101800 := by decide
  rcases family_descends (prefixWord ++ tailWord_101800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101815 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 2, 3]
def baseStart_101815 : Nat := 118140960795 + 101815 * 2 ^ 59
def prefixEnd_101815 : Nat := 4983230072969 + 3 ^ 40 * 101815 * 2
def baseEnd_101815 : Nat := 34853355225082921362845

theorem tailTrace_101815 : CollatzResearch.WordTrace tailWord_101815 prefixEnd_101815 34853355225082921362845 := by
  unfold tailWord_101815
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713498126149118462730899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2475665417432745641820599 3713498126149118462730899)
  ·
    refine ⟨5570247189223677694096349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3713498126149118462730899 5570247189223677694096349)
    ·
      refine ⟨2088842695958879135286131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5570247189223677694096349 2088842695958879135286131)
      ·
        refine ⟨3133264043938318702929197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088842695958879135286131 3133264043938318702929197)
        ·
          refine ⟨1174974016476869513598449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3133264043938318702929197 1174974016476869513598449)
          ·
            refine ⟨881230512357652135198837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174974016476869513598449 881230512357652135198837)
            ·
              refine ⟨82615360533529887674891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 881230512357652135198837 82615360533529887674891)
              ·
                refine ⟨123923040800294831512337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82615360533529887674891 123923040800294831512337)
                ·
                  refine ⟨92942280600221123634253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123923040800294831512337 92942280600221123634253)
                  ·
                    refine ⟨34853355225082921362845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92942280600221123634253 34853355225082921362845)
                    ·
                      rfl

theorem cell22_101815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_101815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101815 prefixEnd_101815 := by exact prefixLift 101815
  have htrace : WordTrace (prefixWord ++ tailWord_101815) baseStart_101815 baseEnd_101815 := by
    simpa [prefixWord, tailWord_101815, baseEnd_101815] using wordTrace_append hprefix tailTrace_101815
  have hstable : (prefixWord ++ tailWord_101815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101815).length < 2 ^ (prefixWord ++ tailWord_101815).sum := by decide
  have hdescent : baseEnd_101815 < baseStart_101815 := by decide
  rcases family_descends (prefixWord ++ tailWord_101815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101828 : List Nat := [2, 3, 3, 2, 1, 2, 1, 8]
def baseStart_101828 : Nat := 118140960795 + 101828 * 2 ^ 59
def prefixEnd_101828 : Nat := 4983230072969 + 3 ^ 40 * 101828 * 2
def baseEnd_101828 : Nat := 3873089487861691198645

theorem tailTrace_101828 : CollatzResearch.WordTrace tailWord_101828 prefixEnd_101828 3873089487861691198645 := by
  unfold tailWord_101828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856986137551010841477069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2475981516734681121969425 1856986137551010841477069)
  ·
    refine ⟨696369801581629065553901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1856986137551010841477069 696369801581629065553901)
    ·
      refine ⟨261138675593110899582713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 696369801581629065553901 261138675593110899582713)
      ·
        refine ⟨195854006694833174687035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261138675593110899582713 195854006694833174687035)
        ·
          refine ⟨293781010042249762030553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195854006694833174687035 293781010042249762030553)
          ·
            refine ⟨220335757531687321522915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293781010042249762030553 220335757531687321522915)
            ·
              refine ⟨330503636297530982284373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220335757531687321522915 330503636297530982284373)
              ·
                refine ⟨3873089487861691198645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 330503636297530982284373 3873089487861691198645)
                ·
                  rfl

theorem cell22_101828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_101828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101828 prefixEnd_101828 := by exact prefixLift 101828
  have htrace : WordTrace (prefixWord ++ tailWord_101828) baseStart_101828 baseEnd_101828 := by
    simpa [prefixWord, tailWord_101828, baseEnd_101828] using wordTrace_append hprefix tailTrace_101828
  have hstable : (prefixWord ++ tailWord_101828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101828).length < 2 ^ (prefixWord ++ tailWord_101828).sum := by decide
  have hdescent : baseEnd_101828 < baseStart_101828 := by decide
  rcases family_descends (prefixWord ++ tailWord_101828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101860 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_101860 : Nat := 118140960795 + 101860 * 2 ^ 59
def prefixEnd_101860 : Nat := 4983230072969 + 3 ^ 40 * 101860 * 2
def baseEnd_101860 : Nat := 34868759644717803987707

theorem tailTrace_101860 : CollatzResearch.WordTrace tailWord_101860 prefixEnd_101860 34868759644717803987707 := by
  unfold tailWord_101860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857569705493045574059517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2476759607324060765412689 1857569705493045574059517)
  ·
    refine ⟨696588639559892090272319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1857569705493045574059517 696588639559892090272319)
    ·
      refine ⟨1044882959339838135408479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696588639559892090272319 1044882959339838135408479)
      ·
        refine ⟨1567324439009757203112719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044882959339838135408479 1567324439009757203112719)
        ·
          refine ⟨2350986658514635804669079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567324439009757203112719 2350986658514635804669079)
          ·
            refine ⟨3526479987771953707003619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350986658514635804669079 3526479987771953707003619)
            ·
              refine ⟨5289719981657930560505429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526479987771953707003619 5289719981657930560505429)
              ·
                refine ⟨61988906035053873755923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5289719981657930560505429 61988906035053873755923)
                ·
                  refine ⟨92983359052580810633885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61988906035053873755923 92983359052580810633885)
                  ·
                    refine ⟨34868759644717803987707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92983359052580810633885 34868759644717803987707)
                    ·
                      rfl

theorem cell22_101860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_101860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101860 prefixEnd_101860 := by exact prefixLift 101860
  have htrace : WordTrace (prefixWord ++ tailWord_101860) baseStart_101860 baseEnd_101860 := by
    simpa [prefixWord, tailWord_101860, baseEnd_101860] using wordTrace_append hprefix tailTrace_101860
  have hstable : (prefixWord ++ tailWord_101860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101860).length < 2 ^ (prefixWord ++ tailWord_101860).sum := by decide
  have hdescent : baseEnd_101860 < baseStart_101860 := by decide
  rcases family_descends (prefixWord ++ tailWord_101860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101871 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_101871 : Nat := 118140960795 + 101871 * 2 ^ 59
def prefixEnd_101871 : Nat := 4983230072969 + 3 ^ 40 * 101871 * 2
def baseEnd_101871 : Nat := 34872525169517441962673

theorem tailTrace_101871 : CollatzResearch.WordTrace tailWord_101871 prefixEnd_101871 34872525169517441962673 := by
  unfold tailWord_101871
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715540613946240026769467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2477027075964160017846311 3715540613946240026769467)
  ·
    refine ⟨5573310920919360040154201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715540613946240026769467 5573310920919360040154201)
    ·
      refine ⟨4179983190689520030115651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5573310920919360040154201 4179983190689520030115651)
      ·
        refine ⟨6269974786034280045173477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4179983190689520030115651 6269974786034280045173477)
        ·
          refine ⟨1175620272381427508470027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6269974786034280045173477 1175620272381427508470027)
          ·
            refine ⟨1763430408572141262705041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175620272381427508470027 1763430408572141262705041)
            ·
              refine ⟨1322572806429105947028781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763430408572141262705041 1322572806429105947028781)
              ·
                refine ⟨495964802410914730135793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1322572806429105947028781 495964802410914730135793)
                ·
                  refine ⟨371973601808186047601845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495964802410914730135793 371973601808186047601845)
                  ·
                    refine ⟨34872525169517441962673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 371973601808186047601845 34872525169517441962673)
                    ·
                      rfl

theorem cell22_101871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_101871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101871 prefixEnd_101871 := by exact prefixLift 101871
  have htrace : WordTrace (prefixWord ++ tailWord_101871) baseStart_101871 baseEnd_101871 := by
    simpa [prefixWord, tailWord_101871, baseEnd_101871] using wordTrace_append hprefix tailTrace_101871
  have hstable : (prefixWord ++ tailWord_101871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101871).length < 2 ^ (prefixWord ++ tailWord_101871).sum := by decide
  have hdescent : baseEnd_101871 < baseStart_101871 := by decide
  rcases family_descends (prefixWord ++ tailWord_101871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101873 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 5]
def baseStart_101873 : Nat := 118140960795 + 101873 * 2 ^ 59
def prefixEnd_101873 : Nat := 4983230072969 + 3 ^ 40 * 101873 * 2
def baseEnd_101873 : Nat := 11624403270130034470889

theorem tailTrace_101873 : CollatzResearch.WordTrace tailWord_101873 prefixEnd_101873 11624403270130034470889 := by
  unfold tailWord_101873
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715613559938994368342273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2477075706625996245561515 3715613559938994368342273)
  ·
    refine ⟨2786710169954245776256705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3715613559938994368342273 2786710169954245776256705)
    ·
      refine ⟨2090032627465684332192529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2786710169954245776256705 2090032627465684332192529)
      ·
        refine ⟨1567524470599263249144397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2090032627465684332192529 1567524470599263249144397)
        ·
          refine ⟨587821676474723718429149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1567524470599263249144397 587821676474723718429149)
          ·
            refine ⟨220433128678021394410931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 587821676474723718429149 220433128678021394410931)
            ·
              refine ⟨330649693017032091616397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220433128678021394410931 330649693017032091616397)
              ·
                refine ⟨123993634881387034356149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330649693017032091616397 123993634881387034356149)
                ·
                  refine ⟨11624403270130034470889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123993634881387034356149 11624403270130034470889)
                  ·
                    rfl

theorem cell22_101873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_101873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101873 prefixEnd_101873 := by exact prefixLift 101873
  have htrace : WordTrace (prefixWord ++ tailWord_101873) baseStart_101873 baseEnd_101873 := by
    simpa [prefixWord, tailWord_101873, baseEnd_101873] using wordTrace_append hprefix tailTrace_101873
  have hstable : (prefixWord ++ tailWord_101873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101873).length < 2 ^ (prefixWord ++ tailWord_101873).sum := by decide
  have hdescent : baseEnd_101873 < baseStart_101873 := by decide
  rcases family_descends (prefixWord ++ tailWord_101873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101961 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_101961 : Nat := 118140960795 + 101961 * 2 ^ 59
def prefixEnd_101961 : Nat := 4983230072969 + 3 ^ 40 * 101961 * 2
def baseEnd_101961 : Nat := 34903334008787207212397

theorem tailTrace_101961 : CollatzResearch.WordTrace tailWord_101961 prefixEnd_101961 34903334008787207212397 := by
  unfold tailWord_101961
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718823183620185397545737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2479215455746790265030491 3718823183620185397545737)
  ·
    refine ⟨2789117387715139048159303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3718823183620185397545737 2789117387715139048159303)
    ·
      refine ⟨4183676081572708572238955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789117387715139048159303 4183676081572708572238955)
      ·
        refine ⟨6275514122359062858358433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183676081572708572238955 6275514122359062858358433)
        ·
          refine ⟨4706635591769297143768825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6275514122359062858358433 4706635591769297143768825)
          ·
            refine ⟨3529976693826972857826619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4706635591769297143768825 3529976693826972857826619)
            ·
              refine ⟨5294965040740459286739929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529976693826972857826619 5294965040740459286739929)
              ·
                refine ⟨3971223780555344465054947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5294965040740459286739929 3971223780555344465054947)
                ·
                  refine ⟨5956835670833016697582421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971223780555344465054947 5956835670833016697582421)
                  ·
                    refine ⟨34903334008787207212397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 5956835670833016697582421 34903334008787207212397)
                    ·
                      rfl

theorem cell22_101961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_101961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101961 prefixEnd_101961 := by exact prefixLift 101961
  have htrace : WordTrace (prefixWord ++ tailWord_101961) baseStart_101961 baseEnd_101961 := by
    simpa [prefixWord, tailWord_101961, baseEnd_101961] using wordTrace_append hprefix tailTrace_101961
  have hstable : (prefixWord ++ tailWord_101961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101961).length < 2 ^ (prefixWord ++ tailWord_101961).sum := by decide
  have hdescent : baseEnd_101961 < baseStart_101961 := by decide
  rcases family_descends (prefixWord ++ tailWord_101961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101997 : List Nat := [1, 5, 1, 1, 4, 2, 2, 6]
def baseStart_101997 : Nat := 118140960795 + 101997 * 2 ^ 59
def prefixEnd_101997 : Nat := 4983230072969 + 3 ^ 40 * 101997 * 2
def baseEnd_101997 : Nat := 3879517504943901479143

theorem tailTrace_101997 : CollatzResearch.WordTrace tailWord_101997 prefixEnd_101997 3879517504943901479143 := by
  unfold tailWord_101997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720136211489763545856245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2480090807659842363904163 3720136211489763545856245)
  ·
    refine ⟨348762769827165332424023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3720136211489763545856245 348762769827165332424023)
    ·
      refine ⟨523144154740747998636035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348762769827165332424023 523144154740747998636035)
      ·
        refine ⟨784716232111121997954053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523144154740747998636035 784716232111121997954053)
        ·
          refine ⟨147134293520835374616385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 784716232111121997954053 147134293520835374616385)
          ·
            refine ⟨110350720140626530962289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147134293520835374616385 110350720140626530962289)
            ·
              refine ⟨82763040105469898221717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110350720140626530962289 82763040105469898221717)
              ·
                refine ⟨3879517504943901479143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82763040105469898221717 3879517504943901479143)
                ·
                  rfl

theorem cell22_101997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 6].length) (baseStart_101997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_101997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_101997 prefixEnd_101997 := by exact prefixLift 101997
  have htrace : WordTrace (prefixWord ++ tailWord_101997) baseStart_101997 baseEnd_101997 := by
    simpa [prefixWord, tailWord_101997, baseEnd_101997] using wordTrace_append hprefix tailTrace_101997
  have hstable : (prefixWord ++ tailWord_101997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101997).length < 2 ^ (prefixWord ++ tailWord_101997).sum := by decide
  have hdescent : baseEnd_101997 < baseStart_101997 := by decide
  rcases family_descends (prefixWord ++ tailWord_101997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102053 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 6]
def baseStart_102053 : Nat := 118140960795 + 102053 * 2 ^ 59
def prefixEnd_102053 : Nat := 4983230072969 + 3 ^ 40 * 102053 * 2
def baseEnd_102053 : Nat := 11644942496309877970705

theorem tailTrace_102053 : CollatzResearch.WordTrace tailWord_102053 prefixEnd_102053 11644942496309877970705 := by
  unfold tailWord_102053
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722178699286885109894813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2481452466191256739929875 3722178699286885109894813)
  ·
    refine ⟨1395817012232581916210555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3722178699286885109894813 1395817012232581916210555)
    ·
      refine ⟨2093725518348872874315833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395817012232581916210555 2093725518348872874315833)
      ·
        refine ⟨1570294138761654655736875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093725518348872874315833 1570294138761654655736875)
        ·
          refine ⟨2355441208142481983605313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570294138761654655736875 2355441208142481983605313)
          ·
            refine ⟨1766580906106861487703985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355441208142481983605313 1766580906106861487703985)
            ·
              refine ⟨1324935679580146115777989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766580906106861487703985 1324935679580146115777989)
              ·
                refine ⟨248425439921277396708373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1324935679580146115777989 248425439921277396708373)
                ·
                  refine ⟨11644942496309877970705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248425439921277396708373 11644942496309877970705)
                  ·
                    rfl

theorem cell22_102053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_102053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102053 prefixEnd_102053 := by exact prefixLift 102053
  have htrace : WordTrace (prefixWord ++ tailWord_102053) baseStart_102053 baseEnd_102053 := by
    simpa [prefixWord, tailWord_102053, baseEnd_102053] using wordTrace_append hprefix tailTrace_102053
  have hstable : (prefixWord ++ tailWord_102053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102053).length < 2 ^ (prefixWord ++ tailWord_102053).sum := by decide
  have hdescent : baseEnd_102053 < baseStart_102053 := by decide
  rcases family_descends (prefixWord ++ tailWord_102053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102128 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_102128 : Nat := 118140960795 + 102128 * 2 ^ 59
def prefixEnd_102128 : Nat := 4983230072969 + 3 ^ 40 * 102128 * 2
def baseEnd_102128 : Nat := 34960501521654438286885

theorem tailTrace_102128 : CollatzResearch.WordTrace tailWord_102128 prefixEnd_102128 34960501521654438286885 := by
  unfold tailWord_102128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862457087007586459437519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2483276116010115279250025 1862457087007586459437519)
  ·
    refine ⟨2793685630511379689156279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1862457087007586459437519 2793685630511379689156279)
    ·
      refine ⟨4190528445767069533734419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2793685630511379689156279 4190528445767069533734419)
      ·
        refine ⟨6285792668650604300601629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4190528445767069533734419 6285792668650604300601629)
        ·
          refine ⟨2357172250743976612725611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6285792668650604300601629 2357172250743976612725611)
          ·
            refine ⟨3535758376115964919088417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357172250743976612725611 3535758376115964919088417)
            ·
              refine ⟨2651818782086973689316313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535758376115964919088417 2651818782086973689316313)
              ·
                refine ⟨1988864086565230266987235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651818782086973689316313 1988864086565230266987235)
                ·
                  refine ⟨2983296129847845400480853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988864086565230266987235 2983296129847845400480853)
                  ·
                    refine ⟨34960501521654438286885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2983296129847845400480853 34960501521654438286885)
                    ·
                      rfl

theorem cell22_102128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_102128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102128 prefixEnd_102128 := by exact prefixLift 102128
  have htrace : WordTrace (prefixWord ++ tailWord_102128) baseStart_102128 baseEnd_102128 := by
    simpa [prefixWord, tailWord_102128, baseEnd_102128] using wordTrace_append hprefix tailTrace_102128
  have hstable : (prefixWord ++ tailWord_102128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102128).length < 2 ^ (prefixWord ++ tailWord_102128).sum := by decide
  have hdescent : baseEnd_102128 < baseStart_102128 := by decide
  rcases family_descends (prefixWord ++ tailWord_102128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102181 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_102181 : Nat := 118140960795 + 102181 * 2 ^ 59
def prefixEnd_102181 : Nat := 4983230072969 + 3 ^ 40 * 102181 * 2
def baseEnd_102181 : Nat := 34978644504779966711723

theorem tailTrace_102181 : CollatzResearch.WordTrace tailWord_102181 prefixEnd_102181 34978644504779966711723 := by
  unfold tailWord_102181
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726847242823162970554397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2484564828548775313702931 3726847242823162970554397)
  ·
    refine ⟨1397567716058686113957899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3726847242823162970554397 1397567716058686113957899)
    ·
      refine ⟨2096351574088029170936849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397567716058686113957899 2096351574088029170936849)
      ·
        refine ⟨1572263680566021878202637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2096351574088029170936849 1572263680566021878202637)
        ·
          refine ⟨589598880212258204325989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1572263680566021878202637 589598880212258204325989)
          ·
            refine ⟨110549790039798413311123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 589598880212258204325989 110549790039798413311123)
            ·
              refine ⟨165824685059697619966685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110549790039798413311123 165824685059697619966685)
              ·
                refine ⟨62184256897386607487507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165824685059697619966685 62184256897386607487507)
                ·
                  refine ⟨93276385346079911231261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62184256897386607487507 93276385346079911231261)
                  ·
                    refine ⟨34978644504779966711723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93276385346079911231261 34978644504779966711723)
                    ·
                      rfl

theorem cell22_102181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_102181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102181 prefixEnd_102181 := by exact prefixLift 102181
  have htrace : WordTrace (prefixWord ++ tailWord_102181) baseStart_102181 baseEnd_102181 := by
    simpa [prefixWord, tailWord_102181, baseEnd_102181] using wordTrace_append hprefix tailTrace_102181
  have hstable : (prefixWord ++ tailWord_102181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102181).length < 2 ^ (prefixWord ++ tailWord_102181).sum := by decide
  have hdescent : baseEnd_102181 < baseStart_102181 := by decide
  rcases family_descends (prefixWord ++ tailWord_102181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102252 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_102252 : Nat := 118140960795 + 102252 * 2 ^ 59
def prefixEnd_102252 : Nat := 4983230072969 + 3 ^ 40 * 102252 * 2
def baseEnd_102252 : Nat := 35002949255759448186505

theorem tailTrace_102252 : CollatzResearch.WordTrace tailWord_102252 prefixEnd_102252 35002949255759448186505 := by
  unfold tailWord_102252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864718412782971048194505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2486291217043961397592673 1864718412782971048194505)
  ·
    refine ⟨1398538809587228286145879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1864718412782971048194505 1398538809587228286145879)
    ·
      refine ⟨2097808214380842429218819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398538809587228286145879 2097808214380842429218819)
      ·
        refine ⟨3146712321571263643828229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097808214380842429218819 3146712321571263643828229)
        ·
          refine ⟨590008560294611933217793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3146712321571263643828229 590008560294611933217793)
          ·
            refine ⟨442506420220958949913345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590008560294611933217793 442506420220958949913345)
            ·
              refine ⟨331879815165719212435009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442506420220958949913345 331879815165719212435009)
              ·
                refine ⟨248909861374289409326257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331879815165719212435009 248909861374289409326257)
                ·
                  refine ⟨186682396030717056994693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248909861374289409326257 186682396030717056994693)
                  ·
                    refine ⟨35002949255759448186505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186682396030717056994693 35002949255759448186505)
                    ·
                      rfl

theorem cell22_102252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_102252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102252 prefixEnd_102252 := by exact prefixLift 102252
  have htrace : WordTrace (prefixWord ++ tailWord_102252) baseStart_102252 baseEnd_102252 := by
    simpa [prefixWord, tailWord_102252, baseEnd_102252] using wordTrace_append hprefix tailTrace_102252
  have hstable : (prefixWord ++ tailWord_102252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102252).length < 2 ^ (prefixWord ++ tailWord_102252).sum := by decide
  have hdescent : baseEnd_102252 < baseStart_102252 := by decide
  rcases family_descends (prefixWord ++ tailWord_102252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102329 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 5]
def baseStart_102329 : Nat := 118140960795 + 102329 * 2 ^ 59
def prefixEnd_102329 : Nat := 4983230072969 + 3 ^ 40 * 102329 * 2
def baseEnd_102329 : Nat := 11676435976452304670423

theorem tailTrace_102329 : CollatzResearch.WordTrace tailWord_102329 prefixEnd_102329 11676435976452304670423 := by
  unfold tailWord_102329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732245246286984246942041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2488163497524656164628027 3732245246286984246942041)
  ·
    refine ⟨2799183934715238185206531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3732245246286984246942041 2799183934715238185206531)
    ·
      refine ⟨4198775902072857277809797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799183934715238185206531 4198775902072857277809797)
      ·
        refine ⟨787270481638660739589337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4198775902072857277809797 787270481638660739589337)
        ·
          refine ⟨590452861228995554692003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787270481638660739589337 590452861228995554692003)
          ·
            refine ⟨885679291843493332038005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590452861228995554692003 885679291843493332038005)
            ·
              refine ⟨83032433610327499878563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 885679291843493332038005 83032433610327499878563)
              ·
                refine ⟨124548650415491249817845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83032433610327499878563 124548650415491249817845)
                ·
                  refine ⟨11676435976452304670423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124548650415491249817845 11676435976452304670423)
                  ·
                    rfl

theorem cell22_102329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_102329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102329 prefixEnd_102329 := by exact prefixLift 102329
  have htrace : WordTrace (prefixWord ++ tailWord_102329) baseStart_102329 baseEnd_102329 := by
    simpa [prefixWord, tailWord_102329, baseEnd_102329] using wordTrace_append hprefix tailTrace_102329
  have hstable : (prefixWord ++ tailWord_102329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102329).length < 2 ^ (prefixWord ++ tailWord_102329).sum := by decide
  have hdescent : baseEnd_102329 < baseStart_102329 := by decide
  rcases family_descends (prefixWord ++ tailWord_102329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102423 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 2, 3]
def baseStart_102423 : Nat := 118140960795 + 102423 * 2 ^ 59
def prefixEnd_102423 : Nat := 4983230072969 + 3 ^ 40 * 102423 * 2
def baseEnd_102423 : Nat := 35061486050372002160981

theorem tailTrace_102423 : CollatzResearch.WordTrace tailWord_102423 prefixEnd_102423 35061486050372002160981 := by
  unfold tailWord_102423
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735673707946438300863923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2490449138630958867242615 3735673707946438300863923)
  ·
    refine ⟨5603510561919657451295885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3735673707946438300863923 5603510561919657451295885)
    ·
      refine ⟨2101316460719871544235957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5603510561919657451295885 2101316460719871544235957)
      ·
        refine ⟨196998418192487957272121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2101316460719871544235957 196998418192487957272121)
        ·
          refine ⟨147748813644365967954091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196998418192487957272121 147748813644365967954091)
          ·
            refine ⟨221623220466548951931137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147748813644365967954091 221623220466548951931137)
            ·
              refine ⟨166217415349911713948353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221623220466548951931137 166217415349911713948353)
              ·
                refine ⟨124663061512433785461265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166217415349911713948353 124663061512433785461265)
                ·
                  refine ⟨93497296134325339095949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124663061512433785461265 93497296134325339095949)
                  ·
                    refine ⟨35061486050372002160981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93497296134325339095949 35061486050372002160981)
                    ·
                      rfl

theorem cell22_102423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_102423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102423 prefixEnd_102423 := by exact prefixLift 102423
  have htrace : WordTrace (prefixWord ++ tailWord_102423) baseStart_102423 baseEnd_102423 := by
    simpa [prefixWord, tailWord_102423, baseEnd_102423] using wordTrace_append hprefix tailTrace_102423
  have hstable : (prefixWord ++ tailWord_102423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102423).length < 2 ^ (prefixWord ++ tailWord_102423).sum := by decide
  have hdescent : baseEnd_102423 < baseStart_102423 := by decide
  rcases family_descends (prefixWord ++ tailWord_102423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102436 : List Nat := [2, 3, 1, 4, 2, 2, 1, 7]
def baseStart_102436 : Nat := 118140960795 + 102436 * 2 ^ 59
def prefixEnd_102436 : Nat := 4983230072969 + 3 ^ 40 * 102436 * 2
def baseEnd_102436 : Nat := 3896215135116033509549

theorem tailTrace_102436 : CollatzResearch.WordTrace tailWord_102436 prefixEnd_102436 3896215135116033509549 := by
  unfold tailWord_102436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868073928449670760543581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2490765237932894347391441 1868073928449670760543581)
  ·
    refine ⟨700527723168626535203843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1868073928449670760543581 700527723168626535203843)
    ·
      refine ⟨1050791584752939802805765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700527723168626535203843 1050791584752939802805765)
      ·
        refine ⟨197023422141176213026081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1050791584752939802805765 197023422141176213026081)
        ·
          refine ⟨147767566605882159769561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197023422141176213026081 147767566605882159769561)
          ·
            refine ⟨110825674954411619827171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147767566605882159769561 110825674954411619827171)
            ·
              refine ⟨166238512431617429740757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110825674954411619827171 166238512431617429740757)
              ·
                refine ⟨3896215135116033509549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166238512431617429740757 3896215135116033509549)
                ·
                  rfl

theorem cell22_102436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 7].length) (baseStart_102436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102436 prefixEnd_102436 := by exact prefixLift 102436
  have htrace : WordTrace (prefixWord ++ tailWord_102436) baseStart_102436 baseEnd_102436 := by
    simpa [prefixWord, tailWord_102436, baseEnd_102436] using wordTrace_append hprefix tailTrace_102436
  have hstable : (prefixWord ++ tailWord_102436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102436).length < 2 ^ (prefixWord ++ tailWord_102436).sum := by decide
  have hdescent : baseEnd_102436 < baseStart_102436 := by decide
  rcases family_descends (prefixWord ++ tailWord_102436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102509 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 6]
def baseStart_102509 : Nat := 118140960795 + 102509 * 2 ^ 59
def prefixEnd_102509 : Nat := 4983230072969 + 3 ^ 40 * 102509 * 2
def baseEnd_102509 : Nat := 11696975202632148170239

theorem tailTrace_102509 : CollatzResearch.WordTrace tailWord_102509 prefixEnd_102509 11696975202632148170239 := by
  unfold tailWord_102509
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738810385634874988494581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2492540257089916658996387 3738810385634874988494581)
  ·
    refine ⟨350513473653269530171367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3738810385634874988494581 350513473653269530171367)
    ·
      refine ⟨525770210479904295257051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350513473653269530171367 525770210479904295257051)
      ·
        refine ⟨788655315719856442885577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525770210479904295257051 788655315719856442885577)
        ·
          refine ⟨591491486789892332164183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788655315719856442885577 591491486789892332164183)
          ·
            refine ⟨887237230184838498246275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591491486789892332164183 887237230184838498246275)
            ·
              refine ⟨1330855845277257747369413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887237230184838498246275 1330855845277257747369413)
              ·
                refine ⟨249535470989485827631765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1330855845277257747369413 249535470989485827631765)
                ·
                  refine ⟨11696975202632148170239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249535470989485827631765 11696975202632148170239)
                  ·
                    rfl

theorem cell22_102509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_102509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102509 prefixEnd_102509 := by exact prefixLift 102509
  have htrace : WordTrace (prefixWord ++ tailWord_102509) baseStart_102509 baseEnd_102509 := by
    simpa [prefixWord, tailWord_102509, baseEnd_102509] using wordTrace_append hprefix tailTrace_102509
  have hstable : (prefixWord ++ tailWord_102509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102509).length < 2 ^ (prefixWord ++ tailWord_102509).sum := by decide
  have hdescent : baseEnd_102509 < baseStart_102509 := by decide
  rcases family_descends (prefixWord ++ tailWord_102509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102511 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 1, 4]
def baseStart_102511 : Nat := 118140960795 + 102511 * 2 ^ 59
def prefixEnd_102511 : Nat := 4983230072969 + 3 ^ 40 * 102511 * 2
def baseEnd_102511 : Nat := 35091610248769105960711

theorem tailTrace_102511 : CollatzResearch.WordTrace tailWord_102511 prefixEnd_102511 35091610248769105960711 := by
  unfold tailWord_102511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738883331627629330067387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2492588887751752886711591 3738883331627629330067387)
  ·
    refine ⟨5608324997441443995101081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738883331627629330067387 5608324997441443995101081)
    ·
      refine ⟨4206243748081082996325811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5608324997441443995101081 4206243748081082996325811)
      ·
        refine ⟨6309365622121624494488717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4206243748081082996325811 6309365622121624494488717)
        ·
          refine ⟨2366012108295609185433269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6309365622121624494488717 2366012108295609185433269)
          ·
            refine ⟨221813635152713361134369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2366012108295609185433269 221813635152713361134369)
            ·
              refine ⟨166360226364535020850777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221813635152713361134369 166360226364535020850777)
              ·
                refine ⟨124770169773401265638083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166360226364535020850777 124770169773401265638083)
                ·
                  refine ⟨187155254660101898457125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124770169773401265638083 187155254660101898457125)
                  ·
                    refine ⟨35091610248769105960711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187155254660101898457125 35091610248769105960711)
                    ·
                      rfl

theorem cell22_102511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_102511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102511 prefixEnd_102511 := by exact prefixLift 102511
  have htrace : WordTrace (prefixWord ++ tailWord_102511) baseStart_102511 baseEnd_102511 := by
    simpa [prefixWord, tailWord_102511, baseEnd_102511] using wordTrace_append hprefix tailTrace_102511
  have hstable : (prefixWord ++ tailWord_102511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102511).length < 2 ^ (prefixWord ++ tailWord_102511).sum := by decide
  have hdescent : baseEnd_102511 < baseStart_102511 := by decide
  rcases family_descends (prefixWord ++ tailWord_102511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102573 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_102573 : Nat := 118140960795 + 102573 * 2 ^ 59
def prefixEnd_102573 : Nat := 4983230072969 + 3 ^ 40 * 102573 * 2
def baseEnd_102573 : Nat := 35112834115821610910521

theorem tailTrace_102573 : CollatzResearch.WordTrace tailWord_102573 prefixEnd_102573 35112834115821610910521 := by
  unfold tailWord_102573
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741144657403013918824373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2494096438268675945882915 3741144657403013918824373)
  ·
    refine ⟨350732311631532554889785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3741144657403013918824373 350732311631532554889785)
    ·
      refine ⟨263049233723649416167339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350732311631532554889785 263049233723649416167339)
      ·
        refine ⟨394573850585474124251009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263049233723649416167339 394573850585474124251009)
        ·
          refine ⟨295930387939105593188257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394573850585474124251009 295930387939105593188257)
          ·
            refine ⟨221947790954329194891193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295930387939105593188257 221947790954329194891193)
            ·
              refine ⟨166460843215746896168395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221947790954329194891193 166460843215746896168395)
              ·
                refine ⟨249691264823620344252593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166460843215746896168395 249691264823620344252593)
                ·
                  refine ⟨187268448617715258189445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249691264823620344252593 187268448617715258189445)
                  ·
                    refine ⟨35112834115821610910521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187268448617715258189445 35112834115821610910521)
                    ·
                      rfl

theorem cell22_102573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_102573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102573 prefixEnd_102573 := by exact prefixLift 102573
  have htrace : WordTrace (prefixWord ++ tailWord_102573) baseStart_102573 baseEnd_102573 := by
    simpa [prefixWord, tailWord_102573, baseEnd_102573] using wordTrace_append hprefix tailTrace_102573
  have hstable : (prefixWord ++ tailWord_102573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102573).length < 2 ^ (prefixWord ++ tailWord_102573).sum := by decide
  have hdescent : baseEnd_102573 < baseStart_102573 := by decide
  rcases family_descends (prefixWord ++ tailWord_102573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102594 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_102594 : Nat := 118140960795 + 102594 * 2 ^ 59
def prefixEnd_102594 : Nat := 4983230072969 + 3 ^ 40 * 102594 * 2
def baseEnd_102594 : Nat := 11706674281661518711819

theorem tailTrace_102594 : CollatzResearch.WordTrace tailWord_102594 prefixEnd_102594 11706674281661518711819 := by
  unfold tailWord_102594
  simp only [CollatzResearch.WordTrace]
  refine ⟨935477647581733626334709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2494607060217956336892557 935477647581733626334709)
  ·
    refine ⟨87701029460787527468879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 935477647581733626334709 87701029460787527468879)
    ·
      refine ⟨131551544191181291203319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87701029460787527468879 131551544191181291203319)
      ·
        refine ⟨197327316286771936804979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131551544191181291203319 197327316286771936804979)
        ·
          refine ⟨295990974430157905207469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197327316286771936804979 295990974430157905207469)
          ·
            refine ⟨110996615411309214452801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295990974430157905207469 110996615411309214452801)
            ·
              refine ⟨83247461558481910839601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110996615411309214452801 83247461558481910839601)
              ·
                refine ⟨62435596168861433129701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83247461558481910839601 62435596168861433129701)
                ·
                  refine ⟨11706674281661518711819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62435596168861433129701 11706674281661518711819)
                  ·
                    rfl

theorem cell22_102594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_102594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102594 prefixEnd_102594 := by exact prefixLift 102594
  have htrace : WordTrace (prefixWord ++ tailWord_102594) baseStart_102594 baseEnd_102594 := by
    simpa [prefixWord, tailWord_102594, baseEnd_102594] using wordTrace_append hprefix tailTrace_102594
  have hstable : (prefixWord ++ tailWord_102594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102594).length < 2 ^ (prefixWord ++ tailWord_102594).sum := by decide
  have hdescent : baseEnd_102594 < baseStart_102594 := by decide
  rcases family_descends (prefixWord ++ tailWord_102594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102603 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 1, 3]
def baseStart_102603 : Nat := 118140960795 + 102603 * 2 ^ 59
def prefixEnd_102603 : Nat := 4983230072969 + 3 ^ 40 * 102603 * 2
def baseEnd_102603 : Nat := 35123103728911532660429

theorem tailTrace_102603 : CollatzResearch.WordTrace tailWord_102603 prefixEnd_102603 35123103728911532660429 := by
  unfold tailWord_102603
  simp only [CollatzResearch.WordTrace]
  refine ⟨3742238847294329042416463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2494825898196219361610975 3742238847294329042416463)
  ·
    refine ⟨5613358270941493563624695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3742238847294329042416463 5613358270941493563624695)
    ·
      refine ⟨8420037406412240345437043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5613358270941493563624695 8420037406412240345437043)
      ·
        refine ⟨12630056109618360518155565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8420037406412240345437043 12630056109618360518155565)
        ·
          refine ⟨4736271041106885194308337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12630056109618360518155565 4736271041106885194308337)
          ·
            refine ⟨3552203280830163895731253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4736271041106885194308337 3552203280830163895731253)
            ·
              refine ⟨333019057577827865224805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3552203280830163895731253 333019057577827865224805)
              ·
                refine ⟨62441073295842724729651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333019057577827865224805 62441073295842724729651)
                ·
                  refine ⟨93661609943764087094477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62441073295842724729651 93661609943764087094477)
                  ·
                    refine ⟨35123103728911532660429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93661609943764087094477 35123103728911532660429)
                    ·
                      rfl

theorem cell22_102603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 3].length) (baseStart_102603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102603 prefixEnd_102603 := by exact prefixLift 102603
  have htrace : WordTrace (prefixWord ++ tailWord_102603) baseStart_102603 baseEnd_102603 := by
    simpa [prefixWord, tailWord_102603, baseEnd_102603] using wordTrace_append hprefix tailTrace_102603
  have hstable : (prefixWord ++ tailWord_102603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102603).length < 2 ^ (prefixWord ++ tailWord_102603).sum := by decide
  have hdescent : baseEnd_102603 < baseStart_102603 := by decide
  rcases family_descends (prefixWord ++ tailWord_102603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102616 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_102616 : Nat := 118140960795 + 102616 * 2 ^ 59
def prefixEnd_102616 : Nat := 4983230072969 + 3 ^ 40 * 102616 * 2
def baseEnd_102616 : Nat := 11709184631527944028463

theorem tailTrace_102616 : CollatzResearch.WordTrace tailWord_102616 prefixEnd_102616 11709184631527944028463 := by
  unfold tailWord_102616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871356498123616131319851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2495141997498154841759801 1871356498123616131319851)
  ·
    refine ⟨2807034747185424196979777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871356498123616131319851 2807034747185424196979777)
    ·
      refine ⟨2105276060389068147734833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2807034747185424196979777 2105276060389068147734833)
      ·
        refine ⟨1578957045291801110801125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105276060389068147734833 1578957045291801110801125)
        ·
          refine ⟨296054445992212708275211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1578957045291801110801125 296054445992212708275211)
          ·
            refine ⟨444081668988319062412817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296054445992212708275211 444081668988319062412817)
            ·
              refine ⟨333061251741239296809613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444081668988319062412817 333061251741239296809613)
              ·
                refine ⟨124897969402964736303605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333061251741239296809613 124897969402964736303605)
                ·
                  refine ⟨11709184631527944028463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124897969402964736303605 11709184631527944028463)
                  ·
                    rfl

theorem cell22_102616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_102616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102616 prefixEnd_102616 := by exact prefixLift 102616
  have htrace : WordTrace (prefixWord ++ tailWord_102616) baseStart_102616 baseEnd_102616 := by
    simpa [prefixWord, tailWord_102616, baseEnd_102616] using wordTrace_append hprefix tailTrace_102616
  have hstable : (prefixWord ++ tailWord_102616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102616).length < 2 ^ (prefixWord ++ tailWord_102616).sum := by decide
  have hdescent : baseEnd_102616 < baseStart_102616 := by decide
  rcases family_descends (prefixWord ++ tailWord_102616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102637 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_102637 : Nat := 118140960795 + 102637 * 2 ^ 59
def prefixEnd_102637 : Nat := 4983230072969 + 3 ^ 40 * 102637 * 2
def baseEnd_102637 : Nat := 35134742623746777310325

theorem tailTrace_102637 : CollatzResearch.WordTrace tailWord_102637 prefixEnd_102637 35134742623746777310325 := by
  unfold tailWord_102637
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743478929171152849154165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2495652619447435232769443 3743478929171152849154165)
  ·
    refine ⟨350951149609795579608203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3743478929171152849154165 350951149609795579608203)
    ·
      refine ⟨526426724414693369412305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350951149609795579608203 526426724414693369412305)
      ·
        refine ⟨394820043311020027059229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526426724414693369412305 394820043311020027059229)
        ·
          refine ⟨148057516241632510147211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394820043311020027059229 148057516241632510147211)
          ·
            refine ⟨222086274362448765220817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148057516241632510147211 222086274362448765220817)
            ·
              refine ⟨166564705771836573915613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222086274362448765220817 166564705771836573915613)
              ·
                refine ⟨62461764664438715218355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166564705771836573915613 62461764664438715218355)
                ·
                  refine ⟨93692646996658072827533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62461764664438715218355 93692646996658072827533)
                  ·
                    refine ⟨35134742623746777310325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93692646996658072827533 35134742623746777310325)
                    ·
                      rfl

theorem cell22_102637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_102637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102637 prefixEnd_102637 := by exact prefixLift 102637
  have htrace : WordTrace (prefixWord ++ tailWord_102637) baseStart_102637 baseEnd_102637 := by
    simpa [prefixWord, tailWord_102637, baseEnd_102637] using wordTrace_append hprefix tailTrace_102637
  have hstable : (prefixWord ++ tailWord_102637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102637).length < 2 ^ (prefixWord ++ tailWord_102637).sum := by decide
  have hdescent : baseEnd_102637 < baseStart_102637 := by decide
  rcases family_descends (prefixWord ++ tailWord_102637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102691 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 2, 4]
def baseStart_102691 : Nat := 118140960795 + 102691 * 2 ^ 59
def prefixEnd_102691 : Nat := 4983230072969 + 3 ^ 40 * 102691 * 2
def baseEnd_102691 : Nat := 35153227927308636460159

theorem tailTrace_102691 : CollatzResearch.WordTrace tailWord_102691 prefixEnd_102691 35153227927308636460159 := by
  unfold tailWord_102691
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745448470975520071619927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2496965647317013381079951 3745448470975520071619927)
  ·
    refine ⟨5618172706463280107429891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745448470975520071619927 5618172706463280107429891)
    ·
      refine ⟨8427259059694920161144837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618172706463280107429891 8427259059694920161144837)
      ·
        refine ⟨1580111073692797530214657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8427259059694920161144837 1580111073692797530214657)
        ·
          refine ⟨1185083305269598147660993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1580111073692797530214657 1185083305269598147660993)
          ·
            refine ⟨888812478952198610745745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185083305269598147660993 888812478952198610745745)
            ·
              refine ⟨666609359214148958059309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888812478952198610745745 666609359214148958059309)
              ·
                refine ⟨249978509705305859272241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666609359214148958059309 249978509705305859272241)
                ·
                  refine ⟨187483882278979394454181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249978509705305859272241 187483882278979394454181)
                  ·
                    refine ⟨35153227927308636460159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187483882278979394454181 35153227927308636460159)
                    ·
                      rfl

theorem cell22_102691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_102691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102691 prefixEnd_102691 := by exact prefixLift 102691
  have htrace : WordTrace (prefixWord ++ tailWord_102691) baseStart_102691 baseEnd_102691 := by
    simpa [prefixWord, tailWord_102691, baseEnd_102691] using wordTrace_append hprefix tailTrace_102691
  have hstable : (prefixWord ++ tailWord_102691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102691).length < 2 ^ (prefixWord ++ tailWord_102691).sum := by decide
  have hdescent : baseEnd_102691 < baseStart_102691 := by decide
  rcases family_descends (prefixWord ++ tailWord_102691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102708 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_102708 : Nat := 118140960795 + 102708 * 2 ^ 59
def prefixEnd_102708 : Nat := 4983230072969 + 3 ^ 40 * 102708 * 2
def baseEnd_102708 : Nat := 35159047374726258785107

theorem tailTrace_102708 : CollatzResearch.WordTrace tailWord_102708 prefixEnd_102708 35159047374726258785107 := by
  unfold tailWord_102708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873034255956965987494389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2497379007942621316659185 1873034255956965987494389)
  ·
    refine ⟨175596961495965561327599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1873034255956965987494389 175596961495965561327599)
    ·
      refine ⟨263395442243948341991399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175596961495965561327599 263395442243948341991399)
      ·
        refine ⟨395093163365922512987099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263395442243948341991399 395093163365922512987099)
        ·
          refine ⟨592639745048883769480649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395093163365922512987099 592639745048883769480649)
          ·
            refine ⟨444479808786662827110487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592639745048883769480649 444479808786662827110487)
            ·
              refine ⟨666719713179994240665731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444479808786662827110487 666719713179994240665731)
              ·
                refine ⟨1000079569769991360998597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666719713179994240665731 1000079569769991360998597)
                ·
                  refine ⟨187514919331873380187237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1000079569769991360998597 187514919331873380187237)
                  ·
                    refine ⟨35159047374726258785107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187514919331873380187237 35159047374726258785107)
                    ·
                      rfl

theorem cell22_102708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_102708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102708 prefixEnd_102708 := by exact prefixLift 102708
  have htrace : WordTrace (prefixWord ++ tailWord_102708) baseStart_102708 baseEnd_102708 := by
    simpa [prefixWord, tailWord_102708, baseEnd_102708] using wordTrace_append hprefix tailTrace_102708
  have hstable : (prefixWord ++ tailWord_102708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102708).length < 2 ^ (prefixWord ++ tailWord_102708).sum := by decide
  have hdescent : baseEnd_102708 < baseStart_102708 := by decide
  rcases family_descends (prefixWord ++ tailWord_102708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102738 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_102738 : Nat := 118140960795 + 102738 * 2 ^ 59
def prefixEnd_102738 : Nat := 4983230072969 + 3 ^ 40 * 102738 * 2
def baseEnd_102738 : Nat := 35169316987816180535015

theorem tailTrace_102738 : CollatzResearch.WordTrace tailWord_102738 prefixEnd_102738 35169316987816180535015 := by
  unfold tailWord_102738
  simp only [CollatzResearch.WordTrace]
  refine ⟨936790675451311774645217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2498108467870164732387245 936790675451311774645217)
  ·
    refine ⟨702593006588483830983913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 936790675451311774645217 702593006588483830983913)
    ·
      refine ⟨526944754941362873237935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702593006588483830983913 526944754941362873237935)
      ·
        refine ⟨790417132412044309856903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526944754941362873237935 790417132412044309856903)
        ·
          refine ⟨1185625698618066464785355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790417132412044309856903 1185625698618066464785355)
          ·
            refine ⟨1778438547927099697178033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185625698618066464785355 1778438547927099697178033)
            ·
              refine ⟨1333828910945324772883525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778438547927099697178033 1333828910945324772883525)
              ·
                refine ⟨250092920802248394915661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1333828910945324772883525 250092920802248394915661)
                ·
                  refine ⟨93784845300843148093373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250092920802248394915661 93784845300843148093373)
                  ·
                    refine ⟨35169316987816180535015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93784845300843148093373 35169316987816180535015)
                    ·
                      rfl

theorem cell22_102738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_102738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102738 prefixEnd_102738 := by exact prefixLift 102738
  have htrace : WordTrace (prefixWord ++ tailWord_102738) baseStart_102738 baseEnd_102738 := by
    simpa [prefixWord, tailWord_102738, baseEnd_102738] using wordTrace_append hprefix tailTrace_102738
  have hstable : (prefixWord ++ tailWord_102738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102738).length < 2 ^ (prefixWord ++ tailWord_102738).sum := by decide
  have hdescent : baseEnd_102738 < baseStart_102738 := by decide
  rcases family_descends (prefixWord ++ tailWord_102738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102755 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 1, 3]
def baseStart_102755 : Nat := 118140960795 + 102755 * 2 ^ 59
def prefixEnd_102755 : Nat := 4983230072969 + 3 ^ 40 * 102755 * 2
def baseEnd_102755 : Nat := 35175136435233802859963

theorem tailTrace_102755 : CollatzResearch.WordTrace tailWord_102755 prefixEnd_102755 35175136435233802859963 := by
  unfold tailWord_102755
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747782742743659001949719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2498521828495772667966479 3747782742743659001949719)
  ·
    refine ⟨5621674114115488502924579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3747782742743659001949719 5621674114115488502924579)
    ·
      refine ⟨8432511171173232754386869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621674114115488502924579 8432511171173232754386869)
      ·
        refine ⟨790547922297490570723769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8432511171173232754386869 790547922297490570723769)
        ·
          refine ⟨592910941723117928042827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790547922297490570723769 592910941723117928042827)
          ·
            refine ⟨889366412584676892064241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592910941723117928042827 889366412584676892064241)
            ·
              refine ⟨667024809438507669048181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889366412584676892064241 667024809438507669048181)
              ·
                refine ⟨62533575884860093973267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 667024809438507669048181 62533575884860093973267)
                ·
                  refine ⟨93800363827290140959901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62533575884860093973267 93800363827290140959901)
                  ·
                    refine ⟨35175136435233802859963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93800363827290140959901 35175136435233802859963)
                    ·
                      rfl

theorem cell22_102755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 3].length) (baseStart_102755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102755 prefixEnd_102755 := by exact prefixLift 102755
  have htrace : WordTrace (prefixWord ++ tailWord_102755) baseStart_102755 baseEnd_102755 := by
    simpa [prefixWord, tailWord_102755, baseEnd_102755] using wordTrace_append hprefix tailTrace_102755
  have hstable : (prefixWord ++ tailWord_102755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102755).length < 2 ^ (prefixWord ++ tailWord_102755).sum := by decide
  have hdescent : baseEnd_102755 < baseStart_102755 := by decide
  rcases family_descends (prefixWord ++ tailWord_102755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102768 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_102768 : Nat := 118140960795 + 102768 * 2 ^ 59
def prefixEnd_102768 : Nat := 4983230072969 + 3 ^ 40 * 102768 * 2
def baseEnd_102768 : Nat := 11726528866968700761641

theorem tailTrace_102768 : CollatzResearch.WordTrace tailWord_102768 prefixEnd_102768 11726528866968700761641 := by
  unfold tailWord_102768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874128445848281111086479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2498837927797708148115305 1874128445848281111086479)
  ·
    refine ⟨2811192668772421666629719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874128445848281111086479 2811192668772421666629719)
    ·
      refine ⟨4216789003158632499944579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811192668772421666629719 4216789003158632499944579)
      ·
        refine ⟨6325183504737948749916869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216789003158632499944579 6325183504737948749916869)
        ·
          refine ⟨1185971907138365390609413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6325183504737948749916869 1185971907138365390609413)
          ·
            refine ⟨222369732588443510739265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1185971907138365390609413 222369732588443510739265)
            ·
              refine ⟨166777299441332633054449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222369732588443510739265 166777299441332633054449)
              ·
                refine ⟨125082974580999474790837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166777299441332633054449 125082974580999474790837)
                ·
                  refine ⟨11726528866968700761641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125082974580999474790837 11726528866968700761641)
                  ·
                    rfl

theorem cell22_102768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_102768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102768 prefixEnd_102768 := by exact prefixLift 102768
  have htrace : WordTrace (prefixWord ++ tailWord_102768) baseStart_102768 baseEnd_102768 := by
    simpa [prefixWord, tailWord_102768, baseEnd_102768] using wordTrace_append hprefix tailTrace_102768
  have hstable : (prefixWord ++ tailWord_102768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102768).length < 2 ^ (prefixWord ++ tailWord_102768).sum := by decide
  have hdescent : baseEnd_102768 < baseStart_102768 := by decide
  rcases family_descends (prefixWord ++ tailWord_102768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102796 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_102796 : Nat := 118140960795 + 102796 * 2 ^ 59
def prefixEnd_102796 : Nat := 4983230072969 + 3 ^ 40 * 102796 * 2
def baseEnd_102796 : Nat := 11729723857707787528279

theorem tailTrace_102796 : CollatzResearch.WordTrace tailWord_102796 prefixEnd_102796 11729723857707787528279 := by
  unfold tailWord_102796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874639067797561502096121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2499518757063415336128161 1874639067797561502096121)
  ·
    refine ⟨1405979300848171126572091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1874639067797561502096121 1405979300848171126572091)
    ·
      refine ⟨2108968951272256689858137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405979300848171126572091 2108968951272256689858137)
      ·
        refine ⟨1581726713454192517393603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2108968951272256689858137 1581726713454192517393603)
        ·
          refine ⟨2372590070181288776090405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581726713454192517393603 2372590070181288776090405)
          ·
            refine ⟨444860638158991645516951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2372590070181288776090405 444860638158991645516951)
            ·
              refine ⟨667290957238487468275427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444860638158991645516951 667290957238487468275427)
              ·
                refine ⟨1000936435857731202413141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667290957238487468275427 1000936435857731202413141)
                ·
                  refine ⟨11729723857707787528279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1000936435857731202413141 11729723857707787528279)
                  ·
                    rfl

theorem cell22_102796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_102796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102796 prefixEnd_102796 := by exact prefixLift 102796
  have htrace : WordTrace (prefixWord ++ tailWord_102796) baseStart_102796 baseEnd_102796 := by
    simpa [prefixWord, tailWord_102796, baseEnd_102796] using wordTrace_append hprefix tailTrace_102796
  have hstable : (prefixWord ++ tailWord_102796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102796).length < 2 ^ (prefixWord ++ tailWord_102796).sum := by decide
  have hdescent : baseEnd_102796 < baseStart_102796 := by decide
  rcases family_descends (prefixWord ++ tailWord_102796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102845 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_102845 : Nat := 118140960795 + 102845 * 2 ^ 59
def prefixEnd_102845 : Nat := 4983230072969 + 3 ^ 40 * 102845 * 2
def baseEnd_102845 : Nat := 35205945274503568109687

theorem tailTrace_102845 : CollatzResearch.WordTrace tailWord_102845 prefixEnd_102845 35205945274503568109687 := by
  unfold tailWord_102845
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751065312417604372725989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2500710208278402915150659 3751065312417604372725989)
  ·
    refine ⟨703324746078300819886123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3751065312417604372725989 703324746078300819886123)
    ·
      refine ⟨1054987119117451229829185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703324746078300819886123 1054987119117451229829185)
      ·
        refine ⟨791240339338088422371889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1054987119117451229829185 791240339338088422371889)
        ·
          refine ⟨593430254503566316778917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791240339338088422371889 593430254503566316778917)
          ·
            refine ⟨111268172719418684396047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 593430254503566316778917 111268172719418684396047)
            ·
              refine ⟨166902259079128026594071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111268172719418684396047 166902259079128026594071)
              ·
                refine ⟨250353388618692039891107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166902259079128026594071 250353388618692039891107)
                ·
                  refine ⟨375530082928038059836661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250353388618692039891107 375530082928038059836661)
                  ·
                    refine ⟨35205945274503568109687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 375530082928038059836661 35205945274503568109687)
                    ·
                      rfl

theorem cell22_102845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_102845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102845 prefixEnd_102845 := by exact prefixLift 102845
  have htrace : WordTrace (prefixWord ++ tailWord_102845) baseStart_102845 baseEnd_102845 := by
    simpa [prefixWord, tailWord_102845, baseEnd_102845] using wordTrace_append hprefix tailTrace_102845
  have hstable : (prefixWord ++ tailWord_102845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102845).length < 2 ^ (prefixWord ++ tailWord_102845).sum := by decide
  have hdescent : baseEnd_102845 < baseStart_102845 := by decide
  rcases family_descends (prefixWord ++ tailWord_102845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102871 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_102871 : Nat := 118140960795 + 102871 * 2 ^ 59
def prefixEnd_102871 : Nat := 4983230072969 + 3 ^ 40 * 102871 * 2
def baseEnd_102871 : Nat := 35214845605848166959607

theorem tailTrace_102871 : CollatzResearch.WordTrace tailWord_102871 prefixEnd_102871 35214845605848166959607 := by
  unfold tailWord_102871
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752013610323410813172467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2501342406882273875448311 3752013610323410813172467)
  ·
    refine ⟨5628020415485116219758701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3752013610323410813172467 5628020415485116219758701)
    ·
      refine ⟨2110507655806918582409513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5628020415485116219758701 2110507655806918582409513)
      ·
        refine ⟨1582880741855188936807135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2110507655806918582409513 1582880741855188936807135)
        ·
          refine ⟨2374321112782783405210703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582880741855188936807135 2374321112782783405210703)
          ·
            refine ⟨3561481669174175107816055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374321112782783405210703 3561481669174175107816055)
            ·
              refine ⟨5342222503761262661724083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561481669174175107816055 5342222503761262661724083)
              ·
                refine ⟨8013333755641893992586125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5342222503761262661724083 8013333755641893992586125)
                ·
                  refine ⟨3005000158365710247219797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8013333755641893992586125 3005000158365710247219797)
                  ·
                    refine ⟨35214845605848166959607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3005000158365710247219797 35214845605848166959607)
                    ·
                      rfl

theorem cell22_102871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_102871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102871 prefixEnd_102871 := by exact prefixLift 102871
  have htrace : WordTrace (prefixWord ++ tailWord_102871) baseStart_102871 baseEnd_102871 := by
    simpa [prefixWord, tailWord_102871, baseEnd_102871] using wordTrace_append hprefix tailTrace_102871
  have hstable : (prefixWord ++ tailWord_102871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102871).length < 2 ^ (prefixWord ++ tailWord_102871).sum := by decide
  have hdescent : baseEnd_102871 < baseStart_102871 := by decide
  rcases family_descends (prefixWord ++ tailWord_102871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102941 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_102941 : Nat := 118140960795 + 102941 * 2 ^ 59
def prefixEnd_102941 : Nat := 4983230072969 + 3 ^ 40 * 102941 * 2
def baseEnd_102941 : Nat := 35238808036391317709393

theorem tailTrace_102941 : CollatzResearch.WordTrace tailWord_102941 prefixEnd_102941 35238808036391317709393 := by
  unfold tailWord_102941
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754566720069812768220677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2503044480046541845480451 3754566720069812768220677)
  ·
    refine ⟨703981260013089894041377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3754566720069812768220677 703981260013089894041377)
    ·
      refine ⟨527985945009817420531033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 703981260013089894041377 527985945009817420531033)
      ·
        refine ⟨395989458757363065398275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527985945009817420531033 395989458757363065398275)
        ·
          refine ⟨593984188136044598097413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395989458757363065398275 593984188136044598097413)
          ·
            refine ⟨111372035275508362143265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 593984188136044598097413 111372035275508362143265)
            ·
              refine ⟨83529026456631271607449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111372035275508362143265 83529026456631271607449)
              ·
                refine ⟨62646769842473453705587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83529026456631271607449 62646769842473453705587)
                ·
                  refine ⟨93970154763710180558381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62646769842473453705587 93970154763710180558381)
                  ·
                    refine ⟨35238808036391317709393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93970154763710180558381 35238808036391317709393)
                    ·
                      rfl

theorem cell22_102941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_102941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102941 prefixEnd_102941 := by exact prefixLift 102941
  have htrace : WordTrace (prefixWord ++ tailWord_102941) baseStart_102941 baseEnd_102941 := by
    simpa [prefixWord, tailWord_102941, baseEnd_102941] using wordTrace_append hprefix tailTrace_102941
  have hstable : (prefixWord ++ tailWord_102941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102941).length < 2 ^ (prefixWord ++ tailWord_102941).sum := by decide
  have hdescent : baseEnd_102941 < baseStart_102941 := by decide
  rcases family_descends (prefixWord ++ tailWord_102941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102993 : List Nat := [1, 2, 2, 1, 3, 4, 9]
def baseStart_102993 : Nat := 118140960795 + 102993 * 2 ^ 59
def prefixEnd_102993 : Nat := 4983230072969 + 3 ^ 40 * 102993 * 2
def baseEnd_102993 : Nat := 1305800322188167237379

theorem tailTrace_102993 : CollatzResearch.WordTrace tailWord_102993 prefixEnd_102993 1305800322188167237379 := by
  unfold tailWord_102993
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756463315881425649113633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2504308877254283766075755 3756463315881425649113633)
  ·
    refine ⟨2817347486911069236835225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3756463315881425649113633 2817347486911069236835225)
    ·
      refine ⟨2113010615183301927626419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2817347486911069236835225 2113010615183301927626419)
      ·
        refine ⟨3169515922774952891439629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113010615183301927626419 3169515922774952891439629)
        ·
          refine ⟨1188568471040607334289861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3169515922774952891439629 1188568471040607334289861)
          ·
            refine ⟨222856588320113875179349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1188568471040607334289861 222856588320113875179349)
            ·
              refine ⟨1305800322188167237379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 222856588320113875179349 1305800322188167237379)
              ·
                rfl

theorem cell22_102993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 9].length) (baseStart_102993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102993 prefixEnd_102993 := by exact prefixLift 102993
  have htrace : WordTrace (prefixWord ++ tailWord_102993) baseStart_102993 baseEnd_102993 := by
    simpa [prefixWord, tailWord_102993, baseEnd_102993] using wordTrace_append hprefix tailTrace_102993
  have hstable : (prefixWord ++ tailWord_102993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102993).length < 2 ^ (prefixWord ++ tailWord_102993).sum := by decide
  have hdescent : baseEnd_102993 < baseStart_102993 := by decide
  rcases family_descends (prefixWord ++ tailWord_102993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102997 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_102997 : Nat := 118140960795 + 102997 * 2 ^ 59
def prefixEnd_102997 : Nat := 4983230072969 + 3 ^ 40 * 102997 * 2
def baseEnd_102997 : Nat := 35257977980825838309221

theorem tailTrace_102997 : CollatzResearch.WordTrace tailWord_102997 prefixEnd_102997 35257977980825838309221 := by
  unfold tailWord_102997
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756609207866934332259245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2504406138577956221506163 3756609207866934332259245)
  ·
    refine ⟨1408728452950100374597217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3756609207866934332259245 1408728452950100374597217)
    ·
      refine ⟨1056546339712575280947913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1408728452950100374597217 1056546339712575280947913)
      ·
        refine ⟨792409754784431460710935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056546339712575280947913 792409754784431460710935)
        ·
          refine ⟨1188614632176647191066403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792409754784431460710935 1188614632176647191066403)
          ·
            refine ⟨1782921948264970786599605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188614632176647191066403 1782921948264970786599605)
            ·
              refine ⟨167148932649841011243713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1782921948264970786599605 167148932649841011243713)
              ·
                refine ⟨125361699487380758432785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167148932649841011243713 125361699487380758432785)
                ·
                  refine ⟨94021274615535568824589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125361699487380758432785 94021274615535568824589)
                  ·
                    refine ⟨35257977980825838309221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94021274615535568824589 35257977980825838309221)
                    ·
                      rfl

theorem cell22_102997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_102997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_102997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_102997 prefixEnd_102997 := by exact prefixLift 102997
  have htrace : WordTrace (prefixWord ++ tailWord_102997) baseStart_102997 baseEnd_102997 := by
    simpa [prefixWord, tailWord_102997, baseEnd_102997] using wordTrace_append hprefix tailTrace_102997
  have hstable : (prefixWord ++ tailWord_102997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102997).length < 2 ^ (prefixWord ++ tailWord_102997).sum := by decide
  have hdescent : baseEnd_102997 < baseStart_102997 := by decide
  rcases family_descends (prefixWord ++ tailWord_102997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103023 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_103023 : Nat := 118140960795 + 103023 * 2 ^ 59
def prefixEnd_103023 : Nat := 4983230072969 + 3 ^ 40 * 103023 * 2
def baseEnd_103023 : Nat := 35266878312170437159141

theorem tailTrace_103023 : CollatzResearch.WordTrace tailWord_103023 prefixEnd_103023 35266878312170437159141 := by
  unfold tailWord_103023
  simp only [CollatzResearch.WordTrace]
  refine ⟨3757557505772740772705723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2505038337181827181803815 3757557505772740772705723)
  ·
    refine ⟨5636336258659111159058585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3757557505772740772705723 5636336258659111159058585)
    ·
      refine ⟨4227252193994333369293939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5636336258659111159058585 4227252193994333369293939)
      ·
        refine ⟨6340878290991500053940909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227252193994333369293939 6340878290991500053940909)
        ·
          refine ⟨2377829359121812520227841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6340878290991500053940909 2377829359121812520227841)
          ·
            refine ⟨1783372019341359390170881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2377829359121812520227841 1783372019341359390170881)
            ·
              refine ⟨1337529014506019542628161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783372019341359390170881 1337529014506019542628161)
              ·
                refine ⟨1003146760879514656971121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337529014506019542628161 1003146760879514656971121)
                ·
                  refine ⟨752360070659635992728341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003146760879514656971121 752360070659635992728341)
                  ·
                    refine ⟨35266878312170437159141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 752360070659635992728341 35266878312170437159141)
                    ·
                      rfl

theorem cell22_103023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_103023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103023 prefixEnd_103023 := by exact prefixLift 103023
  have htrace : WordTrace (prefixWord ++ tailWord_103023) baseStart_103023 baseEnd_103023 := by
    simpa [prefixWord, tailWord_103023, baseEnd_103023] using wordTrace_append hprefix tailTrace_103023
  have hstable : (prefixWord ++ tailWord_103023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103023).length < 2 ^ (prefixWord ++ tailWord_103023).sum := by decide
  have hdescent : baseEnd_103023 < baseStart_103023 := by decide
  rcases family_descends (prefixWord ++ tailWord_103023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103072 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_103072 : Nat := 118140960795 + 103072 * 2 ^ 59
def prefixEnd_103072 : Nat := 4983230072969 + 3 ^ 40 * 103072 * 2
def baseEnd_103072 : Nat := 11761217337850214227997

theorem tailTrace_103072 : CollatzResearch.WordTrace tailWord_103072 prefixEnd_103072 11761217337850214227997 := by
  unfold tailWord_103072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879672341297611070619735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2506229788396814760826313 1879672341297611070619735)
  ·
    refine ⟨2819508511946416605929603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879672341297611070619735 2819508511946416605929603)
    ·
      refine ⟨4229262767919624908894405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819508511946416605929603 4229262767919624908894405)
      ·
        refine ⟨792986768984929670417701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4229262767919624908894405 792986768984929670417701)
        ·
          refine ⟨148685019184674313203319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 792986768984929670417701 148685019184674313203319)
          ·
            refine ⟨223027528777011469804979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148685019184674313203319 223027528777011469804979)
            ·
              refine ⟨334541293165517204707469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223027528777011469804979 334541293165517204707469)
              ·
                refine ⟨125452984937068951765301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334541293165517204707469 125452984937068951765301)
                ·
                  refine ⟨11761217337850214227997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125452984937068951765301 11761217337850214227997)
                  ·
                    rfl

theorem cell22_103072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_103072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103072 prefixEnd_103072 := by exact prefixLift 103072
  have htrace : WordTrace (prefixWord ++ tailWord_103072) baseStart_103072 baseEnd_103072 := by
    simpa [prefixWord, tailWord_103072, baseEnd_103072] using wordTrace_append hprefix tailTrace_103072
  have hstable : (prefixWord ++ tailWord_103072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103072).length < 2 ^ (prefixWord ++ tailWord_103072).sum := by decide
  have hdescent : baseEnd_103072 < baseStart_103072 := by decide
  rcases family_descends (prefixWord ++ tailWord_103072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103110 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_103110 : Nat := 118140960795 + 103110 * 2 ^ 59
def prefixEnd_103110 : Nat := 4983230072969 + 3 ^ 40 * 103110 * 2
def baseEnd_103110 : Nat := 35296660190131210233875

theorem tailTrace_103110 : CollatzResearch.WordTrace tailWord_103110 prefixEnd_103110 35296660190131210233875 := by
  unfold tailWord_103110
  simp only [CollatzResearch.WordTrace]
  refine ⟨117522833014298582222587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2507153770971703087415189 117522833014298582222587)
  ·
    refine ⟨176284249521447873333881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117522833014298582222587 176284249521447873333881)
    ·
      refine ⟨132213187141085905000411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176284249521447873333881 132213187141085905000411)
      ·
        refine ⟨198319780711628857500617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132213187141085905000411 198319780711628857500617)
        ·
          refine ⟨148739835533721643125463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198319780711628857500617 148739835533721643125463)
          ·
            refine ⟨223109753300582464688195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148739835533721643125463 223109753300582464688195)
            ·
              refine ⟨334664629950873697032293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223109753300582464688195 334664629950873697032293)
              ·
                refine ⟨62749618115788818193555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334664629950873697032293 62749618115788818193555)
                ·
                  refine ⟨94124427173683227290333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62749618115788818193555 94124427173683227290333)
                  ·
                    refine ⟨35296660190131210233875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94124427173683227290333 35296660190131210233875)
                    ·
                      rfl

theorem cell22_103110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_103110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103110 prefixEnd_103110 := by exact prefixLift 103110
  have htrace : WordTrace (prefixWord ++ tailWord_103110) baseStart_103110 baseEnd_103110 := by
    simpa [prefixWord, tailWord_103110, baseEnd_103110] using wordTrace_append hprefix tailTrace_103110
  have hstable : (prefixWord ++ tailWord_103110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103110).length < 2 ^ (prefixWord ++ tailWord_103110).sum := by decide
  have hdescent : baseEnd_103110 < baseStart_103110 := by decide
  rcases family_descends (prefixWord ++ tailWord_103110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103130 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_103130 : Nat := 118140960795 + 103130 * 2 ^ 59
def prefixEnd_103130 : Nat := 4983230072969 + 3 ^ 40 * 103130 * 2
def baseEnd_103130 : Nat := 35303506598857824733813

theorem tailTrace_103130 : CollatzResearch.WordTrace tailWord_103130 prefixEnd_103130 35303506598857824733813 := by
  unfold tailWord_103130
  simp only [CollatzResearch.WordTrace]
  refine ⟨940365029096274511712711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2507640077590065364567229 940365029096274511712711)
  ·
    refine ⟨1410547543644411767569067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940365029096274511712711 1410547543644411767569067)
    ·
      refine ⟨2115821315466617651353601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410547543644411767569067 2115821315466617651353601)
      ·
        refine ⟨1586865986599963238515201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115821315466617651353601 1586865986599963238515201)
        ·
          refine ⟨1190149489949972428886401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586865986599963238515201 1190149489949972428886401)
          ·
            refine ⟨892612117462479321664801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190149489949972428886401 892612117462479321664801)
            ·
              refine ⟨669459088096859491248601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892612117462479321664801 669459088096859491248601)
              ·
                refine ⟨502094316072644618436451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669459088096859491248601 502094316072644618436451)
                ·
                  refine ⟨753141474108966927654677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502094316072644618436451 753141474108966927654677)
                  ·
                    refine ⟨35303506598857824733813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 753141474108966927654677 35303506598857824733813)
                    ·
                      rfl

theorem cell22_103130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_103130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103130 prefixEnd_103130 := by exact prefixLift 103130
  have htrace : WordTrace (prefixWord ++ tailWord_103130) baseStart_103130 baseEnd_103130 := by
    simpa [prefixWord, tailWord_103130, baseEnd_103130] using wordTrace_append hprefix tailTrace_103130
  have hstable : (prefixWord ++ tailWord_103130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103130).length < 2 ^ (prefixWord ++ tailWord_103130).sum := by decide
  have hdescent : baseEnd_103130 < baseStart_103130 := by decide
  rcases family_descends (prefixWord ++ tailWord_103130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103166 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_103166 : Nat := 118140960795 + 103166 * 2 ^ 59
def prefixEnd_103166 : Nat := 4983230072969 + 3 ^ 40 * 103166 * 2
def baseEnd_103166 : Nat := 35315830134565730833703

theorem tailTrace_103166 : CollatzResearch.WordTrace tailWord_103166 prefixEnd_103166 35315830134565730833703 := by
  unfold tailWord_103166
  simp only [CollatzResearch.WordTrace]
  refine ⟨470346643031834524395169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2508515429503117463440901 470346643031834524395169)
  ·
    refine ⟨352759982273875893296377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 470346643031834524395169 352759982273875893296377)
    ·
      refine ⟨264569986705406919972283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352759982273875893296377 264569986705406919972283)
      ·
        refine ⟨396854980058110379958425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264569986705406919972283 396854980058110379958425)
        ·
          refine ⟨297641235043582784968819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396854980058110379958425 297641235043582784968819)
          ·
            refine ⟨446461852565374177453229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297641235043582784968819 446461852565374177453229)
            ·
              refine ⟨167423194712015316544961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 446461852565374177453229 167423194712015316544961)
              ·
                refine ⟨125567396034011487408721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167423194712015316544961 125567396034011487408721)
                ·
                  refine ⟨94175547025508615556541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125567396034011487408721 94175547025508615556541)
                  ·
                    refine ⟨35315830134565730833703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94175547025508615556541 35315830134565730833703)
                    ·
                      rfl

theorem cell22_103166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_103166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103166 prefixEnd_103166 := by exact prefixLift 103166
  have htrace : WordTrace (prefixWord ++ tailWord_103166) baseStart_103166 baseEnd_103166 := by
    simpa [prefixWord, tailWord_103166, baseEnd_103166] using wordTrace_append hprefix tailTrace_103166
  have hstable : (prefixWord ++ tailWord_103166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103166).length < 2 ^ (prefixWord ++ tailWord_103166).sum := by decide
  have hdescent : baseEnd_103166 < baseStart_103166 := by decide
  rcases family_descends (prefixWord ++ tailWord_103166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103177 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_103177 : Nat := 118140960795 + 103177 * 2 ^ 59
def prefixEnd_103177 : Nat := 4983230072969 + 3 ^ 40 * 103177 * 2
def baseEnd_103177 : Nat := 35319595659365368808669

theorem tailTrace_103177 : CollatzResearch.WordTrace tailWord_103177 prefixEnd_103177 35319595659365368808669 := by
  unfold tailWord_103177
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763174347214825073811785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2508782898143216715874523 3763174347214825073811785)
  ·
    refine ⟨2822380760411118805358839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3763174347214825073811785 2822380760411118805358839)
    ·
      refine ⟨4233571140616678208038259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822380760411118805358839 4233571140616678208038259)
      ·
        refine ⟨6350356710925017312057389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233571140616678208038259 6350356710925017312057389)
        ·
          refine ⟨2381383766596881492021521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6350356710925017312057389 2381383766596881492021521)
          ·
            refine ⟨1786037824947661119016141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381383766596881492021521 1786037824947661119016141)
            ·
              refine ⟨669764184355372919631053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786037824947661119016141 669764184355372919631053)
              ·
                refine ⟨251161569133264844861645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669764184355372919631053 251161569133264844861645)
                ·
                  refine ⟨94185588424974316823117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251161569133264844861645 94185588424974316823117)
                  ·
                    refine ⟨35319595659365368808669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94185588424974316823117 35319595659365368808669)
                    ·
                      rfl

theorem cell22_103177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_103177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103177 prefixEnd_103177 := by exact prefixLift 103177
  have htrace : WordTrace (prefixWord ++ tailWord_103177) baseStart_103177 baseEnd_103177 := by
    simpa [prefixWord, tailWord_103177, baseEnd_103177] using wordTrace_append hprefix tailTrace_103177
  have hstable : (prefixWord ++ tailWord_103177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103177).length < 2 ^ (prefixWord ++ tailWord_103177).sum := by decide
  have hdescent : baseEnd_103177 < baseStart_103177 := by decide
  rcases family_descends (prefixWord ++ tailWord_103177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103267 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 3, 5]
def baseStart_103267 : Nat := 118140960795 + 103267 * 2 ^ 59
def prefixEnd_103267 : Nat := 4983230072969 + 3 ^ 40 * 103267 * 2
def baseEnd_103267 : Nat := 35350404498635134058393

theorem tailTrace_103267 : CollatzResearch.WordTrace tailWord_103267 prefixEnd_103267 35350404498635134058393 := by
  unfold tailWord_103267
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766456916888770444588055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2510971277925846963058703 3766456916888770444588055)
  ·
    refine ⟨5649685375333155666882083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3766456916888770444588055 5649685375333155666882083)
    ·
      refine ⟨8474528062999733500323125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649685375333155666882083 8474528062999733500323125)
      ·
        refine ⟨794487005906225015655293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8474528062999733500323125 794487005906225015655293)
        ·
          refine ⟨297932627214834380870735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794487005906225015655293 297932627214834380870735)
          ·
            refine ⟨446898940822251571306103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297932627214834380870735 446898940822251571306103)
            ·
              refine ⟨670348411233377356959155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446898940822251571306103 670348411233377356959155)
              ·
                refine ⟨1005522616850066035438733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670348411233377356959155 1005522616850066035438733)
                ·
                  refine ⟨377070981318774763289525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005522616850066035438733 377070981318774763289525)
                  ·
                    refine ⟨35350404498635134058393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377070981318774763289525 35350404498635134058393)
                    ·
                      rfl

theorem cell22_103267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_103267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103267 prefixEnd_103267 := by exact prefixLift 103267
  have htrace : WordTrace (prefixWord ++ tailWord_103267) baseStart_103267 baseEnd_103267 := by
    simpa [prefixWord, tailWord_103267, baseEnd_103267] using wordTrace_append hprefix tailTrace_103267
  have hstable : (prefixWord ++ tailWord_103267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103267).length < 2 ^ (prefixWord ++ tailWord_103267).sum := by decide
  have hdescent : baseEnd_103267 < baseStart_103267 := by decide
  rcases family_descends (prefixWord ++ tailWord_103267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103271 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 1, 4]
def baseStart_103271 : Nat := 118140960795 + 103271 * 2 ^ 59
def prefixEnd_103271 : Nat := 4983230072969 + 3 ^ 40 * 103271 * 2
def baseEnd_103271 : Nat := 35351773780380456958381

theorem tailTrace_103271 : CollatzResearch.WordTrace tailWord_103271 prefixEnd_103271 35351773780380456958381 := by
  unfold tailWord_103271
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766602808874279127733667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2511068539249519418489111 3766602808874279127733667)
  ·
    refine ⟨5649904213311418691600501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3766602808874279127733667 5649904213311418691600501)
    ·
      refine ⟨529678519997945502337547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5649904213311418691600501 529678519997945502337547)
      ·
        refine ⟨794517779996918253506321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529678519997945502337547 794517779996918253506321)
        ·
          refine ⟨595888334997688690129741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794517779996918253506321 595888334997688690129741)
          ·
            refine ⟨223458125624133258798653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 595888334997688690129741 223458125624133258798653)
            ·
              refine ⟨83796797109049972049495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223458125624133258798653 83796797109049972049495)
              ·
                refine ⟨125695195663574958074243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83796797109049972049495 125695195663574958074243)
                ·
                  refine ⟨188542793495362437111365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125695195663574958074243 188542793495362437111365)
                  ·
                    refine ⟨35351773780380456958381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188542793495362437111365 35351773780380456958381)
                    ·
                      rfl

theorem cell22_103271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_103271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103271 prefixEnd_103271 := by exact prefixLift 103271
  have htrace : WordTrace (prefixWord ++ tailWord_103271) baseStart_103271 baseEnd_103271 := by
    simpa [prefixWord, tailWord_103271, baseEnd_103271] using wordTrace_append hprefix tailTrace_103271
  have hstable : (prefixWord ++ tailWord_103271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103271).length < 2 ^ (prefixWord ++ tailWord_103271).sum := by decide
  have hdescent : baseEnd_103271 < baseStart_103271 := by decide
  rcases family_descends (prefixWord ++ tailWord_103271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103318 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_103318 : Nat := 118140960795 + 103318 * 2 ^ 59
def prefixEnd_103318 : Nat := 4983230072969 + 3 ^ 40 * 103318 * 2
def baseEnd_103318 : Nat := 35367862840888001033237

theorem tailTrace_103318 : CollatzResearch.WordTrace tailWord_103318 prefixEnd_103318 35367862840888001033237 := by
  unfold tailWord_103318
  simp only [CollatzResearch.WordTrace]
  refine ⟨235519814981500384668413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2512211359802670769796405 235519814981500384668413)
  ·
    refine ⟨88319930618062644250655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235519814981500384668413 88319930618062644250655)
    ·
      refine ⟨132479895927093966375983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88319930618062644250655 132479895927093966375983)
      ·
        refine ⟨198719843890640949563975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132479895927093966375983 198719843890640949563975)
        ·
          refine ⟨298079765835961424345963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198719843890640949563975 298079765835961424345963)
          ·
            refine ⟨447119648753942136518945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298079765835961424345963 447119648753942136518945)
            ·
              refine ⟨335339736565456602389209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447119648753942136518945 335339736565456602389209)
              ·
                refine ⟨251504802424092451791907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335339736565456602389209 251504802424092451791907)
                ·
                  refine ⟨377257203636138677687861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251504802424092451791907 377257203636138677687861)
                  ·
                    refine ⟨35367862840888001033237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377257203636138677687861 35367862840888001033237)
                    ·
                      rfl

theorem cell22_103318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_103318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103318 prefixEnd_103318 := by exact prefixLift 103318
  have htrace : WordTrace (prefixWord ++ tailWord_103318) baseStart_103318 baseEnd_103318 := by
    simpa [prefixWord, tailWord_103318, baseEnd_103318] using wordTrace_append hprefix tailTrace_103318
  have hstable : (prefixWord ++ tailWord_103318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103318).length < 2 ^ (prefixWord ++ tailWord_103318).sum := by decide
  have hdescent : baseEnd_103318 < baseStart_103318 := by decide
  rcases family_descends (prefixWord ++ tailWord_103318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103335 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 2, 3]
def baseStart_103335 : Nat := 118140960795 + 103335 * 2 ^ 59
def prefixEnd_103335 : Nat := 4983230072969 + 3 ^ 40 * 103335 * 2
def baseEnd_103335 : Nat := 35373682288305623358185

theorem tailTrace_103335 : CollatzResearch.WordTrace tailWord_103335 prefixEnd_103335 35373682288305623358185 := by
  unfold tailWord_103335
  simp only [CollatzResearch.WordTrace]
  refine ⟨3768937080642418058063459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2512624720428278705375639 3768937080642418058063459)
  ·
    refine ⟨5653405620963627087095189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3768937080642418058063459 5653405620963627087095189)
    ·
      refine ⟨265003388482670019707587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5653405620963627087095189 265003388482670019707587)
      ·
        refine ⟨397505082724005029561381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265003388482670019707587 397505082724005029561381)
        ·
          refine ⟨74532203010750943042759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397505082724005029561381 74532203010750943042759)
          ·
            refine ⟨111798304516126414564139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74532203010750943042759 111798304516126414564139)
            ·
              refine ⟨167697456774189621846209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111798304516126414564139 167697456774189621846209)
              ·
                refine ⟨125773092580642216384657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167697456774189621846209 125773092580642216384657)
                ·
                  refine ⟨94329819435481662288493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125773092580642216384657 94329819435481662288493)
                  ·
                    refine ⟨35373682288305623358185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94329819435481662288493 35373682288305623358185)
                    ·
                      rfl

theorem cell22_103335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_103335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103335 prefixEnd_103335 := by exact prefixLift 103335
  have htrace : WordTrace (prefixWord ++ tailWord_103335) baseStart_103335 baseEnd_103335 := by
    simpa [prefixWord, tailWord_103335, baseEnd_103335] using wordTrace_append hprefix tailTrace_103335
  have hstable : (prefixWord ++ tailWord_103335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103335).length < 2 ^ (prefixWord ++ tailWord_103335).sum := by decide
  have hdescent : baseEnd_103335 < baseStart_103335 := by decide
  rcases family_descends (prefixWord ++ tailWord_103335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103380 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_103380 : Nat := 118140960795 + 103380 * 2 ^ 59
def prefixEnd_103380 : Nat := 4983230072969 + 3 ^ 40 * 103380 * 2
def baseEnd_103380 : Nat := 35389086707940505983047

theorem tailTrace_103380 : CollatzResearch.WordTrace tailWord_103380 prefixEnd_103380 35389086707940505983047 := by
  unfold tailWord_103380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885289182739695371725797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2513718910319593828967729 1885289182739695371725797)
  ·
    refine ⟨353491721763692882198587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1885289182739695371725797 353491721763692882198587)
    ·
      refine ⟨530237582645539323297881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353491721763692882198587 530237582645539323297881)
      ·
        refine ⟨397678186984154492473411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530237582645539323297881 397678186984154492473411)
        ·
          refine ⟨596517280476231738710117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397678186984154492473411 596517280476231738710117)
          ·
            refine ⟨111846990089293451008147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 596517280476231738710117 111846990089293451008147)
            ·
              refine ⟨167770485133940176512221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111846990089293451008147 167770485133940176512221)
              ·
                refine ⟨62913931925227566192083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167770485133940176512221 62913931925227566192083)
                ·
                  refine ⟨94370897887841349288125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62913931925227566192083 94370897887841349288125)
                  ·
                    refine ⟨35389086707940505983047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94370897887841349288125 35389086707940505983047)
                    ·
                      rfl

theorem cell22_103380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_103380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103380 prefixEnd_103380 := by exact prefixLift 103380
  have htrace : WordTrace (prefixWord ++ tailWord_103380) baseStart_103380 baseEnd_103380 := by
    simpa [prefixWord, tailWord_103380, baseEnd_103380] using wordTrace_append hprefix tailTrace_103380
  have hstable : (prefixWord ++ tailWord_103380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103380).length < 2 ^ (prefixWord ++ tailWord_103380).sum := by decide
  have hdescent : baseEnd_103380 < baseStart_103380 := by decide
  rcases family_descends (prefixWord ++ tailWord_103380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103397 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_103397 : Nat := 118140960795 + 103397 * 2 ^ 59
def prefixEnd_103397 : Nat := 4983230072969 + 3 ^ 40 * 103397 * 2
def baseEnd_103397 : Nat := 35394906155358128307995

theorem tailTrace_103397 : CollatzResearch.WordTrace tailWord_103397 prefixEnd_103397 35394906155358128307995 := by
  unfold tailWord_103397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771198406417802646820445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2514132270945201764546963 3771198406417802646820445)
  ·
    refine ⟨1414199402406675992557667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3771198406417802646820445 1414199402406675992557667)
    ·
      refine ⟨2121299103610013988836501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414199402406675992557667 2121299103610013988836501)
      ·
        refine ⟨99435895481719405726711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2121299103610013988836501 99435895481719405726711)
        ·
          refine ⟨149153843222579108590067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99435895481719405726711 149153843222579108590067)
          ·
            refine ⟨223730764833868662885101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149153843222579108590067 223730764833868662885101)
            ·
              refine ⟨83899036812700748581913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223730764833868662885101 83899036812700748581913)
              ·
                refine ⟨62924277609525561436435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83899036812700748581913 62924277609525561436435)
                ·
                  refine ⟨94386416414288342154653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62924277609525561436435 94386416414288342154653)
                  ·
                    refine ⟨35394906155358128307995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94386416414288342154653 35394906155358128307995)
                    ·
                      rfl

theorem cell22_103397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_103397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103397 prefixEnd_103397 := by exact prefixLift 103397
  have htrace : WordTrace (prefixWord ++ tailWord_103397) baseStart_103397 baseEnd_103397 := by
    simpa [prefixWord, tailWord_103397, baseEnd_103397] using wordTrace_append hprefix tailTrace_103397
  have hstable : (prefixWord ++ tailWord_103397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103397).length < 2 ^ (prefixWord ++ tailWord_103397).sum := by decide
  have hdescent : baseEnd_103397 < baseStart_103397 := by decide
  rcases family_descends (prefixWord ++ tailWord_103397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103410 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_103410 : Nat := 118140960795 + 103410 * 2 ^ 59
def prefixEnd_103410 : Nat := 4983230072969 + 3 ^ 40 * 103410 * 2
def baseEnd_103410 : Nat := 11799785440343475910985

theorem tailTrace_103410 : CollatzResearch.WordTrace tailWord_103410 prefixEnd_103410 11799785440343475910985 := by
  unfold tailWord_103410
  simp only [CollatzResearch.WordTrace]
  refine ⟨942918138842676466760921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2514448370247137244695789 942918138842676466760921)
  ·
    refine ⟨707188604132007350070691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 942918138842676466760921 707188604132007350070691)
    ·
      refine ⟨1060782906198011025106037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707188604132007350070691 1060782906198011025106037)
      ·
        refine ⟨99448397456063533603691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1060782906198011025106037 99448397456063533603691)
        ·
          refine ⟨149172596184095300405537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99448397456063533603691 149172596184095300405537)
          ·
            refine ⟨111879447138071475304153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149172596184095300405537 111879447138071475304153)
            ·
              refine ⟨83909585353553606478115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111879447138071475304153 83909585353553606478115)
              ·
                refine ⟨125864378030330409717173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83909585353553606478115 125864378030330409717173)
                ·
                  refine ⟨11799785440343475910985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125864378030330409717173 11799785440343475910985)
                  ·
                    rfl

theorem cell22_103410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_103410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103410 prefixEnd_103410 := by exact prefixLift 103410
  have htrace : WordTrace (prefixWord ++ tailWord_103410) baseStart_103410 baseEnd_103410 := by
    simpa [prefixWord, tailWord_103410, baseEnd_103410] using wordTrace_append hprefix tailTrace_103410
  have hstable : (prefixWord ++ tailWord_103410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103410).length < 2 ^ (prefixWord ++ tailWord_103410).sum := by decide
  have hdescent : baseEnd_103410 < baseStart_103410 := by decide
  rcases family_descends (prefixWord ++ tailWord_103410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103481 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_103481 : Nat := 118140960795 + 103481 * 2 ^ 59
def prefixEnd_103481 : Nat := 4983230072969 + 3 ^ 40 * 103481 * 2
def baseEnd_103481 : Nat := 35423661072009909207737

theorem tailTrace_103481 : CollatzResearch.WordTrace tailWord_103481 prefixEnd_103481 35423661072009909207737 := by
  unfold tailWord_103481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774262138113484992878297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2516174758742323328585531 3774262138113484992878297)
  ·
    refine ⟨2830696603585113744658723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3774262138113484992878297 2830696603585113744658723)
    ·
      refine ⟨4246044905377670616988085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830696603585113744658723 4246044905377670616988085)
      ·
        refine ⟨398066709879156620342633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4246044905377670616988085 398066709879156620342633)
        ·
          refine ⟨298550032409367465256975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398066709879156620342633 298550032409367465256975)
          ·
            refine ⟨447825048614051197885463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298550032409367465256975 447825048614051197885463)
            ·
              refine ⟨671737572921076796828195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447825048614051197885463 671737572921076796828195)
              ·
                refine ⟨1007606359381615195242293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671737572921076796828195 1007606359381615195242293)
                ·
                  refine ⟨94463096192026424553965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1007606359381615195242293 94463096192026424553965)
                  ·
                    refine ⟨35423661072009909207737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94463096192026424553965 35423661072009909207737)
                    ·
                      rfl

theorem cell22_103481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_103481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103481 prefixEnd_103481 := by exact prefixLift 103481
  have htrace : WordTrace (prefixWord ++ tailWord_103481) baseStart_103481 baseEnd_103481 := by
    simpa [prefixWord, tailWord_103481, baseEnd_103481] using wordTrace_append hprefix tailTrace_103481
  have hstable : (prefixWord ++ tailWord_103481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103481).length < 2 ^ (prefixWord ++ tailWord_103481).sum := by decide
  have hdescent : baseEnd_103481 < baseStart_103481 := by decide
  rcases family_descends (prefixWord ++ tailWord_103481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103498 : List Nat := [3, 1, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_103498 : Nat := 118140960795 + 103498 * 2 ^ 59
def prefixEnd_103498 : Nat := 4983230072969 + 3 ^ 40 * 103498 * 2
def baseEnd_103498 : Nat := 35429480519427531532685

theorem tailTrace_103498 : CollatzResearch.WordTrace tailWord_103498 prefixEnd_103498 35429480519427531532685 := by
  unfold tailWord_103498
  simp only [CollatzResearch.WordTrace]
  refine ⟨943720544762974224061787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2516588119367931264164765 943720544762974224061787)
  ·
    refine ⟨1415580817144461336092681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943720544762974224061787 1415580817144461336092681)
    ·
      refine ⟨1061685612858346002069511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1415580817144461336092681 1061685612858346002069511)
      ·
        refine ⟨1592528419287519003104267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061685612858346002069511 1592528419287519003104267)
        ·
          refine ⟨2388792628931278504656401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592528419287519003104267 2388792628931278504656401)
          ·
            refine ⟨1791594471698458878492301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2388792628931278504656401 1791594471698458878492301)
            ·
              refine ⟨671847926886922079434613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1791594471698458878492301 671847926886922079434613)
              ·
                refine ⟨62985743145648944946995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 671847926886922079434613 62985743145648944946995)
                ·
                  refine ⟨94478614718473417420493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62985743145648944946995 94478614718473417420493)
                  ·
                    refine ⟨35429480519427531532685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94478614718473417420493 35429480519427531532685)
                    ·
                      rfl

theorem cell22_103498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_103498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103498 prefixEnd_103498 := by exact prefixLift 103498
  have htrace : WordTrace (prefixWord ++ tailWord_103498) baseStart_103498 baseEnd_103498 := by
    simpa [prefixWord, tailWord_103498, baseEnd_103498] using wordTrace_append hprefix tailTrace_103498
  have hstable : (prefixWord ++ tailWord_103498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103498).length < 2 ^ (prefixWord ++ tailWord_103498).sum := by decide
  have hdescent : baseEnd_103498 < baseStart_103498 := by decide
  rcases family_descends (prefixWord ++ tailWord_103498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103509 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_103509 : Nat := 118140960795 + 103509 * 2 ^ 59
def prefixEnd_103509 : Nat := 4983230072969 + 3 ^ 40 * 103509 * 2
def baseEnd_103509 : Nat := 35433246044227169507651

theorem tailTrace_103509 : CollatzResearch.WordTrace tailWord_103509 prefixEnd_103509 35433246044227169507651 := by
  unfold tailWord_103509
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775283382012045774897581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2516855588008030516598387 3775283382012045774897581)
  ·
    refine ⟨1415731268254517165586593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3775283382012045774897581 1415731268254517165586593)
    ·
      refine ⟨1061798451190887874189945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1415731268254517165586593 1061798451190887874189945)
      ·
        refine ⟨796348838393165905642459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061798451190887874189945 796348838393165905642459)
        ·
          refine ⟨1194523257589748858463689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796348838393165905642459 1194523257589748858463689)
          ·
            refine ⟨895892443192311643847767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194523257589748858463689 895892443192311643847767)
            ·
              refine ⟨1343838664788467465771651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895892443192311643847767 1343838664788467465771651)
              ·
                refine ⟨2015757997182701198657477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343838664788467465771651 2015757997182701198657477)
                ·
                  refine ⟨377954624471756474748277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015757997182701198657477 377954624471756474748277)
                  ·
                    refine ⟨35433246044227169507651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 377954624471756474748277 35433246044227169507651)
                    ·
                      rfl

theorem cell22_103509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_103509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103509 prefixEnd_103509 := by exact prefixLift 103509
  have htrace : WordTrace (prefixWord ++ tailWord_103509) baseStart_103509 baseEnd_103509 := by
    simpa [prefixWord, tailWord_103509, baseEnd_103509] using wordTrace_append hprefix tailTrace_103509
  have hstable : (prefixWord ++ tailWord_103509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103509).length < 2 ^ (prefixWord ++ tailWord_103509).sum := by decide
  have hdescent : baseEnd_103509 < baseStart_103509 := by decide
  rcases family_descends (prefixWord ++ tailWord_103509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103571 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 4, 3]
def baseStart_103571 : Nat := 118140960795 + 103571 * 2 ^ 59
def prefixEnd_103571 : Nat := 4983230072969 + 3 ^ 40 * 103571 * 2
def baseEnd_103571 : Nat := 35454469911279674457461

theorem tailTrace_103571 : CollatzResearch.WordTrace tailWord_103571 prefixEnd_103571 35454469911279674457461 := by
  unfold tailWord_103571
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777544707787430363654567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2518363138524953575769711 3777544707787430363654567)
  ·
    refine ⟨5666317061681145545481851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3777544707787430363654567 5666317061681145545481851)
    ·
      refine ⟨8499475592521718318222777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5666317061681145545481851 8499475592521718318222777)
      ·
        refine ⟨6374606694391288738667083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8499475592521718318222777 6374606694391288738667083)
        ·
          refine ⟨9561910041586933108000625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374606694391288738667083 9561910041586933108000625)
          ·
            refine ⟨7171432531190199831000469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9561910041586933108000625 7171432531190199831000469)
            ·
              refine ⟨336160899899540617078147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7171432531190199831000469 336160899899540617078147)
              ·
                refine ⟨504241349849310925617221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336160899899540617078147 504241349849310925617221)
                ·
                  refine ⟨94545253096745798553229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504241349849310925617221 94545253096745798553229)
                  ·
                    refine ⟨35454469911279674457461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94545253096745798553229 35454469911279674457461)
                    ·
                      rfl

theorem cell22_103571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 3].length) (baseStart_103571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103571 prefixEnd_103571 := by exact prefixLift 103571
  have htrace : WordTrace (prefixWord ++ tailWord_103571) baseStart_103571 baseEnd_103571 := by
    simpa [prefixWord, tailWord_103571, baseEnd_103571] using wordTrace_append hprefix tailTrace_103571
  have hstable : (prefixWord ++ tailWord_103571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103571).length < 2 ^ (prefixWord ++ tailWord_103571).sum := by decide
  have hdescent : baseEnd_103571 < baseStart_103571 := by decide
  rcases family_descends (prefixWord ++ tailWord_103571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103599 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_103599 : Nat := 118140960795 + 103599 * 2 ^ 59
def prefixEnd_103599 : Nat := 4983230072969 + 3 ^ 40 * 103599 * 2
def baseEnd_103599 : Nat := 35464054883496934757375

theorem tailTrace_103599 : CollatzResearch.WordTrace tailWord_103599 prefixEnd_103599 35464054883496934757375 := by
  unfold tailWord_103599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778565951685991145673851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2519043967790660763782567 3778565951685991145673851)
  ·
    refine ⟨5667848927528986718510777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3778565951685991145673851 5667848927528986718510777)
    ·
      refine ⟨4250886695646740038883083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5667848927528986718510777 4250886695646740038883083)
      ·
        refine ⟨6376330043470110058324625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4250886695646740038883083 6376330043470110058324625)
        ·
          refine ⟨4782247532602582543743469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6376330043470110058324625 4782247532602582543743469)
          ·
            refine ⟨1793342824725968453903801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4782247532602582543743469 1793342824725968453903801)
            ·
              refine ⟨1345007118544476340427851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793342824725968453903801 1345007118544476340427851)
              ·
                refine ⟨2017510677816714510641777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345007118544476340427851 2017510677816714510641777)
                ·
                  refine ⟨1513133008362535882981333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2017510677816714510641777 1513133008362535882981333)
                  ·
                    refine ⟨35464054883496934757375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1513133008362535882981333 35464054883496934757375)
                    ·
                      rfl

theorem cell22_103599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_103599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103599 prefixEnd_103599 := by exact prefixLift 103599
  have htrace : WordTrace (prefixWord ++ tailWord_103599) baseStart_103599 baseEnd_103599 := by
    simpa [prefixWord, tailWord_103599, baseEnd_103599] using wordTrace_append hprefix tailTrace_103599
  have hstable : (prefixWord ++ tailWord_103599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103599).length < 2 ^ (prefixWord ++ tailWord_103599).sum := by decide
  have hdescent : baseEnd_103599 < baseStart_103599 := by decide
  rcases family_descends (prefixWord ++ tailWord_103599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103601 : List Nat := [1, 2, 2, 5, 1, 1, 2, 8]
def baseStart_103601 : Nat := 118140960795 + 103601 * 2 ^ 59
def prefixEnd_103601 : Nat := 4983230072969 + 3 ^ 40 * 103601 * 2
def baseEnd_103601 : Nat := 3940526613818844023041

theorem tailTrace_103601 : CollatzResearch.WordTrace tailWord_103601 prefixEnd_103601 3940526613818844023041 := by
  unfold tailWord_103601
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778638897678745487246657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2519092598452496991497771 3778638897678745487246657)
  ·
    refine ⟨2833979173259059115434993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3778638897678745487246657 2833979173259059115434993)
    ·
      refine ⟨2125484379944294336576245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2833979173259059115434993 2125484379944294336576245)
      ·
        refine ⟨199264160619777594054023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2125484379944294336576245 199264160619777594054023)
        ·
          refine ⟨298896240929666391081035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199264160619777594054023 298896240929666391081035)
          ·
            refine ⟨448344361394499586621553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298896240929666391081035 448344361394499586621553)
            ·
              refine ⟨336258271045874689966165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448344361394499586621553 336258271045874689966165)
              ·
                refine ⟨3940526613818844023041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 336258271045874689966165 3940526613818844023041)
                ·
                  rfl

theorem cell22_103601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 8].length) (baseStart_103601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103601 prefixEnd_103601 := by exact prefixLift 103601
  have htrace : WordTrace (prefixWord ++ tailWord_103601) baseStart_103601 baseEnd_103601 := by
    simpa [prefixWord, tailWord_103601, baseEnd_103601] using wordTrace_append hprefix tailTrace_103601
  have hstable : (prefixWord ++ tailWord_103601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103601).length < 2 ^ (prefixWord ++ tailWord_103601).sum := by decide
  have hdescent : baseEnd_103601 < baseStart_103601 := by decide
  rcases family_descends (prefixWord ++ tailWord_103601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103618 : List Nat := [3, 5, 1, 1, 12]
def baseStart_103618 : Nat := 118140960795 + 103618 * 2 ^ 59
def prefixEnd_103618 : Nat := 4983230072969 + 3 ^ 40 * 103618 * 2
def baseEnd_103618 : Nat := 145969378484721063919

theorem tailTrace_103618 : CollatzResearch.WordTrace tailWord_103618 prefixEnd_103618 145969378484721063919 := by
  unfold tailWord_103618
  simp only [CollatzResearch.WordTrace]
  refine ⟨944814734654289347653877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2519505959078104927077005 944814734654289347653877)
  ·
    refine ⟨88576381373839626342551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 944814734654289347653877 88576381373839626342551)
    ·
      refine ⟨132864572060759439513827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88576381373839626342551 132864572060759439513827)
      ·
        refine ⟨199296858091139159270741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132864572060759439513827 199296858091139159270741)
        ·
          refine ⟨145969378484721063919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 199296858091139159270741 145969378484721063919)
          ·
            rfl

theorem cell22_103618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 12].length) (baseStart_103618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103618 prefixEnd_103618 := by exact prefixLift 103618
  have htrace : WordTrace (prefixWord ++ tailWord_103618) baseStart_103618 baseEnd_103618 := by
    simpa [prefixWord, tailWord_103618, baseEnd_103618] using wordTrace_append hprefix tailTrace_103618
  have hstable : (prefixWord ++ tailWord_103618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103618).length < 2 ^ (prefixWord ++ tailWord_103618).sum := by decide
  have hdescent : baseEnd_103618 < baseStart_103618 := by decide
  rcases family_descends (prefixWord ++ tailWord_103618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103678 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_103678 : Nat := 118140960795 + 103678 * 2 ^ 59
def prefixEnd_103678 : Nat := 4983230072969 + 3 ^ 40 * 103678 * 2
def baseEnd_103678 : Nat := 35491098197967062032133

theorem tailTrace_103678 : CollatzResearch.WordTrace tailWord_103678 prefixEnd_103678 35491098197967062032133 := by
  unfold tailWord_103678
  simp only [CollatzResearch.WordTrace]
  refine ⟨472680914799973454724961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2520964878933191758533125 472680914799973454724961)
  ·
    refine ⟨354510686099980091043721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 472680914799973454724961 354510686099980091043721)
    ·
      refine ⟨265883014574985068282791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354510686099980091043721 265883014574985068282791)
      ·
        refine ⟨398824521862477602424187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265883014574985068282791 398824521862477602424187)
        ·
          refine ⟨598236782793716403636281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398824521862477602424187 598236782793716403636281)
          ·
            refine ⟨448677587095287302727211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598236782793716403636281 448677587095287302727211)
            ·
              refine ⟨673016380642930954090817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448677587095287302727211 673016380642930954090817)
              ·
                refine ⟨504762285482198215568113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673016380642930954090817 504762285482198215568113)
                ·
                  refine ⟨378571714111648661676085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504762285482198215568113 378571714111648661676085)
                  ·
                    refine ⟨35491098197967062032133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 378571714111648661676085 35491098197967062032133)
                    ·
                      rfl

theorem cell22_103678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_103678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103678 prefixEnd_103678 := by exact prefixLift 103678
  have htrace : WordTrace (prefixWord ++ tailWord_103678) baseStart_103678 baseEnd_103678 := by
    simpa [prefixWord, tailWord_103678, baseEnd_103678] using wordTrace_append hprefix tailTrace_103678
  have hstable : (prefixWord ++ tailWord_103678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103678).length < 2 ^ (prefixWord ++ tailWord_103678).sum := by decide
  have hdescent : baseEnd_103678 < baseStart_103678 := by decide
  rcases family_descends (prefixWord ++ tailWord_103678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103691 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 6]
def baseStart_103691 : Nat := 118140960795 + 103691 * 2 ^ 59
def prefixEnd_103691 : Nat := 4983230072969 + 3 ^ 40 * 103691 * 2
def baseEnd_103691 : Nat := 11831849454546453819031

theorem tailTrace_103691 : CollatzResearch.WordTrace tailWord_103691 prefixEnd_103691 11831849454546453819031 := by
  unfold tailWord_103691
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781921467352690858022927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2521280978235127238681951 3781921467352690858022927)
  ·
    refine ⟨5672882201029036287034391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3781921467352690858022927 5672882201029036287034391)
    ·
      refine ⟨8509323301543554430551587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672882201029036287034391 8509323301543554430551587)
      ·
        refine ⟨12763984952315331645827381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509323301543554430551587 12763984952315331645827381)
        ·
          refine ⟨1196623589279562341796317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12763984952315331645827381 1196623589279562341796317)
          ·
            refine ⟨448733845979835878173619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1196623589279562341796317 448733845979835878173619)
            ·
              refine ⟨673100768969753817260429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448733845979835878173619 673100768969753817260429)
              ·
                refine ⟨252412788363657681472661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673100768969753817260429 252412788363657681472661)
                ·
                  refine ⟨11831849454546453819031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 252412788363657681472661 11831849454546453819031)
                  ·
                    rfl

theorem cell22_103691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_103691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103691 prefixEnd_103691 := by exact prefixLift 103691
  have htrace : WordTrace (prefixWord ++ tailWord_103691) baseStart_103691 baseEnd_103691 := by
    simpa [prefixWord, tailWord_103691, baseEnd_103691] using wordTrace_append hprefix tailTrace_103691
  have hstable : (prefixWord ++ tailWord_103691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103691).length < 2 ^ (prefixWord ++ tailWord_103691).sum := by decide
  have hdescent : baseEnd_103691 < baseStart_103691 := by decide
  rcases family_descends (prefixWord ++ tailWord_103691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103738 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_103738 : Nat := 118140960795 + 103738 * 2 ^ 59
def prefixEnd_103738 : Nat := 4983230072969 + 3 ^ 40 * 103738 * 2
def baseEnd_103738 : Nat := 35511637424146905531949

theorem tailTrace_103738 : CollatzResearch.WordTrace tailWord_103738 prefixEnd_103738 35511637424146905531949 := by
  unfold tailWord_103738
  simp only [CollatzResearch.WordTrace]
  refine ⟨945908924545604471245967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2522423798788278589989245 945908924545604471245967)
  ·
    refine ⟨1418863386818406706868951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 945908924545604471245967 1418863386818406706868951)
    ·
      refine ⟨2128295080227610060303427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418863386818406706868951 2128295080227610060303427)
      ·
        refine ⟨3192442620341415090455141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128295080227610060303427 3192442620341415090455141)
        ·
          refine ⟨598582991314015329460339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3192442620341415090455141 598582991314015329460339)
          ·
            refine ⟨897874486971022994190509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598582991314015329460339 897874486971022994190509)
            ·
              refine ⟨336702932614133622821441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 897874486971022994190509 336702932614133622821441)
              ·
                refine ⟨252527199460600217116081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336702932614133622821441 252527199460600217116081)
                ·
                  refine ⟨189395399595450162837061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252527199460600217116081 189395399595450162837061)
                  ·
                    refine ⟨35511637424146905531949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189395399595450162837061 35511637424146905531949)
                    ·
                      rfl

theorem cell22_103738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_103738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103738 prefixEnd_103738 := by exact prefixLift 103738
  have htrace : WordTrace (prefixWord ++ tailWord_103738) baseStart_103738 baseEnd_103738 := by
    simpa [prefixWord, tailWord_103738, baseEnd_103738] using wordTrace_append hprefix tailTrace_103738
  have hstable : (prefixWord ++ tailWord_103738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103738).length < 2 ^ (prefixWord ++ tailWord_103738).sum := by decide
  have hdescent : baseEnd_103738 < baseStart_103738 := by decide
  rcases family_descends (prefixWord ++ tailWord_103738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103742 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_103742 : Nat := 118140960795 + 103742 * 2 ^ 59
def prefixEnd_103742 : Nat := 4983230072969 + 3 ^ 40 * 103742 * 2
def baseEnd_103742 : Nat := 11837668901964076143979

theorem tailTrace_103742 : CollatzResearch.WordTrace tailWord_103742 prefixEnd_103742 11837668901964076143979 := by
  unfold tailWord_103742
  simp only [CollatzResearch.WordTrace]
  refine ⟨472972698770990821016185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2522521060111951045419653 472972698770990821016185)
  ·
    refine ⟨354729524078243115762139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 472972698770990821016185 354729524078243115762139)
    ·
      refine ⟨532094286117364673643209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354729524078243115762139 532094286117364673643209)
      ·
        refine ⟨399070714588023505232407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532094286117364673643209 399070714588023505232407)
        ·
          refine ⟨598606071882035257848611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399070714588023505232407 598606071882035257848611)
          ·
            refine ⟨897909107823052886772917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598606071882035257848611 897909107823052886772917)
            ·
              refine ⟨84178978858411208134961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 897909107823052886772917 84178978858411208134961)
              ·
                refine ⟨63134234143808406101221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84178978858411208134961 63134234143808406101221)
                ·
                  refine ⟨11837668901964076143979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63134234143808406101221 11837668901964076143979)
                  ·
                    rfl

theorem cell22_103742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_103742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103742 prefixEnd_103742 := by exact prefixLift 103742
  have htrace : WordTrace (prefixWord ++ tailWord_103742) baseStart_103742 baseEnd_103742 := by
    simpa [prefixWord, tailWord_103742, baseEnd_103742] using wordTrace_append hprefix tailTrace_103742
  have hstable : (prefixWord ++ tailWord_103742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103742).length < 2 ^ (prefixWord ++ tailWord_103742).sum := by decide
  have hdescent : baseEnd_103742 < baseStart_103742 := by decide
  rcases family_descends (prefixWord ++ tailWord_103742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103768 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_103768 : Nat := 118140960795 + 103768 * 2 ^ 59
def prefixEnd_103768 : Nat := 4983230072969 + 3 ^ 40 * 103768 * 2
def baseEnd_103768 : Nat := 35521907037236827281857

theorem tailTrace_103768 : CollatzResearch.WordTrace tailWord_103768 prefixEnd_103768 35521907037236827281857 := by
  unfold tailWord_103768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892364944036866504287979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2523153258715822005717305 1892364944036866504287979)
  ·
    refine ⟨2838547416055299756431969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892364944036866504287979 2838547416055299756431969)
    ·
      refine ⟨2128910562041474817323977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2838547416055299756431969 2128910562041474817323977)
      ·
        refine ⟨1596682921531106112992983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2128910562041474817323977 1596682921531106112992983)
        ·
          refine ⟨2395024382296659169489475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596682921531106112992983 2395024382296659169489475)
          ·
            refine ⟨3592536573444988754234213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395024382296659169489475 3592536573444988754234213)
            ·
              refine ⟨673600607520935391418915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3592536573444988754234213 673600607520935391418915)
              ·
                refine ⟨1010400911281403087128373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673600607520935391418915 1010400911281403087128373)
                ·
                  refine ⟨94725085432631539418285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1010400911281403087128373 94725085432631539418285)
                  ·
                    refine ⟨35521907037236827281857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94725085432631539418285 35521907037236827281857)
                    ·
                      rfl

theorem cell22_103768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_103768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103768 prefixEnd_103768 := by exact prefixLift 103768
  have htrace : WordTrace (prefixWord ++ tailWord_103768) baseStart_103768 baseEnd_103768 := by
    simpa [prefixWord, tailWord_103768, baseEnd_103768] using wordTrace_append hprefix tailTrace_103768
  have hstable : (prefixWord ++ tailWord_103768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103768).length < 2 ^ (prefixWord ++ tailWord_103768).sum := by decide
  have hdescent : baseEnd_103768 < baseStart_103768 := by decide
  rcases family_descends (prefixWord ++ tailWord_103768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103836 : List Nat := [2, 2, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_103836 : Nat := 118140960795 + 103836 * 2 ^ 59
def prefixEnd_103836 : Nat := 4983230072969 + 3 ^ 40 * 103836 * 2
def baseEnd_103836 : Nat := 35545184826907316581649

theorem tailTrace_103836 : CollatzResearch.WordTrace tailWord_103836 prefixEnd_103836 35545184826907316581649 := by
  unfold tailWord_103836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893605025913690311025681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2524806701218253748034241 1893605025913690311025681)
  ·
    refine ⟨1420203769435267733269261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1893605025913690311025681 1420203769435267733269261)
    ·
      refine ⟨532576413538225399975973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1420203769435267733269261 532576413538225399975973)
      ·
        refine ⟨99858077538417262495495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 532576413538225399975973 99858077538417262495495)
        ·
          refine ⟨149787116307625893743243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99858077538417262495495 149787116307625893743243)
          ·
            refine ⟨224680674461438840614865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149787116307625893743243 224680674461438840614865)
            ·
              refine ⟨168510505846079130461149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224680674461438840614865 168510505846079130461149)
              ·
                refine ⟨63191439692279673922931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168510505846079130461149 63191439692279673922931)
                ·
                  refine ⟨94787159538419510884397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63191439692279673922931 94787159538419510884397)
                  ·
                    refine ⟨35545184826907316581649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94787159538419510884397 35545184826907316581649)
                    ·
                      rfl

theorem cell22_103836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_103836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103836 prefixEnd_103836 := by exact prefixLift 103836
  have htrace : WordTrace (prefixWord ++ tailWord_103836) baseStart_103836 baseEnd_103836 := by
    simpa [prefixWord, tailWord_103836, baseEnd_103836] using wordTrace_append hprefix tailTrace_103836
  have hstable : (prefixWord ++ tailWord_103836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103836).length < 2 ^ (prefixWord ++ tailWord_103836).sum := by decide
  have hdescent : baseEnd_103836 < baseStart_103836 := by decide
  rcases family_descends (prefixWord ++ tailWord_103836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103875 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 2, 3]
def baseStart_103875 : Nat := 118140960795 + 103875 * 2 ^ 59
def prefixEnd_103875 : Nat := 4983230072969 + 3 ^ 40 * 103875 * 2
def baseEnd_103875 : Nat := 35558535323924214856529

theorem tailTrace_103875 : CollatzResearch.WordTrace tailWord_103875 prefixEnd_103875 35558535323924214856529 := by
  unfold tailWord_103875
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788632498686090282721079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2525754999124060188480719 3788632498686090282721079)
  ·
    refine ⟨5682948748029135424081619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788632498686090282721079 5682948748029135424081619)
    ·
      refine ⟨8524423122043703136122429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682948748029135424081619 8524423122043703136122429)
      ·
        refine ⟨3196658670766388676045911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8524423122043703136122429 3196658670766388676045911)
        ·
          refine ⟨4794988006149583014068867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196658670766388676045911 4794988006149583014068867)
          ·
            refine ⟨7192482009224374521103301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794988006149583014068867 7192482009224374521103301)
            ·
              refine ⟨1348590376729570222706869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7192482009224374521103301 1348590376729570222706869)
              ·
                refine ⟨126430347818397208378769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1348590376729570222706869 126430347818397208378769)
                ·
                  refine ⟨94822760863797906284077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126430347818397208378769 94822760863797906284077)
                  ·
                    refine ⟨35558535323924214856529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94822760863797906284077 35558535323924214856529)
                    ·
                      rfl

theorem cell22_103875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 3].length) (baseStart_103875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103875 prefixEnd_103875 := by exact prefixLift 103875
  have htrace : WordTrace (prefixWord ++ tailWord_103875) baseStart_103875 baseEnd_103875 := by
    simpa [prefixWord, tailWord_103875, baseEnd_103875] using wordTrace_append hprefix tailTrace_103875
  have hstable : (prefixWord ++ tailWord_103875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103875).length < 2 ^ (prefixWord ++ tailWord_103875).sum := by decide
  have hdescent : baseEnd_103875 < baseStart_103875 := by decide
  rcases family_descends (prefixWord ++ tailWord_103875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103894 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_103894 : Nat := 118140960795 + 103894 * 2 ^ 59
def prefixEnd_103894 : Nat := 4983230072969 + 3 ^ 40 * 103894 * 2
def baseEnd_103894 : Nat := 11855013137404832877157

theorem tailTrace_103894 : CollatzResearch.WordTrace tailWord_103894 prefixEnd_103894 11855013137404832877157 := by
  unfold tailWord_103894
  simp only [CollatzResearch.WordTrace]
  refine ⟨236832842851078532978921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2526216990411504351775157 236832842851078532978921)
  ·
    refine ⟨177624632138308899734191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236832842851078532978921 177624632138308899734191)
    ·
      refine ⟨266436948207463349601287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177624632138308899734191 266436948207463349601287)
      ·
        refine ⟨399655422311195024401931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266436948207463349601287 399655422311195024401931)
        ·
          refine ⟨599483133466792536602897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399655422311195024401931 599483133466792536602897)
          ·
            refine ⟨449612350100094402452173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599483133466792536602897 449612350100094402452173)
            ·
              refine ⟨168604631287535400919565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449612350100094402452173 168604631287535400919565)
              ·
                refine ⟨63226736732825775344837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168604631287535400919565 63226736732825775344837)
                ·
                  refine ⟨11855013137404832877157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63226736732825775344837 11855013137404832877157)
                  ·
                    rfl

theorem cell22_103894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_103894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103894 prefixEnd_103894 := by exact prefixLift 103894
  have htrace : WordTrace (prefixWord ++ tailWord_103894) baseStart_103894 baseEnd_103894 := by
    simpa [prefixWord, tailWord_103894, baseEnd_103894] using wordTrace_append hprefix tailTrace_103894
  have hstable : (prefixWord ++ tailWord_103894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103894).length < 2 ^ (prefixWord ++ tailWord_103894).sum := by decide
  have hdescent : baseEnd_103894 < baseStart_103894 := by decide
  rcases family_descends (prefixWord ++ tailWord_103894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103926 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_103926 : Nat := 118140960795 + 103926 * 2 ^ 59
def prefixEnd_103926 : Nat := 4983230072969 + 3 ^ 40 * 103926 * 2
def baseEnd_103926 : Nat := 35575993666177081831373

theorem tailTrace_103926 : CollatzResearch.WordTrace tailWord_103926 prefixEnd_103926 35575993666177081831373 := by
  unfold tailWord_103926
  simp only [CollatzResearch.WordTrace]
  refine ⟨236905788843832874551727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2526995081000883995218421 236905788843832874551727)
  ·
    refine ⟨355358683265749311827591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236905788843832874551727 355358683265749311827591)
    ·
      refine ⟨533038024898623967741387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355358683265749311827591 533038024898623967741387)
      ·
        refine ⟨799557037347935951612081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533038024898623967741387 799557037347935951612081)
        ·
          refine ⟨599667778010951963709061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799557037347935951612081 599667778010951963709061)
          ·
            refine ⟨112437708377053493195449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 599667778010951963709061 112437708377053493195449)
            ·
              refine ⟨84328281282790119896587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112437708377053493195449 84328281282790119896587)
              ·
                refine ⟨126492421924185179844881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84328281282790119896587 126492421924185179844881)
                ·
                  refine ⟨94869316443138884883661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126492421924185179844881 94869316443138884883661)
                  ·
                    refine ⟨35575993666177081831373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94869316443138884883661 35575993666177081831373)
                    ·
                      rfl

theorem cell22_103926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_103926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103926 prefixEnd_103926 := by exact prefixLift 103926
  have htrace : WordTrace (prefixWord ++ tailWord_103926) baseStart_103926 baseEnd_103926 := by
    simpa [prefixWord, tailWord_103926, baseEnd_103926] using wordTrace_append hprefix tailTrace_103926
  have hstable : (prefixWord ++ tailWord_103926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103926).length < 2 ^ (prefixWord ++ tailWord_103926).sum := by decide
  have hdescent : baseEnd_103926 < baseStart_103926 := by decide
  rcases family_descends (prefixWord ++ tailWord_103926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103965 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_103965 : Nat := 118140960795 + 103965 * 2 ^ 59
def prefixEnd_103965 : Nat := 4983230072969 + 3 ^ 40 * 103965 * 2
def baseEnd_103965 : Nat := 35589344163193980106253

theorem tailTrace_103965 : CollatzResearch.WordTrace tailWord_103965 prefixEnd_103965 35589344163193980106253 := by
  unfold tailWord_103965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791915068360035653497349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2527943378906690435664899 3791915068360035653497349)
  ·
    refine ⟨710984075317506685030753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3791915068360035653497349 710984075317506685030753)
    ·
      refine ⟨533238056488130013773065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 710984075317506685030753 533238056488130013773065)
      ·
        refine ⟨399928542366097510329799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533238056488130013773065 399928542366097510329799)
        ·
          refine ⟨599892813549146265494699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399928542366097510329799 599892813549146265494699)
          ·
            refine ⟨899839220323719398242049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599892813549146265494699 899839220323719398242049)
            ·
              refine ⟨674879415242789548681537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899839220323719398242049 674879415242789548681537)
              ·
                refine ⟨506159561432092161511153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674879415242789548681537 506159561432092161511153)
                ·
                  refine ⟨379619671074069121133365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506159561432092161511153 379619671074069121133365)
                  ·
                    refine ⟨35589344163193980106253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 379619671074069121133365 35589344163193980106253)
                    ·
                      rfl

theorem cell22_103965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_103965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103965 prefixEnd_103965 := by exact prefixLift 103965
  have htrace : WordTrace (prefixWord ++ tailWord_103965) baseStart_103965 baseEnd_103965 := by
    simpa [prefixWord, tailWord_103965, baseEnd_103965] using wordTrace_append hprefix tailTrace_103965
  have hstable : (prefixWord ++ tailWord_103965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103965).length < 2 ^ (prefixWord ++ tailWord_103965).sum := by decide
  have hdescent : baseEnd_103965 < baseStart_103965 := by decide
  rcases family_descends (prefixWord ++ tailWord_103965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103982 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_103982 : Nat := 118140960795 + 103982 * 2 ^ 59
def prefixEnd_103982 : Nat := 4983230072969 + 3 ^ 40 * 103982 * 2
def baseEnd_103982 : Nat := 35595163610611602431201

theorem tailTrace_103982 : CollatzResearch.WordTrace tailWord_103982 prefixEnd_103982 35595163610611602431201 := by
  unfold tailWord_103982
  simp only [CollatzResearch.WordTrace]
  refine ⟨474066888662305944608275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2528356739532298371244133 474066888662305944608275)
  ·
    refine ⟨711100332993458916912413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 474066888662305944608275 711100332993458916912413)
    ·
      refine ⟨266662624872547093842155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 711100332993458916912413 266662624872547093842155)
      ·
        refine ⟨399993937308820640763233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266662624872547093842155 399993937308820640763233)
        ·
          refine ⟨299995452981615480572425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399993937308820640763233 299995452981615480572425)
          ·
            refine ⟨224996589736211610429319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299995452981615480572425 224996589736211610429319)
            ·
              refine ⟨337494884604317415643979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224996589736211610429319 337494884604317415643979)
              ·
                refine ⟨506242326906476123465969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337494884604317415643979 506242326906476123465969)
                ·
                  refine ⟨379681745179857092599477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506242326906476123465969 379681745179857092599477)
                  ·
                    refine ⟨35595163610611602431201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 379681745179857092599477 35595163610611602431201)
                    ·
                      rfl

theorem cell22_103982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_103982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_103982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_103982 prefixEnd_103982 := by exact prefixLift 103982
  have htrace : WordTrace (prefixWord ++ tailWord_103982) baseStart_103982 baseEnd_103982 := by
    simpa [prefixWord, tailWord_103982, baseEnd_103982] using wordTrace_append hprefix tailTrace_103982
  have hstable : (prefixWord ++ tailWord_103982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103982).length < 2 ^ (prefixWord ++ tailWord_103982).sum := by decide
  have hdescent : baseEnd_103982 < baseStart_103982 := by decide
  rcases family_descends (prefixWord ++ tailWord_103982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104010 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_104010 : Nat := 118140960795 + 104010 * 2 ^ 59
def prefixEnd_104010 : Nat := 4983230072969 + 3 ^ 40 * 104010 * 2
def baseEnd_104010 : Nat := 35604748582828862731115

theorem tailTrace_104010 : CollatzResearch.WordTrace tailWord_104010 prefixEnd_104010 35604748582828862731115 := by
  unfold tailWord_104010
  simp only [CollatzResearch.WordTrace]
  refine ⟨948389088299252084721371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2529037568798005559256989 948389088299252084721371)
  ·
    refine ⟨1422583632448878127082057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948389088299252084721371 1422583632448878127082057)
    ·
      refine ⟨1066937724336658595311543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1422583632448878127082057 1066937724336658595311543)
      ·
        refine ⟨1600406586504987892967315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066937724336658595311543 1600406586504987892967315)
        ·
          refine ⟨2400609879757481839450973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600406586504987892967315 2400609879757481839450973)
          ·
            refine ⟨900228704909055689794115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2400609879757481839450973 900228704909055689794115)
            ·
              refine ⟨1350343057363583534691173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900228704909055689794115 1350343057363583534691173)
              ·
                refine ⟨253189323255671912754595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1350343057363583534691173 253189323255671912754595)
                ·
                  refine ⟨379783984883507869131893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253189323255671912754595 379783984883507869131893)
                  ·
                    refine ⟨35604748582828862731115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 379783984883507869131893 35604748582828862731115)
                    ·
                      rfl

theorem cell22_104010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_104010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104010 prefixEnd_104010 := by exact prefixLift 104010
  have htrace : WordTrace (prefixWord ++ tailWord_104010) baseStart_104010 baseEnd_104010 := by
    simpa [prefixWord, tailWord_104010, baseEnd_104010] using wordTrace_append hprefix tailTrace_104010
  have hstable : (prefixWord ++ tailWord_104010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104010).length < 2 ^ (prefixWord ++ tailWord_104010).sum := by decide
  have hdescent : baseEnd_104010 < baseStart_104010 := by decide
  rcases family_descends (prefixWord ++ tailWord_104010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104012 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 4]
def baseStart_104012 : Nat := 118140960795 + 104012 * 2 ^ 59
def prefixEnd_104012 : Nat := 4983230072969 + 3 ^ 40 * 104012 * 2
def baseEnd_104012 : Nat := 11868477741233841393703

theorem tailTrace_104012 : CollatzResearch.WordTrace tailWord_104012 prefixEnd_104012 11868477741233841393703 := by
  unfold tailWord_104012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896814649594881340229145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2529086199459841786972193 1896814649594881340229145)
  ·
    refine ⟨1422610987196161005171859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1896814649594881340229145 1422610987196161005171859)
    ·
      refine ⟨2133916480794241507757789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422610987196161005171859 2133916480794241507757789)
      ·
        refine ⟨800218680297840565409171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2133916480794241507757789 800218680297840565409171)
        ·
          refine ⟨1200328020446760848113757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800218680297840565409171 1200328020446760848113757)
          ·
            refine ⟨450123007667535318042659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1200328020446760848113757 450123007667535318042659)
            ·
              refine ⟨675184511501302977063989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450123007667535318042659 675184511501302977063989)
              ·
                refine ⟨63298547953247154099749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 675184511501302977063989 63298547953247154099749)
                ·
                  refine ⟨11868477741233841393703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63298547953247154099749 11868477741233841393703)
                  ·
                    rfl

theorem cell22_104012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_104012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104012 prefixEnd_104012 := by exact prefixLift 104012
  have htrace : WordTrace (prefixWord ++ tailWord_104012) baseStart_104012 baseEnd_104012 := by
    simpa [prefixWord, tailWord_104012, baseEnd_104012] using wordTrace_append hprefix tailTrace_104012
  have hstable : (prefixWord ++ tailWord_104012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104012).length < 2 ^ (prefixWord ++ tailWord_104012).sum := by decide
  have hdescent : baseEnd_104012 < baseStart_104012 := by decide
  rcases family_descends (prefixWord ++ tailWord_104012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104025 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_104025 : Nat := 118140960795 + 104025 * 2 ^ 59
def prefixEnd_104025 : Nat := 4983230072969 + 3 ^ 40 * 104025 * 2
def baseEnd_104025 : Nat := 35609883389373823606069

theorem tailTrace_104025 : CollatzResearch.WordTrace tailWord_104025 prefixEnd_104025 35609883389373823606069 := by
  unfold tailWord_104025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794103448142665900681529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2529402298761777267121019 3794103448142665900681529)
  ·
    refine ⟨2845577586106999425511147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3794103448142665900681529 2845577586106999425511147)
    ·
      refine ⟨4268366379160499138266721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845577586106999425511147 4268366379160499138266721)
      ·
        refine ⟨3201274784370374353700041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4268366379160499138266721 3201274784370374353700041)
        ·
          refine ⟨2400956088277780765275031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201274784370374353700041 2400956088277780765275031)
          ·
            refine ⟨3601434132416671147912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400956088277780765275031 3601434132416671147912547)
            ·
              refine ⟨5402151198625006721868821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601434132416671147912547 5402151198625006721868821)
              ·
                refine ⟨253225837435547190087601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5402151198625006721868821 253225837435547190087601)
                ·
                  refine ⟨189919378076660392565701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253225837435547190087601 189919378076660392565701)
                  ·
                    refine ⟨35609883389373823606069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189919378076660392565701 35609883389373823606069)
                    ·
                      rfl

theorem cell22_104025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_104025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104025 prefixEnd_104025 := by exact prefixLift 104025
  have htrace : WordTrace (prefixWord ++ tailWord_104025) baseStart_104025 baseEnd_104025 := by
    simpa [prefixWord, tailWord_104025, baseEnd_104025] using wordTrace_append hprefix tailTrace_104025
  have hstable : (prefixWord ++ tailWord_104025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104025).length < 2 ^ (prefixWord ++ tailWord_104025).sum := by decide
  have hdescent : baseEnd_104025 < baseStart_104025 := by decide
  rcases family_descends (prefixWord ++ tailWord_104025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104095 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 2, 3]
def baseStart_104095 : Nat := 118140960795 + 104095 * 2 ^ 59
def prefixEnd_104095 : Nat := 4983230072969 + 3 ^ 40 * 104095 * 2
def baseEnd_104095 : Nat := 35633845819916974355855

theorem tailTrace_104095 : CollatzResearch.WordTrace tailWord_104095 prefixEnd_104095 35633845819916974355855 := by
  unfold tailWord_104095
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796656557889067855729739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2531104371926045237153159 3796656557889067855729739)
  ·
    refine ⟨5694984836833601783594609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3796656557889067855729739 5694984836833601783594609)
    ·
      refine ⟨4271238627625201337695957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5694984836833601783594609 4271238627625201337695957)
      ·
        refine ⟨100107155334965656352249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4271238627625201337695957 100107155334965656352249)
        ·
          refine ⟨75080366501224242264187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100107155334965656352249 75080366501224242264187)
          ·
            refine ⟨112620549751836363396281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75080366501224242264187 112620549751836363396281)
            ·
              refine ⟨84465412313877272547211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112620549751836363396281 84465412313877272547211)
              ·
                refine ⟨126698118470815908820817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84465412313877272547211 126698118470815908820817)
                ·
                  refine ⟨95023588853111931615613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126698118470815908820817 95023588853111931615613)
                  ·
                    refine ⟨35633845819916974355855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95023588853111931615613 35633845819916974355855)
                    ·
                      rfl

theorem cell22_104095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_104095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104095 prefixEnd_104095 := by exact prefixLift 104095
  have htrace : WordTrace (prefixWord ++ tailWord_104095) baseStart_104095 baseEnd_104095 := by
    simpa [prefixWord, tailWord_104095, baseEnd_104095] using wordTrace_append hprefix tailTrace_104095
  have hstable : (prefixWord ++ tailWord_104095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104095).length < 2 ^ (prefixWord ++ tailWord_104095).sum := by decide
  have hdescent : baseEnd_104095 < baseStart_104095 := by decide
  rcases family_descends (prefixWord ++ tailWord_104095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104140 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 1, 3]
def baseStart_104140 : Nat := 118140960795 + 104140 * 2 ^ 59
def prefixEnd_104140 : Nat := 4983230072969 + 3 ^ 40 * 104140 * 2
def baseEnd_104140 : Nat := 35649250239551856980717

theorem tailTrace_104140 : CollatzResearch.WordTrace tailWord_104140 prefixEnd_104140 35649250239551856980717 := by
  unfold tailWord_104140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1899148921363020270558937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2532198561817360360745249 1899148921363020270558937)
  ·
    refine ⟨1424361691022265202919203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1899148921363020270558937 1424361691022265202919203)
    ·
      refine ⟨2136542536533397804378805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424361691022265202919203 2136542536533397804378805)
      ·
        refine ⟨200300862800006044160513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2136542536533397804378805 200300862800006044160513)
        ·
          refine ⟨150225647100004533120385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200300862800006044160513 150225647100004533120385)
          ·
            refine ⟨112669235325003399840289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150225647100004533120385 112669235325003399840289)
            ·
              refine ⟨84501926493752549880217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112669235325003399840289 84501926493752549880217)
              ·
                refine ⟨63376444870314412410163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84501926493752549880217 63376444870314412410163)
                ·
                  refine ⟨95064667305471618615245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63376444870314412410163 95064667305471618615245)
                  ·
                    refine ⟨35649250239551856980717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95064667305471618615245 35649250239551856980717)
                    ·
                      rfl

theorem cell22_104140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_104140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104140 prefixEnd_104140 := by exact prefixLift 104140
  have htrace : WordTrace (prefixWord ++ tailWord_104140) baseStart_104140 baseEnd_104140 := by
    simpa [prefixWord, tailWord_104140, baseEnd_104140] using wordTrace_append hprefix tailTrace_104140
  have hstable : (prefixWord ++ tailWord_104140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104140).length < 2 ^ (prefixWord ++ tailWord_104140).sum := by decide
  have hdescent : baseEnd_104140 < baseStart_104140 := by decide
  rcases family_descends (prefixWord ++ tailWord_104140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104177 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_104177 : Nat := 118140960795 + 104177 * 2 ^ 59
def prefixEnd_104177 : Nat := 4983230072969 + 3 ^ 40 * 104177 * 2
def baseEnd_104177 : Nat := 35661916095696093805603

theorem tailTrace_104177 : CollatzResearch.WordTrace tailWord_104177 prefixEnd_104177 35661916095696093805603 := by
  unfold tailWord_104177
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799647343591995860214785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2533098229061330573476523 3799647343591995860214785)
  ·
    refine ⟨2849735507693996895161089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3799647343591995860214785 2849735507693996895161089)
    ·
      refine ⟨2137301630770497671370817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849735507693996895161089 2137301630770497671370817)
      ·
        refine ⟨1602976223077873253528113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2137301630770497671370817 1602976223077873253528113)
        ·
          refine ⟨1202232167308404940146085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1602976223077873253528113 1202232167308404940146085)
          ·
            refine ⟨225418531370325926277391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1202232167308404940146085 225418531370325926277391)
            ·
              refine ⟨338127797055488889416087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225418531370325926277391 338127797055488889416087)
              ·
                refine ⟨507191695583233334124131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338127797055488889416087 507191695583233334124131)
                ·
                  refine ⟨760787543374850001186197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507191695583233334124131 760787543374850001186197)
                  ·
                    refine ⟨35661916095696093805603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 760787543374850001186197 35661916095696093805603)
                    ·
                      rfl

theorem cell22_104177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_104177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104177 prefixEnd_104177 := by exact prefixLift 104177
  have htrace : WordTrace (prefixWord ++ tailWord_104177) baseStart_104177 baseEnd_104177 := by
    simpa [prefixWord, tailWord_104177, baseEnd_104177] using wordTrace_append hprefix tailTrace_104177
  have hstable : (prefixWord ++ tailWord_104177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104177).length < 2 ^ (prefixWord ++ tailWord_104177).sum := by decide
  have hdescent : baseEnd_104177 < baseStart_104177 := by decide
  rcases family_descends (prefixWord ++ tailWord_104177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104194 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_104194 : Nat := 118140960795 + 104194 * 2 ^ 59
def prefixEnd_104194 : Nat := 4983230072969 + 3 ^ 40 * 104194 * 2
def baseEnd_104194 : Nat := 35667735543113716130551

theorem tailTrace_104194 : CollatzResearch.WordTrace tailWord_104194 prefixEnd_104194 35667735543113716130551 := by
  unfold tailWord_104194
  simp only [CollatzResearch.WordTrace]
  refine ⟨950066846132601940895909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2533511589686938509055757 950066846132601940895909)
  ·
    refine ⟨178137533649862863917983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 950066846132601940895909 178137533649862863917983)
    ·
      refine ⟨267206300474794295876975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178137533649862863917983 267206300474794295876975)
      ·
        refine ⟨400809450712191443815463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267206300474794295876975 400809450712191443815463)
        ·
          refine ⟨601214176068287165723195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400809450712191443815463 601214176068287165723195)
          ·
            refine ⟨901821264102430748584793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601214176068287165723195 901821264102430748584793)
            ·
              refine ⟨676365948076823061438595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901821264102430748584793 676365948076823061438595)
              ·
                refine ⟨1014548922115234592157893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676365948076823061438595 1014548922115234592157893)
                ·
                  refine ⟨190227922896606486029605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014548922115234592157893 190227922896606486029605)
                  ·
                    refine ⟨35667735543113716130551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190227922896606486029605 35667735543113716130551)
                    ·
                      rfl

theorem cell22_104194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_104194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104194 prefixEnd_104194 := by exact prefixLift 104194
  have htrace : WordTrace (prefixWord ++ tailWord_104194) baseStart_104194 baseEnd_104194 := by
    simpa [prefixWord, tailWord_104194, baseEnd_104194] using wordTrace_append hprefix tailTrace_104194
  have hstable : (prefixWord ++ tailWord_104194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104194).length < 2 ^ (prefixWord ++ tailWord_104194).sum := by decide
  have hdescent : baseEnd_104194 < baseStart_104194 := by decide
  rcases family_descends (prefixWord ++ tailWord_104194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104196 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_104196 : Nat := 118140960795 + 104196 * 2 ^ 59
def prefixEnd_104196 : Nat := 4983230072969 + 3 ^ 40 * 104196 * 2
def baseEnd_104196 : Nat := 35668420183986377580545

theorem tailTrace_104196 : CollatzResearch.WordTrace tailWord_104196 prefixEnd_104196 35668420183986377580545 := by
  unfold tailWord_104196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900170165261581052578221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2533560220348774736770961 1900170165261581052578221)
  ·
    refine ⟨712563811973092894716833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1900170165261581052578221 712563811973092894716833)
    ·
      refine ⟨534422858979819671037625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 712563811973092894716833 534422858979819671037625)
      ·
        refine ⟨400817144234864753278219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534422858979819671037625 400817144234864753278219)
        ·
          refine ⟨601225716352297129917329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400817144234864753278219 601225716352297129917329)
          ·
            refine ⟨450919287264222847437997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601225716352297129917329 450919287264222847437997)
            ·
              refine ⟨169094732724083567789249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450919287264222847437997 169094732724083567789249)
              ·
                refine ⟨126821049543062675841937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169094732724083567789249 126821049543062675841937)
                ·
                  refine ⟨95115787157297006881453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126821049543062675841937 95115787157297006881453)
                  ·
                    refine ⟨35668420183986377580545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95115787157297006881453 35668420183986377580545)
                    ·
                      rfl

theorem cell22_104196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_104196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104196 prefixEnd_104196 := by exact prefixLift 104196
  have htrace : WordTrace (prefixWord ++ tailWord_104196) baseStart_104196 baseEnd_104196 := by
    simpa [prefixWord, tailWord_104196, baseEnd_104196] using wordTrace_append hprefix tailTrace_104196
  have hstable : (prefixWord ++ tailWord_104196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104196).length < 2 ^ (prefixWord ++ tailWord_104196).sum := by decide
  have hdescent : baseEnd_104196 < baseStart_104196 := by decide
  rcases family_descends (prefixWord ++ tailWord_104196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104224 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_104224 : Nat := 118140960795 + 104224 * 2 ^ 59
def prefixEnd_104224 : Nat := 4983230072969 + 3 ^ 40 * 104224 * 2
def baseEnd_104224 : Nat := 35678005156203637880459

theorem tailTrace_104224 : CollatzResearch.WordTrace tailWord_104224 prefixEnd_104224 35678005156203637880459 := by
  unfold tailWord_104224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900680787210861443587863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2534241049614481924783817 1900680787210861443587863)
  ·
    refine ⟨2851021180816292165381795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900680787210861443587863 2851021180816292165381795)
    ·
      refine ⟨4276531771224438248072693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851021180816292165381795 4276531771224438248072693)
      ·
        refine ⟨400924853552291085756815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4276531771224438248072693 400924853552291085756815)
        ·
          refine ⟨601387280328436628635223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400924853552291085756815 601387280328436628635223)
          ·
            refine ⟨902080920492654942952835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601387280328436628635223 902080920492654942952835)
            ·
              refine ⟨1353121380738982414429253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902080920492654942952835 1353121380738982414429253)
              ·
                refine ⟨253710258888559202705485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1353121380738982414429253 253710258888559202705485)
                ·
                  refine ⟨95141347083209701014557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253710258888559202705485 95141347083209701014557)
                  ·
                    refine ⟨35678005156203637880459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95141347083209701014557 35678005156203637880459)
                    ·
                      rfl

theorem cell22_104224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_104224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104224 prefixEnd_104224 := by exact prefixLift 104224
  have htrace : WordTrace (prefixWord ++ tailWord_104224) baseStart_104224 baseEnd_104224 := by
    simpa [prefixWord, tailWord_104224, baseEnd_104224] using wordTrace_append hprefix tailTrace_104224
  have hstable : (prefixWord ++ tailWord_104224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104224).length < 2 ^ (prefixWord ++ tailWord_104224).sum := by decide
  have hdescent : baseEnd_104224 < baseStart_104224 := by decide
  rcases family_descends (prefixWord ++ tailWord_104224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104252 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_104252 : Nat := 118140960795 + 104252 * 2 ^ 59
def prefixEnd_104252 : Nat := 4983230072969 + 3 ^ 40 * 104252 * 2
def baseEnd_104252 : Nat := 35687590128420898180373

theorem tailTrace_104252 : CollatzResearch.WordTrace tailWord_104252 prefixEnd_104252 35687590128420898180373 := by
  unfold tailWord_104252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901191409160141834597505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2534921878880189112796673 1901191409160141834597505)
  ·
    refine ⟨1425893556870106375948129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1901191409160141834597505 1425893556870106375948129)
    ·
      refine ⟨1069420167652579781961097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1425893556870106375948129 1069420167652579781961097)
      ·
        refine ⟨802065125739434836470823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069420167652579781961097 802065125739434836470823)
        ·
          refine ⟨1203097688609152254706235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802065125739434836470823 1203097688609152254706235)
          ·
            refine ⟨1804646532913728382059353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203097688609152254706235 1804646532913728382059353)
            ·
              refine ⟨1353484899685296286544515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804646532913728382059353 1353484899685296286544515)
              ·
                refine ⟨2030227349527944429816773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353484899685296286544515 2030227349527944429816773)
                ·
                  refine ⟨380667628036489580590645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030227349527944429816773 380667628036489580590645)
                  ·
                    refine ⟨35687590128420898180373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 380667628036489580590645 35687590128420898180373)
                    ·
                      rfl

theorem cell22_104252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_104252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104252 prefixEnd_104252 := by exact prefixLift 104252
  have htrace : WordTrace (prefixWord ++ tailWord_104252) baseStart_104252 baseEnd_104252 := by
    simpa [prefixWord, tailWord_104252, baseEnd_104252] using wordTrace_append hprefix tailTrace_104252
  have hstable : (prefixWord ++ tailWord_104252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104252).length < 2 ^ (prefixWord ++ tailWord_104252).sum := by decide
  have hdescent : baseEnd_104252 < baseStart_104252 := by decide
  rcases family_descends (prefixWord ++ tailWord_104252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104254 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_104254 : Nat := 118140960795 + 104254 * 2 ^ 59
def prefixEnd_104254 : Nat := 4983230072969 + 3 ^ 40 * 104254 * 2
def baseEnd_104254 : Nat := 11896091589764519876789

theorem tailTrace_104254 : CollatzResearch.WordTrace tailWord_104254 prefixEnd_104254 11896091589764519876789 := by
  unfold tailWord_104254
  simp only [CollatzResearch.WordTrace]
  refine ⟨475306970539129751345977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2534970509542025340511877 475306970539129751345977)
  ·
    refine ⟨356480227904347313509483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 475306970539129751345977 356480227904347313509483)
    ·
      refine ⟨534720341856520970264225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356480227904347313509483 534720341856520970264225)
      ·
        refine ⟨401040256392390727698169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534720341856520970264225 401040256392390727698169)
        ·
          refine ⟨300780192294293045773627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401040256392390727698169 300780192294293045773627)
          ·
            refine ⟨451170288441439568660441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300780192294293045773627 451170288441439568660441)
            ·
              refine ⟨338377716331079676495331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451170288441439568660441 338377716331079676495331)
              ·
                refine ⟨507566574496619514742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338377716331079676495331 507566574496619514742997)
                ·
                  refine ⟨11896091589764519876789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 507566574496619514742997 11896091589764519876789)
                  ·
                    rfl

theorem cell22_104254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_104254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104254 prefixEnd_104254 := by exact prefixLift 104254
  have htrace : WordTrace (prefixWord ++ tailWord_104254) baseStart_104254 baseEnd_104254 := by
    simpa [prefixWord, tailWord_104254, baseEnd_104254] using wordTrace_append hprefix tailTrace_104254
  have hstable : (prefixWord ++ tailWord_104254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104254).length < 2 ^ (prefixWord ++ tailWord_104254).sum := by decide
  have hdescent : baseEnd_104254 < baseStart_104254 := by decide
  rcases family_descends (prefixWord ++ tailWord_104254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104282 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_104282 : Nat := 118140960795 + 104282 * 2 ^ 59
def prefixEnd_104282 : Nat := 4983230072969 + 3 ^ 40 * 104282 * 2
def baseEnd_104282 : Nat := 11899286580503606643427

theorem tailTrace_104282 : CollatzResearch.WordTrace tailWord_104282 prefixEnd_104282 11899286580503606643427 := by
  unfold tailWord_104282
  simp only [CollatzResearch.WordTrace]
  refine ⟨950869252052899698196775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2535651338807732528524733 950869252052899698196775)
  ·
    refine ⟨1426303878079349547295163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 950869252052899698196775 1426303878079349547295163)
    ·
      refine ⟨2139455817119024320942745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426303878079349547295163 2139455817119024320942745)
      ·
        refine ⟨1604591862839268240707059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2139455817119024320942745 1604591862839268240707059)
        ·
          refine ⟨2406887794258902361060589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604591862839268240707059 2406887794258902361060589)
          ·
            refine ⟨902582922847088385397721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2406887794258902361060589 902582922847088385397721)
            ·
              refine ⟨676937192135316289048291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902582922847088385397721 676937192135316289048291)
              ·
                refine ⟨1015405788202974433572437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676937192135316289048291 1015405788202974433572437)
                ·
                  refine ⟨11899286580503606643427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1015405788202974433572437 11899286580503606643427)
                  ·
                    rfl

theorem cell22_104282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_104282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104282 prefixEnd_104282 := by exact prefixLift 104282
  have htrace : WordTrace (prefixWord ++ tailWord_104282) baseStart_104282 baseEnd_104282 := by
    simpa [prefixWord, tailWord_104282, baseEnd_104282] using wordTrace_append hprefix tailTrace_104282
  have hstable : (prefixWord ++ tailWord_104282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104282).length < 2 ^ (prefixWord ++ tailWord_104282).sum := by decide
  have hdescent : baseEnd_104282 < baseStart_104282 := by decide
  rcases family_descends (prefixWord ++ tailWord_104282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104299 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 4]
def baseStart_104299 : Nat := 118140960795 + 104299 * 2 ^ 59
def prefixEnd_104299 : Nat := 4983230072969 + 3 ^ 40 * 104299 * 2
def baseEnd_104299 : Nat := 11901226396309480751743

theorem tailTrace_104299 : CollatzResearch.WordTrace tailWord_104299 prefixEnd_104299 11901226396309480751743 := by
  unfold tailWord_104299
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804097049150010696155951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2536064699433340464103967 3804097049150010696155951)
  ·
    refine ⟨5706145573725016044233927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3804097049150010696155951 5706145573725016044233927)
    ·
      refine ⟨8559218360587524066350891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5706145573725016044233927 8559218360587524066350891)
      ·
        refine ⟨12838827540881286099526337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8559218360587524066350891 12838827540881286099526337)
        ·
          refine ⟨9629120655660964574644753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12838827540881286099526337 9629120655660964574644753)
          ·
            refine ⟨7221840491745723430983565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9629120655660964574644753 7221840491745723430983565)
            ·
              refine ⟨2708190184404646286618837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7221840491745723430983565 2708190184404646286618837)
              ·
                refine ⟨63473207446983897342629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2708190184404646286618837 63473207446983897342629)
                ·
                  refine ⟨11901226396309480751743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63473207446983897342629 11901226396309480751743)
                  ·
                    rfl

theorem cell22_104299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 4].length) (baseStart_104299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104299 prefixEnd_104299 := by exact prefixLift 104299
  have htrace : WordTrace (prefixWord ++ tailWord_104299) baseStart_104299 baseEnd_104299 := by
    simpa [prefixWord, tailWord_104299, baseEnd_104299] using wordTrace_append hprefix tailTrace_104299
  have hstable : (prefixWord ++ tailWord_104299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104299).length < 2 ^ (prefixWord ++ tailWord_104299).sum := by decide
  have hdescent : baseEnd_104299 < baseStart_104299 := by decide
  rcases family_descends (prefixWord ++ tailWord_104299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104314 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_104314 : Nat := 118140960795 + 104314 * 2 ^ 59
def prefixEnd_104314 : Nat := 4983230072969 + 3 ^ 40 * 104314 * 2
def baseEnd_104314 : Nat := 35708813995473403130183

theorem tailTrace_104314 : CollatzResearch.WordTrace tailWord_104314 prefixEnd_104314 35708813995473403130183 := by
  unfold tailWord_104314
  simp only [CollatzResearch.WordTrace]
  refine ⟨951161036023917064487999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2536429429397112171967997 951161036023917064487999)
  ·
    refine ⟨1426741554035875596731999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951161036023917064487999 1426741554035875596731999)
    ·
      refine ⟨2140112331053813395097999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426741554035875596731999 2140112331053813395097999)
      ·
        refine ⟨3210168496580720092646999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140112331053813395097999 3210168496580720092646999)
        ·
          refine ⟨4815252744871080138970499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210168496580720092646999 4815252744871080138970499)
          ·
            refine ⟨7222879117306620208455749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815252744871080138970499 7222879117306620208455749)
            ·
              refine ⟨1354289834494991289085453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7222879117306620208455749 1354289834494991289085453)
              ·
                refine ⟨507858687935621733407045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354289834494991289085453 507858687935621733407045)
                ·
                  refine ⟨95223503987929075013821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507858687935621733407045 95223503987929075013821)
                  ·
                    refine ⟨35708813995473403130183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95223503987929075013821 35708813995473403130183)
                    ·
                      rfl

theorem cell22_104314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_104314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104314 prefixEnd_104314 := by exact prefixLift 104314
  have htrace : WordTrace (prefixWord ++ tailWord_104314) baseStart_104314 baseEnd_104314 := by
    simpa [prefixWord, tailWord_104314, baseEnd_104314] using wordTrace_append hprefix tailTrace_104314
  have hstable : (prefixWord ++ tailWord_104314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104314).length < 2 ^ (prefixWord ++ tailWord_104314).sum := by decide
  have hdescent : baseEnd_104314 < baseStart_104314 := by decide
  rcases family_descends (prefixWord ++ tailWord_104314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104346 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_104346 : Nat := 118140960795 + 104346 * 2 ^ 59
def prefixEnd_104346 : Nat := 4983230072969 + 3 ^ 40 * 104346 * 2
def baseEnd_104346 : Nat := 35719768249435986330085

theorem tailTrace_104346 : CollatzResearch.WordTrace tailWord_104346 prefixEnd_104346 35719768249435986330085 := by
  unfold tailWord_104346
  simp only [CollatzResearch.WordTrace]
  refine ⟨951452819994934430779223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2537207519986491815411261 951452819994934430779223)
  ·
    refine ⟨1427179229992401646168835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951452819994934430779223 1427179229992401646168835)
    ·
      refine ⟨2140768844988602469253253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1427179229992401646168835 2140768844988602469253253)
      ·
        refine ⟨401394158435362962984985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2140768844988602469253253 401394158435362962984985)
        ·
          refine ⟨301045618826522222238739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401394158435362962984985 301045618826522222238739)
          ·
            refine ⟨451568428239783333358109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301045618826522222238739 451568428239783333358109)
            ·
              refine ⟨169338160589918750009291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 451568428239783333358109 169338160589918750009291)
              ·
                refine ⟨254007240884878125013937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169338160589918750009291 254007240884878125013937)
                ·
                  refine ⟨190505430663658593760453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254007240884878125013937 190505430663658593760453)
                  ·
                    refine ⟨35719768249435986330085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190505430663658593760453 35719768249435986330085)
                    ·
                      rfl

theorem cell22_104346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_104346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104346 prefixEnd_104346 := by exact prefixLift 104346
  have htrace : WordTrace (prefixWord ++ tailWord_104346) baseStart_104346 baseEnd_104346 := by
    simpa [prefixWord, tailWord_104346, baseEnd_104346] using wordTrace_append hprefix tailTrace_104346
  have hstable : (prefixWord ++ tailWord_104346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104346).length < 2 ^ (prefixWord ++ tailWord_104346).sum := by decide
  have hdescent : baseEnd_104346 < baseStart_104346 := by decide
  rcases family_descends (prefixWord ++ tailWord_104346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104376 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_104376 : Nat := 118140960795 + 104376 * 2 ^ 59
def prefixEnd_104376 : Nat := 4983230072969 + 3 ^ 40 * 104376 * 2
def baseEnd_104376 : Nat := 35730037862525908079993

theorem tailTrace_104376 : CollatzResearch.WordTrace tailWord_104376 prefixEnd_104376 35730037862525908079993 := by
  unfold tailWord_104376
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903452734935526423354491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2537936979914035231139321 1903452734935526423354491)
  ·
    refine ⟨2855179102403289635031737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903452734935526423354491 2855179102403289635031737)
    ·
      refine ⟨2141384326802467226273803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2855179102403289635031737 2141384326802467226273803)
      ·
        refine ⟨3212076490203700839410705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141384326802467226273803 3212076490203700839410705)
        ·
          refine ⟨2409057367652775629558029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3212076490203700839410705 2409057367652775629558029)
          ·
            refine ⟨903396512869790861084261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2409057367652775629558029 903396512869790861084261)
            ·
              refine ⟨169386846163085786453299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 903396512869790861084261 169386846163085786453299)
              ·
                refine ⟨254080269244628679679949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169386846163085786453299 254080269244628679679949)
                ·
                  refine ⟨95280100966735754879981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254080269244628679679949 95280100966735754879981)
                  ·
                    refine ⟨35730037862525908079993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95280100966735754879981 35730037862525908079993)
                    ·
                      rfl

theorem cell22_104376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_104376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104376 prefixEnd_104376 := by exact prefixLift 104376
  have htrace : WordTrace (prefixWord ++ tailWord_104376) baseStart_104376 baseEnd_104376 := by
    simpa [prefixWord, tailWord_104376, baseEnd_104376] using wordTrace_append hprefix tailTrace_104376
  have hstable : (prefixWord ++ tailWord_104376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104376).length < 2 ^ (prefixWord ++ tailWord_104376).sum := by decide
  have hdescent : baseEnd_104376 < baseStart_104376 := by decide
  rcases family_descends (prefixWord ++ tailWord_104376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104453 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_104453 : Nat := 118140960795 + 104453 * 2 ^ 59
def prefixEnd_104453 : Nat := 4983230072969 + 3 ^ 40 * 104453 * 2
def baseEnd_104453 : Nat := 35756396536123373904757

theorem tailTrace_104453 : CollatzResearch.WordTrace tailWord_104453 prefixEnd_104453 35756396536123373904757 := by
  unfold tailWord_104453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809713890592094997262013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2539809260394729998174675 3809713890592094997262013)
  ·
    refine ⟨1428642708972035623973255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3809713890592094997262013 1428642708972035623973255)
    ·
      refine ⟨2142964063458053435959883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428642708972035623973255 2142964063458053435959883)
      ·
        refine ⟨3214446095187080153939825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142964063458053435959883 3214446095187080153939825)
        ·
          refine ⟨2410834571390310115454869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214446095187080153939825 2410834571390310115454869)
          ·
            refine ⟨113007870533920786661947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2410834571390310115454869 113007870533920786661947)
            ·
              refine ⟨169511805800881179992921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113007870533920786661947 169511805800881179992921)
              ·
                refine ⟨127133854350660884994691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169511805800881179992921 127133854350660884994691)
                ·
                  refine ⟨190700781525991327492037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127133854350660884994691 190700781525991327492037)
                  ·
                    refine ⟨35756396536123373904757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190700781525991327492037 35756396536123373904757)
                    ·
                      rfl

theorem cell22_104453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_104453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104453 prefixEnd_104453 := by exact prefixLift 104453
  have htrace : WordTrace (prefixWord ++ tailWord_104453) baseStart_104453 baseEnd_104453 := by
    simpa [prefixWord, tailWord_104453, baseEnd_104453] using wordTrace_append hprefix tailTrace_104453
  have hstable : (prefixWord ++ tailWord_104453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104453).length < 2 ^ (prefixWord ++ tailWord_104453).sum := by decide
  have hdescent : baseEnd_104453 < baseStart_104453 := by decide
  rcases family_descends (prefixWord ++ tailWord_104453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104464 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_104464 : Nat := 118140960795 + 104464 * 2 ^ 59
def prefixEnd_104464 : Nat := 4983230072969 + 3 ^ 40 * 104464 * 2
def baseEnd_104464 : Nat := 35760162060923011879723

theorem tailTrace_104464 : CollatzResearch.WordTrace tailWord_104464 prefixEnd_104464 35760162060923011879723 := by
  unfold tailWord_104464
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905057546776121937956223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2540076729034829250608297 1905057546776121937956223)
  ·
    refine ⟨2857586320164182906934335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905057546776121937956223 2857586320164182906934335)
    ·
      refine ⟨4286379480246274360401503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2857586320164182906934335 4286379480246274360401503)
      ·
        refine ⟨6429569220369411540602255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286379480246274360401503 6429569220369411540602255)
        ·
          refine ⟨9644353830554117310903383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6429569220369411540602255 9644353830554117310903383)
          ·
            refine ⟨14466530745831175966355075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644353830554117310903383 14466530745831175966355075)
            ·
              refine ⟨21699796118746763949532613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14466530745831175966355075 21699796118746763949532613)
              ·
                refine ⟨4068711772265018240537365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21699796118746763949532613 4068711772265018240537365)
                ·
                  refine ⟨190720864324922730025189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4068711772265018240537365 190720864324922730025189)
                  ·
                    refine ⟨35760162060923011879723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190720864324922730025189 35760162060923011879723)
                    ·
                      rfl

theorem cell22_104464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_104464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104464 prefixEnd_104464 := by exact prefixLift 104464
  have htrace : WordTrace (prefixWord ++ tailWord_104464) baseStart_104464 baseEnd_104464 := by
    simpa [prefixWord, tailWord_104464, baseEnd_104464] using wordTrace_append hprefix tailTrace_104464
  have hstable : (prefixWord ++ tailWord_104464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104464).length < 2 ^ (prefixWord ++ tailWord_104464).sum := by decide
  have hdescent : baseEnd_104464 < baseStart_104464 := by decide
  rcases family_descends (prefixWord ++ tailWord_104464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104483 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 2, 3]
def baseStart_104483 : Nat := 118140960795 + 104483 * 2 ^ 59
def prefixEnd_104483 : Nat := 4983230072969 + 3 ^ 40 * 104483 * 2
def baseEnd_104483 : Nat := 35766666149213295654665

theorem tailTrace_104483 : CollatzResearch.WordTrace tailWord_104483 prefixEnd_104483 35766666149213295654665 := by
  unfold tailWord_104483
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810808080483410120854103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2540538720322273413902735 3810808080483410120854103)
  ·
    refine ⟨5716212120725115181281155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810808080483410120854103 5716212120725115181281155)
    ·
      refine ⟨8574318181087672771921733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716212120725115181281155 8574318181087672771921733)
      ·
        refine ⟨1607684658953938644735325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8574318181087672771921733 1607684658953938644735325)
        ·
          refine ⟨602881747107726991775747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1607684658953938644735325 602881747107726991775747)
          ·
            refine ⟨904322620661590487663621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602881747107726991775747 904322620661590487663621)
            ·
              refine ⟨169560491374048216436929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 904322620661590487663621 169560491374048216436929)
              ·
                refine ⟨127170368530536162327697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169560491374048216436929 127170368530536162327697)
                ·
                  refine ⟨95377776397902121745773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127170368530536162327697 95377776397902121745773)
                  ·
                    refine ⟨35766666149213295654665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95377776397902121745773 35766666149213295654665)
                    ·
                      rfl

theorem cell22_104483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 3].length) (baseStart_104483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104483 prefixEnd_104483 := by exact prefixLift 104483
  have htrace : WordTrace (prefixWord ++ tailWord_104483) baseStart_104483 baseEnd_104483 := by
    simpa [prefixWord, tailWord_104483, baseEnd_104483] using wordTrace_append hprefix tailTrace_104483
  have hstable : (prefixWord ++ tailWord_104483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104483).length < 2 ^ (prefixWord ++ tailWord_104483).sum := by decide
  have hdescent : baseEnd_104483 < baseStart_104483 := by decide
  rcases family_descends (prefixWord ++ tailWord_104483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104485 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 4]
def baseStart_104485 : Nat := 118140960795 + 104485 * 2 ^ 59
def prefixEnd_104485 : Nat := 4983230072969 + 3 ^ 40 * 104485 * 2
def baseEnd_104485 : Nat := 11922450263361985701553

theorem tailTrace_104485 : CollatzResearch.WordTrace tailWord_104485 prefixEnd_104485 11922450263361985701553 := by
  unfold tailWord_104485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810881026476164462426909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2540587350984109641617939 3810881026476164462426909)
  ·
    refine ⟨1429080384928561673410091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3810881026476164462426909 1429080384928561673410091)
    ·
      refine ⟨2143620577392842510115137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429080384928561673410091 2143620577392842510115137)
      ·
        refine ⟨1607715433044631882586353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2143620577392842510115137 1607715433044631882586353)
        ·
          refine ⟨1205786574783473911939765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607715433044631882586353 1205786574783473911939765)
          ·
            refine ⟨113042491385950679244353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1205786574783473911939765 113042491385950679244353)
            ·
              refine ⟨84781868539463009433265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113042491385950679244353 84781868539463009433265)
              ·
                refine ⟨63586401404597257074949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84781868539463009433265 63586401404597257074949)
                ·
                  refine ⟨11922450263361985701553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63586401404597257074949 11922450263361985701553)
                  ·
                    rfl

theorem cell22_104485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_104485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104485 prefixEnd_104485 := by exact prefixLift 104485
  have htrace : WordTrace (prefixWord ++ tailWord_104485) baseStart_104485 baseEnd_104485 := by
    simpa [prefixWord, tailWord_104485, baseEnd_104485] using wordTrace_append hprefix tailTrace_104485
  have hstable : (prefixWord ++ tailWord_104485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104485).length < 2 ^ (prefixWord ++ tailWord_104485).sum := by decide
  have hdescent : baseEnd_104485 < baseStart_104485 := by decide
  rcases family_descends (prefixWord ++ tailWord_104485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104496 : List Nat := [2, 1, 1, 1, 2, 7, 1, 7]
def baseStart_104496 : Nat := 118140960795 + 104496 * 2 ^ 59
def prefixEnd_104496 : Nat := 4983230072969 + 3 ^ 40 * 104496 * 2
def baseEnd_104496 : Nat := 3974568479431732786625

theorem tailTrace_104496 : CollatzResearch.WordTrace tailWord_104496 prefixEnd_104496 3974568479431732786625 := by
  unfold tailWord_104496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905641114718156670538671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2540854819624208894051561 1905641114718156670538671)
  ·
    refine ⟨2858461672077235005808007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1905641114718156670538671 2858461672077235005808007)
    ·
      refine ⟨4287692508115852508712011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858461672077235005808007 4287692508115852508712011)
      ·
        refine ⟨6431538762173778763068017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287692508115852508712011 6431538762173778763068017)
        ·
          refine ⟨4823654071630334072301013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6431538762173778763068017 4823654071630334072301013)
          ·
            refine ⟨113054392303835954819555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4823654071630334072301013 113054392303835954819555)
            ·
              refine ⟨169581588455753932229333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113054392303835954819555 169581588455753932229333)
              ·
                refine ⟨3974568479431732786625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 169581588455753932229333 3974568479431732786625)
                ·
                  rfl

theorem cell22_104496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_104496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104496 prefixEnd_104496 := by exact prefixLift 104496
  have htrace : WordTrace (prefixWord ++ tailWord_104496) baseStart_104496 baseEnd_104496 := by
    simpa [prefixWord, tailWord_104496, baseEnd_104496] using wordTrace_append hprefix tailTrace_104496
  have hstable : (prefixWord ++ tailWord_104496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104496).length < 2 ^ (prefixWord ++ tailWord_104496).sum := by decide
  have hdescent : baseEnd_104496 < baseStart_104496 := by decide
  rcases family_descends (prefixWord ++ tailWord_104496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104500 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_104500 : Nat := 118140960795 + 104500 * 2 ^ 59
def prefixEnd_104500 : Nat := 4983230072969 + 3 ^ 40 * 104500 * 2
def baseEnd_104500 : Nat := 35772485596630917979613

theorem tailTrace_104500 : CollatzResearch.WordTrace tailWord_104500 prefixEnd_104500 35772485596630917979613 := by
  unfold tailWord_104500
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905714060710911012111477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2540952080947881349481969 1905714060710911012111477)
  ·
    refine ⟨178660693191647907385451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1905714060710911012111477 178660693191647907385451)
    ·
      refine ⟨267991039787471861078177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178660693191647907385451 267991039787471861078177)
      ·
        refine ⟨200993279840603895808633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267991039787471861078177 200993279840603895808633)
        ·
          refine ⟨150744959880452921856475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200993279840603895808633 150744959880452921856475)
          ·
            refine ⟨226117439820679382784713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150744959880452921856475 226117439820679382784713)
            ·
              refine ⟨169588079865509537088535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226117439820679382784713 169588079865509537088535)
              ·
                refine ⟨254382119798264305632803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169588079865509537088535 254382119798264305632803)
                ·
                  refine ⟨381573179697396458449205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254382119798264305632803 381573179697396458449205)
                  ·
                    refine ⟨35772485596630917979613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 381573179697396458449205 35772485596630917979613)
                    ·
                      rfl

theorem cell22_104500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_104500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104500 prefixEnd_104500 := by exact prefixLift 104500
  have htrace : WordTrace (prefixWord ++ tailWord_104500) baseStart_104500 baseEnd_104500 := by
    simpa [prefixWord, tailWord_104500, baseEnd_104500] using wordTrace_append hprefix tailTrace_104500
  have hstable : (prefixWord ++ tailWord_104500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104500).length < 2 ^ (prefixWord ++ tailWord_104500).sum := by decide
  have hdescent : baseEnd_104500 < baseStart_104500 := by decide
  rcases family_descends (prefixWord ++ tailWord_104500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104511 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 5, 3]
def baseStart_104511 : Nat := 118140960795 + 104511 * 2 ^ 59
def prefixEnd_104511 : Nat := 4983230072969 + 3 ^ 40 * 104511 * 2
def baseEnd_104511 : Nat := 35776251121430555954579

theorem tailTrace_104511 : CollatzResearch.WordTrace tailWord_104511 prefixEnd_104511 35776251121430555954579 := by
  unfold tailWord_104511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811829324381970902873387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2541219549587980601915591 3811829324381970902873387)
  ·
    refine ⟨5717743986572956354310081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3811829324381970902873387 5717743986572956354310081)
    ·
      refine ⟨4288307989929717265732561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5717743986572956354310081 4288307989929717265732561)
      ·
        refine ⟨3216230992447287949299421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4288307989929717265732561 3216230992447287949299421)
        ·
          refine ⟨1206086622167732980987283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3216230992447287949299421 1206086622167732980987283)
          ·
            refine ⟨1809129933251599471480925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206086622167732980987283 1809129933251599471480925)
            ·
              refine ⟨678423724969349801805347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1809129933251599471480925 678423724969349801805347)
              ·
                refine ⟨1017635587454024702708021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678423724969349801805347 1017635587454024702708021)
                ·
                  refine ⟨95403336323814815878877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1017635587454024702708021 95403336323814815878877)
                  ·
                    refine ⟨35776251121430555954579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95403336323814815878877 35776251121430555954579)
                    ·
                      rfl

theorem cell22_104511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_104511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104511 prefixEnd_104511 := by exact prefixLift 104511
  have htrace : WordTrace (prefixWord ++ tailWord_104511) baseStart_104511 baseEnd_104511 := by
    simpa [prefixWord, tailWord_104511, baseEnd_104511] using wordTrace_append hprefix tailTrace_104511
  have hstable : (prefixWord ++ tailWord_104511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104511).length < 2 ^ (prefixWord ++ tailWord_104511).sum := by decide
  have hdescent : baseEnd_104511 < baseStart_104511 := by decide
  rcases family_descends (prefixWord ++ tailWord_104511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104513 : List Nat := [1, 2, 5, 1, 2, 2, 3, 6]
def baseStart_104513 : Nat := 118140960795 + 104513 * 2 ^ 59
def prefixEnd_104513 : Nat := 4983230072969 + 3 ^ 40 * 104513 * 2
def baseEnd_104513 : Nat := 3975215084700357489397

theorem tailTrace_104513 : CollatzResearch.WordTrace tailWord_104513 prefixEnd_104513 3975215084700357489397 := by
  unfold tailWord_104513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811902270374725244446193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2541268180249816829630795 3811902270374725244446193)
  ·
    refine ⟨2858926702781043933334645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3811902270374725244446193 2858926702781043933334645)
    ·
      refine ⟨268024378385722868750123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2858926702781043933334645 268024378385722868750123)
      ·
        refine ⟨402036567578584303125185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268024378385722868750123 402036567578584303125185)
        ·
          refine ⟨301527425683938227343889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402036567578584303125185 301527425683938227343889)
          ·
            refine ⟨226145569262953670507917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301527425683938227343889 226145569262953670507917)
            ·
              refine ⟨84804588473607626440469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226145569262953670507917 84804588473607626440469)
              ·
                refine ⟨3975215084700357489397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84804588473607626440469 3975215084700357489397)
                ·
                  rfl

theorem cell22_104513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 6].length) (baseStart_104513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104513 prefixEnd_104513 := by exact prefixLift 104513
  have htrace : WordTrace (prefixWord ++ tailWord_104513) baseStart_104513 baseEnd_104513 := by
    simpa [prefixWord, tailWord_104513, baseEnd_104513] using wordTrace_append hprefix tailTrace_104513
  have hstable : (prefixWord ++ tailWord_104513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104513).length < 2 ^ (prefixWord ++ tailWord_104513).sum := by decide
  have hdescent : baseEnd_104513 < baseStart_104513 := by decide
  rcases family_descends (prefixWord ++ tailWord_104513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104534 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_104534 : Nat := 118140960795 + 104534 * 2 ^ 59
def prefixEnd_104534 : Nat := 4983230072969 + 3 ^ 40 * 104534 * 2
def baseEnd_104534 : Nat := 35784124491466162629509

theorem tailTrace_104534 : CollatzResearch.WordTrace tailWord_104534 prefixEnd_104534 35784124491466162629509 := by
  unfold tailWord_104534
  simp only [CollatzResearch.WordTrace]
  refine ⟨238291762706165364435041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2541778802199097220640437 238291762706165364435041)
  ·
    refine ⟨178718822029624023326281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238291762706165364435041 178718822029624023326281)
    ·
      refine ⟨134039116522218017494711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178718822029624023326281 134039116522218017494711)
      ·
        refine ⟨201058674783327026242067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134039116522218017494711 201058674783327026242067)
        ·
          refine ⟨301588012174990539363101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201058674783327026242067 301588012174990539363101)
          ·
            refine ⟨113095504565621452261163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301588012174990539363101 113095504565621452261163)
            ·
              refine ⟨169643256848432178391745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113095504565621452261163 169643256848432178391745)
              ·
                refine ⟨127232442636324133793809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169643256848432178391745 127232442636324133793809)
                ·
                  refine ⟨95424331977243100345357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127232442636324133793809 95424331977243100345357)
                  ·
                    refine ⟨35784124491466162629509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95424331977243100345357 35784124491466162629509)
                    ·
                      rfl

theorem cell22_104534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_104534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104534 prefixEnd_104534 := by exact prefixLift 104534
  have htrace : WordTrace (prefixWord ++ tailWord_104534) baseStart_104534 baseEnd_104534 := by
    simpa [prefixWord, tailWord_104534, baseEnd_104534] using wordTrace_append hprefix tailTrace_104534
  have hstable : (prefixWord ++ tailWord_104534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104534).length < 2 ^ (prefixWord ++ tailWord_104534).sum := by decide
  have hdescent : baseEnd_104534 < baseStart_104534 := by decide
  rcases family_descends (prefixWord ++ tailWord_104534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104556 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_104556 : Nat := 118140960795 + 104556 * 2 ^ 59
def prefixEnd_104556 : Nat := 4983230072969 + 3 ^ 40 * 104556 * 2
def baseEnd_104556 : Nat := 35791655541065438579441

theorem tailTrace_104556 : CollatzResearch.WordTrace tailWord_104556 prefixEnd_104556 35791655541065438579441 := by
  unfold tailWord_104556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906735304609471794130761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2542313739479295725507681 1906735304609471794130761)
  ·
    refine ⟨1430051478457103845598071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1906735304609471794130761 1430051478457103845598071)
    ·
      refine ⟨2145077217685655768397107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430051478457103845598071 2145077217685655768397107)
      ·
        refine ⟨3217615826528483652595661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145077217685655768397107 3217615826528483652595661)
        ·
          refine ⟨1206605934948181369723373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217615826528483652595661 1206605934948181369723373)
          ·
            refine ⟨452477225605568013646265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1206605934948181369723373 452477225605568013646265)
            ·
              refine ⟨339357919204176010234699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452477225605568013646265 339357919204176010234699)
              ·
                refine ⟨509036878806264015352049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339357919204176010234699 509036878806264015352049)
                ·
                  refine ⟨381777659104698011514037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509036878806264015352049 381777659104698011514037)
                  ·
                    refine ⟨35791655541065438579441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 381777659104698011514037 35791655541065438579441)
                    ·
                      rfl

theorem cell22_104556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_104556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104556 prefixEnd_104556 := by exact prefixLift 104556
  have htrace : WordTrace (prefixWord ++ tailWord_104556) baseStart_104556 baseEnd_104556 := by
    simpa [prefixWord, tailWord_104556, baseEnd_104556] using wordTrace_append hprefix tailTrace_104556
  have hstable : (prefixWord ++ tailWord_104556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104556).length < 2 ^ (prefixWord ++ tailWord_104556).sum := by decide
  have hdescent : baseEnd_104556 < baseStart_104556 := by decide
  rcases family_descends (prefixWord ++ tailWord_104556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104596 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_104596 : Nat := 118140960795 + 104596 * 2 ^ 59
def prefixEnd_104596 : Nat := 4983230072969 + 3 ^ 40 * 104596 * 2
def baseEnd_104596 : Nat := 35805348358518667579319

theorem tailTrace_104596 : CollatzResearch.WordTrace tailWord_104596 prefixEnd_104596 35805348358518667579319 := by
  unfold tailWord_104596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907464764537015209858821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2543286352716020279811761 1907464764537015209858821)
  ·
    refine ⟨357649643350690351848529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1907464764537015209858821 357649643350690351848529)
    ·
      refine ⟨268237232513017763886397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357649643350690351848529 268237232513017763886397)
      ·
        refine ⟨100588962192381661457399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268237232513017763886397 100588962192381661457399)
        ·
          refine ⟨150883443288572492186099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100588962192381661457399 150883443288572492186099)
          ·
            refine ⟨226325164932858738279149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150883443288572492186099 226325164932858738279149)
            ·
              refine ⟨84871936849822026854681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226325164932858738279149 84871936849822026854681)
              ·
                refine ⟨63653952637366520141011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84871936849822026854681 63653952637366520141011)
                ·
                  refine ⟨95480928956049780211517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63653952637366520141011 95480928956049780211517)
                  ·
                    refine ⟨35805348358518667579319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95480928956049780211517 35805348358518667579319)
                    ·
                      rfl

theorem cell22_104596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_104596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104596 prefixEnd_104596 := by exact prefixLift 104596
  have htrace : WordTrace (prefixWord ++ tailWord_104596) baseStart_104596 baseEnd_104596 := by
    simpa [prefixWord, tailWord_104596, baseEnd_104596] using wordTrace_append hprefix tailTrace_104596
  have hstable : (prefixWord ++ tailWord_104596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104596).length < 2 ^ (prefixWord ++ tailWord_104596).sum := by decide
  have hdescent : baseEnd_104596 < baseStart_104596 := by decide
  rcases family_descends (prefixWord ++ tailWord_104596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104622 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_104622 : Nat := 118140960795 + 104622 * 2 ^ 59
def prefixEnd_104622 : Nat := 4983230072969 + 3 ^ 40 * 104622 * 2
def baseEnd_104622 : Nat := 35814248689863266429239

theorem tailTrace_104622 : CollatzResearch.WordTrace tailWord_104622 prefixEnd_104622 35814248689863266429239 := by
  unfold tailWord_104622
  simp only [CollatzResearch.WordTrace]
  refine ⟨476984728372479607520515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2543918551319891240109413 476984728372479607520515)
  ·
    refine ⟨715477092558719411280773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476984728372479607520515 715477092558719411280773)
    ·
      refine ⟨134151954854759889615145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 715477092558719411280773 134151954854759889615145)
      ·
        refine ⟨100613966141069917211359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134151954854759889615145 100613966141069917211359)
        ·
          refine ⟨150920949211604875817039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100613966141069917211359 150920949211604875817039)
          ·
            refine ⟨226381423817407313725559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150920949211604875817039 226381423817407313725559)
            ·
              refine ⟨339572135726110970588339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226381423817407313725559 339572135726110970588339)
              ·
                refine ⟨509358203589166455882509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339572135726110970588339 509358203589166455882509)
                ·
                  refine ⟨191009326345937420955941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509358203589166455882509 191009326345937420955941)
                  ·
                    refine ⟨35814248689863266429239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191009326345937420955941 35814248689863266429239)
                    ·
                      rfl

theorem cell22_104622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_104622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104622 prefixEnd_104622 := by exact prefixLift 104622
  have htrace : WordTrace (prefixWord ++ tailWord_104622) baseStart_104622 baseEnd_104622 := by
    simpa [prefixWord, tailWord_104622, baseEnd_104622] using wordTrace_append hprefix tailTrace_104622
  have hstable : (prefixWord ++ tailWord_104622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104622).length < 2 ^ (prefixWord ++ tailWord_104622).sum := by decide
  have hdescent : baseEnd_104622 < baseStart_104622 := by decide
  rcases family_descends (prefixWord ++ tailWord_104622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104631 : List Nat := [1, 1, 3, 1, 4, 2, 2, 8]
def baseStart_104631 : Nat := 118140960795 + 104631 * 2 ^ 59
def prefixEnd_104631 : Nat := 4983230072969 + 3 ^ 40 * 104631 * 2
def baseEnd_104631 : Nat := 3979703285976693661579

theorem tailTrace_104631 : CollatzResearch.WordTrace tailWord_104631 prefixEnd_104631 3979703285976693661579 := by
  unfold tailWord_104631
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816206083947231397241747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2544137389298154264827831 3816206083947231397241747)
  ·
    refine ⟨5724309125920847095862621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3816206083947231397241747 5724309125920847095862621)
    ·
      refine ⟨2146615922220317660948483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5724309125920847095862621 2146615922220317660948483)
      ·
        refine ⟨3219923883330476491422725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146615922220317660948483 3219923883330476491422725)
        ·
          refine ⟨603735728124464342141761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3219923883330476491422725 603735728124464342141761)
          ·
            refine ⟨452801796093348256606321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603735728124464342141761 452801796093348256606321)
            ·
              refine ⟨339601347070011192454741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452801796093348256606321 339601347070011192454741)
              ·
                refine ⟨3979703285976693661579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 339601347070011192454741 3979703285976693661579)
                ·
                  rfl

theorem cell22_104631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 8].length) (baseStart_104631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104631 prefixEnd_104631 := by exact prefixLift 104631
  have htrace : WordTrace (prefixWord ++ tailWord_104631) baseStart_104631 baseEnd_104631 := by
    simpa [prefixWord, tailWord_104631, baseEnd_104631] using wordTrace_append hprefix tailTrace_104631
  have hstable : (prefixWord ++ tailWord_104631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104631).length < 2 ^ (prefixWord ++ tailWord_104631).sum := by decide
  have hdescent : baseEnd_104631 < baseStart_104631 := by decide
  rcases family_descends (prefixWord ++ tailWord_104631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104633 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_104633 : Nat := 118140960795 + 104633 * 2 ^ 59
def prefixEnd_104633 : Nat := 4983230072969 + 3 ^ 40 * 104633 * 2
def baseEnd_104633 : Nat := 35818014214662904404205

theorem tailTrace_104633 : CollatzResearch.WordTrace tailWord_104633 prefixEnd_104633 35818014214662904404205 := by
  unfold tailWord_104633
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816279029939985738814553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2544186019959990492543035 3816279029939985738814553)
  ·
    refine ⟨2862209272454989304110915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3816279029939985738814553 2862209272454989304110915)
    ·
      refine ⟨4293313908682483956166373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862209272454989304110915 4293313908682483956166373)
      ·
        refine ⟨804996357877965741781195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4293313908682483956166373 804996357877965741781195)
        ·
          refine ⟨1207494536816948612671793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804996357877965741781195 1207494536816948612671793)
          ·
            refine ⟨905620902612711459503845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207494536816948612671793 905620902612711459503845)
            ·
              refine ⟨169803919239883398656971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 905620902612711459503845 169803919239883398656971)
              ·
                refine ⟨254705878859825097985457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169803919239883398656971 254705878859825097985457)
                ·
                  refine ⟨191029409144868823489093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254705878859825097985457 191029409144868823489093)
                  ·
                    refine ⟨35818014214662904404205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191029409144868823489093 35818014214662904404205)
                    ·
                      rfl

theorem cell22_104633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_104633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104633 prefixEnd_104633 := by exact prefixLift 104633
  have htrace : WordTrace (prefixWord ++ tailWord_104633) baseStart_104633 baseEnd_104633 := by
    simpa [prefixWord, tailWord_104633, baseEnd_104633] using wordTrace_append hprefix tailTrace_104633
  have hstable : (prefixWord ++ tailWord_104633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104633).length < 2 ^ (prefixWord ++ tailWord_104633).sum := by decide
  have hdescent : baseEnd_104633 < baseStart_104633 := by decide
  rcases family_descends (prefixWord ++ tailWord_104633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104663 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 3, 3]
def baseStart_104663 : Nat := 118140960795 + 104663 * 2 ^ 59
def prefixEnd_104663 : Nat := 4983230072969 + 3 ^ 40 * 104663 * 2
def baseEnd_104663 : Nat := 35828283827752826154113

theorem tailTrace_104663 : CollatzResearch.WordTrace tailWord_104663 prefixEnd_104663 35828283827752826154113 := by
  unfold tailWord_104663
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817373219831300862406643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2544915479887533908271095 3817373219831300862406643)
  ·
    refine ⟨5726059829746951293609965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817373219831300862406643 5726059829746951293609965)
    ·
      refine ⟨2147272436155106735103737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5726059829746951293609965 2147272436155106735103737)
      ·
        refine ⟨1610454327116330051327803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147272436155106735103737 1610454327116330051327803)
        ·
          refine ⟨2415681490674495076991705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610454327116330051327803 2415681490674495076991705)
          ·
            refine ⟨1811761118005871307743779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415681490674495076991705 1811761118005871307743779)
            ·
              refine ⟨2717641677008806961615669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811761118005871307743779 2717641677008806961615669)
              ·
                refine ⟨254778907219575652651469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2717641677008806961615669 254778907219575652651469)
                ·
                  refine ⟨95542090207340869744301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254778907219575652651469 95542090207340869744301)
                  ·
                    refine ⟨35828283827752826154113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95542090207340869744301 35828283827752826154113)
                    ·
                      rfl

theorem cell22_104663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_104663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104663 prefixEnd_104663 := by exact prefixLift 104663
  have htrace : WordTrace (prefixWord ++ tailWord_104663) baseStart_104663 baseEnd_104663 := by
    simpa [prefixWord, tailWord_104663, baseEnd_104663] using wordTrace_append hprefix tailTrace_104663
  have hstable : (prefixWord ++ tailWord_104663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104663).length < 2 ^ (prefixWord ++ tailWord_104663).sum := by decide
  have hdescent : baseEnd_104663 < baseStart_104663 := by decide
  rcases family_descends (prefixWord ++ tailWord_104663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104676 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_104676 : Nat := 118140960795 + 104676 * 2 ^ 59
def prefixEnd_104676 : Nat := 4983230072969 + 3 ^ 40 * 104676 * 2
def baseEnd_104676 : Nat := 11944244664475041859691

theorem tailTrace_104676 : CollatzResearch.WordTrace tailWord_104676 prefixEnd_104676 11944244664475041859691 := by
  unfold tailWord_104676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908923684392102041314941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2545231579189469388419921 1908923684392102041314941)
  ·
    refine ⟨715846381647038265493103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1908923684392102041314941 715846381647038265493103)
    ·
      refine ⟨1073769572470557398239655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715846381647038265493103 1073769572470557398239655)
      ·
        refine ⟨1610654358705836097359483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073769572470557398239655 1610654358705836097359483)
        ·
          refine ⟨2415981538058754146039225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610654358705836097359483 2415981538058754146039225)
          ·
            refine ⟨1811986153544065609529419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415981538058754146039225 1811986153544065609529419)
            ·
              refine ⟨2717979230316098414294129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811986153544065609529419 2717979230316098414294129)
              ·
                refine ⟨2038484422737073810720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717979230316098414294129 2038484422737073810720597)
                ·
                  refine ⟨11944244664475041859691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2038484422737073810720597 11944244664475041859691)
                  ·
                    rfl

theorem cell22_104676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_104676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104676 prefixEnd_104676 := by exact prefixLift 104676
  have htrace : WordTrace (prefixWord ++ tailWord_104676) baseStart_104676 baseEnd_104676 := by
    simpa [prefixWord, tailWord_104676, baseEnd_104676] using wordTrace_append hprefix tailTrace_104676
  have hstable : (prefixWord ++ tailWord_104676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104676).length < 2 ^ (prefixWord ++ tailWord_104676).sum := by decide
  have hdescent : baseEnd_104676 < baseStart_104676 := by decide
  rcases family_descends (prefixWord ++ tailWord_104676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104680 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_104680 : Nat := 118140960795 + 104680 * 2 ^ 59
def prefixEnd_104680 : Nat := 4983230072969 + 3 ^ 40 * 104680 * 2
def baseEnd_104680 : Nat := 35834103275170448479061

theorem tailTrace_104680 : CollatzResearch.WordTrace tailWord_104680 prefixEnd_104680 35834103275170448479061 := by
  unfold tailWord_104680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908996630384856382887747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2545328840513141843850329 1908996630384856382887747)
  ·
    refine ⟨2863494945577284574331621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908996630384856382887747 2863494945577284574331621)
    ·
      refine ⟨536905302295740857687179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2863494945577284574331621 536905302295740857687179)
      ·
        refine ⟨805357953443611286530769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536905302295740857687179 805357953443611286530769)
        ·
          refine ⟨604018465082708464898077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805357953443611286530769 604018465082708464898077)
          ·
            refine ⟨226506924406015674336779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604018465082708464898077 226506924406015674336779)
            ·
              refine ⟨339760386609023511505169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226506924406015674336779 339760386609023511505169)
              ·
                refine ⟨254820289956767633628877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339760386609023511505169 254820289956767633628877)
                ·
                  refine ⟨95557608733787862610829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254820289956767633628877 95557608733787862610829)
                  ·
                    refine ⟨35834103275170448479061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95557608733787862610829 35834103275170448479061)
                    ·
                      rfl

theorem cell22_104680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_104680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104680 prefixEnd_104680 := by exact prefixLift 104680
  have htrace : WordTrace (prefixWord ++ tailWord_104680) baseStart_104680 baseEnd_104680 := by
    simpa [prefixWord, tailWord_104680, baseEnd_104680] using wordTrace_append hprefix tailTrace_104680
  have hstable : (prefixWord ++ tailWord_104680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104680).length < 2 ^ (prefixWord ++ tailWord_104680).sum := by decide
  have hdescent : baseEnd_104680 < baseStart_104680 := by decide
  rcases family_descends (prefixWord ++ tailWord_104680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104691 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_104691 : Nat := 118140960795 + 104691 * 2 ^ 59
def prefixEnd_104691 : Nat := 4983230072969 + 3 ^ 40 * 104691 * 2
def baseEnd_104691 : Nat := 35837868799970086454027

theorem tailTrace_104691 : CollatzResearch.WordTrace tailWord_104691 prefixEnd_104691 35837868799970086454027 := by
  unfold tailWord_104691
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818394463729861644425927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2545596309153241096283951 3818394463729861644425927)
  ·
    refine ⟨5727591695594792466638891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818394463729861644425927 5727591695594792466638891)
    ·
      refine ⟨8591387543392188699958337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727591695594792466638891 8591387543392188699958337)
      ·
        refine ⟨6443540657544141524968753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8591387543392188699958337 6443540657544141524968753)
        ·
          refine ⟨4832655493158106143726565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6443540657544141524968753 4832655493158106143726565)
          ·
            refine ⟨906122904967144901948731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4832655493158106143726565 906122904967144901948731)
            ·
              refine ⟨1359184357450717352923097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906122904967144901948731 1359184357450717352923097)
              ·
                refine ⟨1019388268088038014692323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359184357450717352923097 1019388268088038014692323)
                ·
                  refine ⟨1529082402132057022038485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019388268088038014692323 1529082402132057022038485)
                  ·
                    refine ⟨35837868799970086454027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1529082402132057022038485 35837868799970086454027)
                    ·
                      rfl

theorem cell22_104691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_104691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104691 prefixEnd_104691 := by exact prefixLift 104691
  have htrace : WordTrace (prefixWord ++ tailWord_104691) baseStart_104691 baseEnd_104691 := by
    simpa [prefixWord, tailWord_104691, baseEnd_104691] using wordTrace_append hprefix tailTrace_104691
  have hstable : (prefixWord ++ tailWord_104691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104691).length < 2 ^ (prefixWord ++ tailWord_104691).sum := by decide
  have hdescent : baseEnd_104691 < baseStart_104691 := by decide
  rcases family_descends (prefixWord ++ tailWord_104691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104740 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_104740 : Nat := 118140960795 + 104740 * 2 ^ 59
def prefixEnd_104740 : Nat := 4983230072969 + 3 ^ 40 * 104740 * 2
def baseEnd_104740 : Nat := 35854642501350291978877

theorem tailTrace_104740 : CollatzResearch.WordTrace tailWord_104740 prefixEnd_104740 35854642501350291978877 := by
  unfold tailWord_104740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910090820276171506479837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2546787760368228675306449 1910090820276171506479837)
  ·
    refine ⟨716284057603564314929939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1910090820276171506479837 716284057603564314929939)
    ·
      refine ⟨1074426086405346472394909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716284057603564314929939 1074426086405346472394909)
      ·
        refine ⟨402909782402004927148091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1074426086405346472394909 402909782402004927148091)
        ·
          refine ⟨604364673603007390722137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402909782402004927148091 604364673603007390722137)
          ·
            refine ⟨453273505202255543041603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604364673603007390722137 453273505202255543041603)
            ·
              refine ⟨679910257803383314562405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453273505202255543041603 679910257803383314562405)
              ·
                refine ⟨127483173338134371480451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679910257803383314562405 127483173338134371480451)
                ·
                  refine ⟨191224760007201557220677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127483173338134371480451 191224760007201557220677)
                  ·
                    refine ⟨35854642501350291978877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191224760007201557220677 35854642501350291978877)
                    ·
                      rfl

theorem cell22_104740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_104740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104740 prefixEnd_104740 := by exact prefixLift 104740
  have htrace : WordTrace (prefixWord ++ tailWord_104740) baseStart_104740 baseEnd_104740 := by
    simpa [prefixWord, tailWord_104740, baseEnd_104740] using wordTrace_append hprefix tailTrace_104740
  have hstable : (prefixWord ++ tailWord_104740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104740).length < 2 ^ (prefixWord ++ tailWord_104740).sum := by decide
  have hdescent : baseEnd_104740 < baseStart_104740 := by decide
  rcases family_descends (prefixWord ++ tailWord_104740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104802 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_104802 : Nat := 118140960795 + 104802 * 2 ^ 59
def prefixEnd_104802 : Nat := 4983230072969 + 3 ^ 40 * 104802 * 2
def baseEnd_104802 : Nat := 35875866368402796928687

theorem tailTrace_104802 : CollatzResearch.WordTrace tailWord_104802 prefixEnd_104802 35875866368402796928687 := by
  unfold tailWord_104802
  simp only [CollatzResearch.WordTrace]
  refine ⟨955610741581931900429165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2548295310885151734477773 955610741581931900429165)
  ·
    refine ⟨358354028093224462660937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 955610741581931900429165 358354028093224462660937)
    ·
      refine ⟨268765521069918346995703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358354028093224462660937 268765521069918346995703)
      ·
        refine ⟨403148281604877520493555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268765521069918346995703 403148281604877520493555)
        ·
          refine ⟨604722422407316280740333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403148281604877520493555 604722422407316280740333)
          ·
            refine ⟨226770908402743605277625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604722422407316280740333 226770908402743605277625)
            ·
              refine ⟨170078181302057703958219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226770908402743605277625 170078181302057703958219)
              ·
                refine ⟨255117271953086555937329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170078181302057703958219 255117271953086555937329)
                ·
                  refine ⟨191337953964814916952997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255117271953086555937329 191337953964814916952997)
                  ·
                    refine ⟨35875866368402796928687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191337953964814916952997 35875866368402796928687)
                    ·
                      rfl

theorem cell22_104802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_104802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104802 prefixEnd_104802 := by exact prefixLift 104802
  have htrace : WordTrace (prefixWord ++ tailWord_104802) baseStart_104802 baseEnd_104802 := by
    simpa [prefixWord, tailWord_104802, baseEnd_104802] using wordTrace_append hprefix tailTrace_104802
  have hstable : (prefixWord ++ tailWord_104802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104802).length < 2 ^ (prefixWord ++ tailWord_104802).sum := by decide
  have hdescent : baseEnd_104802 < baseStart_104802 := by decide
  rcases family_descends (prefixWord ++ tailWord_104802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104834 : List Nat := [3, 4, 2, 1, 2, 2, 1, 7]
def baseStart_104834 : Nat := 118140960795 + 104834 * 2 ^ 59
def prefixEnd_104834 : Nat := 4983230072969 + 3 ^ 40 * 104834 * 2
def baseEnd_104834 : Nat := 3987424513596153347621

theorem tailTrace_104834 : CollatzResearch.WordTrace tailWord_104834 prefixEnd_104834 3987424513596153347621 := by
  unfold tailWord_104834
  simp only [CollatzResearch.WordTrace]
  refine ⟨955902525552949266720389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2549073401474531377921037 955902525552949266720389)
  ·
    refine ⟨179231723541177987510073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 955902525552949266720389 179231723541177987510073)
    ·
      refine ⟨134423792655883490632555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179231723541177987510073 134423792655883490632555)
      ·
        refine ⟨201635688983825235948833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134423792655883490632555 201635688983825235948833)
        ·
          refine ⟨151226766737868926961625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201635688983825235948833 151226766737868926961625)
          ·
            refine ⟨113420075053401695221219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151226766737868926961625 113420075053401695221219)
            ·
              refine ⟨170130112580102542831829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113420075053401695221219 170130112580102542831829)
              ·
                refine ⟨3987424513596153347621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170130112580102542831829 3987424513596153347621)
                ·
                  rfl

theorem cell22_104834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_104834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104834 prefixEnd_104834 := by exact prefixLift 104834
  have htrace : WordTrace (prefixWord ++ tailWord_104834) baseStart_104834 baseEnd_104834 := by
    simpa [prefixWord, tailWord_104834, baseEnd_104834] using wordTrace_append hprefix tailTrace_104834
  have hstable : (prefixWord ++ tailWord_104834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104834).length < 2 ^ (prefixWord ++ tailWord_104834).sum := by decide
  have hdescent : baseEnd_104834 < baseStart_104834 := by decide
  rcases family_descends (prefixWord ++ tailWord_104834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104843 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_104843 : Nat := 118140960795 + 104843 * 2 ^ 59
def prefixEnd_104843 : Nat := 4983230072969 + 3 ^ 40 * 104843 * 2
def baseEnd_104843 : Nat := 35889901506292356653561

theorem tailTrace_104843 : CollatzResearch.WordTrace tailWord_104843 prefixEnd_104843 35889901506292356653561 := by
  unfold tailWord_104843
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823938359179191603959183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2549292239452794402639455 3823938359179191603959183)
  ·
    refine ⟨5735907538768787405938775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3823938359179191603959183 5735907538768787405938775)
    ·
      refine ⟨8603861308153181108908163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5735907538768787405938775 8603861308153181108908163)
      ·
        refine ⟨12905791962229771663362245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8603861308153181108908163 12905791962229771663362245)
        ·
          refine ⟨2419835992918082186880421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12905791962229771663362245 2419835992918082186880421)
          ·
            refine ⟨453719248672140410040079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2419835992918082186880421 453719248672140410040079)
            ·
              refine ⟨680578873008210615060119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453719248672140410040079 680578873008210615060119)
              ·
                refine ⟨1020868309512315922590179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680578873008210615060119 1020868309512315922590179)
                ·
                  refine ⟨1531302464268473883885269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020868309512315922590179 1531302464268473883885269)
                  ·
                    refine ⟨35889901506292356653561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1531302464268473883885269 35889901506292356653561)
                    ·
                      rfl

theorem cell22_104843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_104843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104843 prefixEnd_104843 := by exact prefixLift 104843
  have htrace : WordTrace (prefixWord ++ tailWord_104843) baseStart_104843 baseEnd_104843 := by
    simpa [prefixWord, tailWord_104843, baseEnd_104843] using wordTrace_append hprefix tailTrace_104843
  have hstable : (prefixWord ++ tailWord_104843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104843).length < 2 ^ (prefixWord ++ tailWord_104843).sum := by decide
  have hdescent : baseEnd_104843 < baseStart_104843 := by decide
  rcases family_descends (prefixWord ++ tailWord_104843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104905 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_104905 : Nat := 118140960795 + 104905 * 2 ^ 59
def prefixEnd_104905 : Nat := 4983230072969 + 3 ^ 40 * 104905 * 2
def baseEnd_104905 : Nat := 35911125373344861603371

theorem tailTrace_104905 : CollatzResearch.WordTrace tailWord_104905 prefixEnd_104905 35911125373344861603371 := by
  unfold tailWord_104905
  simp only [CollatzResearch.WordTrace]
  refine ⟨3826199684954576192716169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2550799789969717461810779 3826199684954576192716169)
  ·
    refine ⟨2869649763715932144537127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3826199684954576192716169 2869649763715932144537127)
    ·
      refine ⟨4304474645573898216805691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2869649763715932144537127 4304474645573898216805691)
      ·
        refine ⟨6456711968360847325208537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304474645573898216805691 6456711968360847325208537)
        ·
          refine ⟨4842533976270635493906403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456711968360847325208537 4842533976270635493906403)
          ·
            refine ⟨7263800964405953240859605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842533976270635493906403 7263800964405953240859605)
            ·
              refine ⟨170245335103264529082647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7263800964405953240859605 170245335103264529082647)
              ·
                refine ⟨255368002654896793623971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170245335103264529082647 255368002654896793623971)
                ·
                  refine ⟨383052003982345190435957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255368002654896793623971 383052003982345190435957)
                  ·
                    refine ⟨35911125373344861603371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 383052003982345190435957 35911125373344861603371)
                    ·
                      rfl

theorem cell22_104905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_104905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104905 prefixEnd_104905 := by exact prefixLift 104905
  have htrace : WordTrace (prefixWord ++ tailWord_104905) baseStart_104905 baseEnd_104905 := by
    simpa [prefixWord, tailWord_104905, baseEnd_104905] using wordTrace_append hprefix tailTrace_104905
  have hstable : (prefixWord ++ tailWord_104905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104905).length < 2 ^ (prefixWord ++ tailWord_104905).sum := by decide
  have hdescent : baseEnd_104905 < baseStart_104905 := by decide
  rcases family_descends (prefixWord ++ tailWord_104905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104920 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_104920 : Nat := 118140960795 + 104920 * 2 ^ 59
def prefixEnd_104920 : Nat := 4983230072969 + 3 ^ 40 * 104920 * 2
def baseEnd_104920 : Nat := 35916260179889822478325

theorem tailTrace_104920 : CollatzResearch.WordTrace tailWord_104920 prefixEnd_104920 35916260179889822478325 := by
  unfold tailWord_104920
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913373389950116877256107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2551164519933489169674809 1913373389950116877256107)
  ·
    refine ⟨2870060084925175315884161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1913373389950116877256107 2870060084925175315884161)
    ·
      refine ⟨2152545063693881486913121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2870060084925175315884161 2152545063693881486913121)
      ·
        refine ⟨1614408797770411115184841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2152545063693881486913121 1614408797770411115184841)
        ·
          refine ⟨1210806598327808336388631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614408797770411115184841 1210806598327808336388631)
          ·
            refine ⟨1816209897491712504582947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210806598327808336388631 1816209897491712504582947)
            ·
              refine ⟨2724314846237568756874421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816209897491712504582947 2724314846237568756874421)
              ·
                refine ⟨255404516834772070956977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2724314846237568756874421 255404516834772070956977)
                ·
                  refine ⟨191553387626079053217733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255404516834772070956977 191553387626079053217733)
                  ·
                    refine ⟨35916260179889822478325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191553387626079053217733 35916260179889822478325)
                    ·
                      rfl

theorem cell22_104920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_104920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104920 prefixEnd_104920 := by exact prefixLift 104920
  have htrace : WordTrace (prefixWord ++ tailWord_104920) baseStart_104920 baseEnd_104920 := by
    simpa [prefixWord, tailWord_104920, baseEnd_104920] using wordTrace_append hprefix tailTrace_104920
  have hstable : (prefixWord ++ tailWord_104920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104920).length < 2 ^ (prefixWord ++ tailWord_104920).sum := by decide
  have hdescent : baseEnd_104920 < baseStart_104920 := by decide
  rcases family_descends (prefixWord ++ tailWord_104920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104941 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 4]
def baseStart_104941 : Nat := 118140960795 + 104941 * 2 ^ 59
def prefixEnd_104941 : Nat := 4983230072969 + 3 ^ 40 * 104941 * 2
def baseEnd_104941 : Nat := 11974482969684255901087

theorem tailTrace_104941 : CollatzResearch.WordTrace tailWord_104941 prefixEnd_104941 11974482969684255901087 := by
  unfold tailWord_104941
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827512712824154341026677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2551675141882769560684451 3827512712824154341026677)
  ·
    refine ⟨358829316827264469471251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3827512712824154341026677 358829316827264469471251)
    ·
      refine ⟨538243975240896704206877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358829316827264469471251 538243975240896704206877)
      ·
        refine ⟨201841490715336264077579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538243975240896704206877 201841490715336264077579)
        ·
          refine ⟨302762236073004396116369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201841490715336264077579 302762236073004396116369)
          ·
            refine ⟨227071677054753297087277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302762236073004396116369 227071677054753297087277)
            ·
              refine ⟨85151878895532486407729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227071677054753297087277 85151878895532486407729)
              ·
                refine ⟨63863909171649364805797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85151878895532486407729 63863909171649364805797)
                ·
                  refine ⟨11974482969684255901087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63863909171649364805797 11974482969684255901087)
                  ·
                    rfl

theorem cell22_104941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_104941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_104941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_104941 prefixEnd_104941 := by exact prefixLift 104941
  have htrace : WordTrace (prefixWord ++ tailWord_104941) baseStart_104941 baseEnd_104941 := by
    simpa [prefixWord, tailWord_104941, baseEnd_104941] using wordTrace_append hprefix tailTrace_104941
  have hstable : (prefixWord ++ tailWord_104941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104941).length < 2 ^ (prefixWord ++ tailWord_104941).sum := by decide
  have hdescent : baseEnd_104941 < baseStart_104941 := by decide
  rcases family_descends (prefixWord ++ tailWord_104941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105014 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_105014 : Nat := 118140960795 + 105014 * 2 ^ 59
def prefixEnd_105014 : Nat := 4983230072969 + 3 ^ 40 * 105014 * 2
def baseEnd_105014 : Nat := 11982812766968303542679

theorem tailTrace_105014 : CollatzResearch.WordTrace tailWord_105014 prefixEnd_105014 11982812766968303542679 := by
  unfold tailWord_105014
  simp only [CollatzResearch.WordTrace]
  refine ⟨239385952597480488027131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2553450161039791872289397 239385952597480488027131)
  ·
    refine ⟨359078928896220732040697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239385952597480488027131 359078928896220732040697)
    ·
      refine ⟨269309196672165549030523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359078928896220732040697 269309196672165549030523)
      ·
        refine ⟨403963795008248323545785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269309196672165549030523 403963795008248323545785)
        ·
          refine ⟨302972846256186242659339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403963795008248323545785 302972846256186242659339)
          ·
            refine ⟨454459269384279363989009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302972846256186242659339 454459269384279363989009)
            ·
              refine ⟨340844452038209522991757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454459269384279363989009 340844452038209522991757)
              ·
                refine ⟨127816669514328571121909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340844452038209522991757 127816669514328571121909)
                ·
                  refine ⟨11982812766968303542679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127816669514328571121909 11982812766968303542679)
                  ·
                    rfl

theorem cell22_105014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_105014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105014 prefixEnd_105014 := by exact prefixLift 105014
  have htrace : WordTrace (prefixWord ++ tailWord_105014) baseStart_105014 baseEnd_105014 := by
    simpa [prefixWord, tailWord_105014, baseEnd_105014] using wordTrace_append hprefix tailTrace_105014
  have hstable : (prefixWord ++ tailWord_105014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105014).length < 2 ^ (prefixWord ++ tailWord_105014).sum := by decide
  have hdescent : baseEnd_105014 < baseStart_105014 := by decide
  rcases family_descends (prefixWord ++ tailWord_105014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105040 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_105040 : Nat := 118140960795 + 105040 * 2 ^ 59
def prefixEnd_105040 : Nat := 4983230072969 + 3 ^ 40 * 105040 * 2
def baseEnd_105040 : Nat := 35957338632249509477957

theorem tailTrace_105040 : CollatzResearch.WordTrace tailWord_105040 prefixEnd_105040 35957338632249509477957 := by
  unfold tailWord_105040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915561769732747124440287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2554082359643662832587049 1915561769732747124440287)
  ·
    refine ⟨2873342654599120686660431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1915561769732747124440287 2873342654599120686660431)
    ·
      refine ⟨4310013981898681029990647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2873342654599120686660431 4310013981898681029990647)
      ·
        refine ⟨6465020972848021544985971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310013981898681029990647 6465020972848021544985971)
        ·
          refine ⟨9697531459272032317478957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465020972848021544985971 9697531459272032317478957)
          ·
            refine ⟨3636574297227012119054609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9697531459272032317478957 3636574297227012119054609)
            ·
              refine ⟨2727430722920259089290957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3636574297227012119054609 2727430722920259089290957)
              ·
                refine ⟨1022786521095097158484109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2727430722920259089290957 1022786521095097158484109)
                ·
                  refine ⟨383544945410661434431541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022786521095097158484109 383544945410661434431541)
                  ·
                    refine ⟨35957338632249509477957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 383544945410661434431541 35957338632249509477957)
                    ·
                      rfl

theorem cell22_105040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_105040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105040 prefixEnd_105040 := by exact prefixLift 105040
  have htrace : WordTrace (prefixWord ++ tailWord_105040) baseStart_105040 baseEnd_105040 := by
    simpa [prefixWord, tailWord_105040, baseEnd_105040] using wordTrace_append hprefix tailTrace_105040
  have hstable : (prefixWord ++ tailWord_105040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105040).length < 2 ^ (prefixWord ++ tailWord_105040).sum := by decide
  have hdescent : baseEnd_105040 < baseStart_105040 := by decide
  rcases family_descends (prefixWord ++ tailWord_105040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105044 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_105044 : Nat := 118140960795 + 105044 * 2 ^ 59
def prefixEnd_105044 : Nat := 4983230072969 + 3 ^ 40 * 105044 * 2
def baseEnd_105044 : Nat := 35958707913994832377945

theorem tailTrace_105044 : CollatzResearch.WordTrace tailWord_105044 prefixEnd_105044 35958707913994832377945 := by
  unfold tailWord_105044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915634715725501466013093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2554179620967335288017457 1915634715725501466013093)
  ·
    refine ⟨359181509198531524877455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1915634715725501466013093 359181509198531524877455)
    ·
      refine ⟨538772263797797287316183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359181509198531524877455 538772263797797287316183)
      ·
        refine ⟨808158395696695930974275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538772263797797287316183 808158395696695930974275)
        ·
          refine ⟨1212237593545043896461413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808158395696695930974275 1212237593545043896461413)
          ·
            refine ⟨227294548789695730586515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1212237593545043896461413 227294548789695730586515)
            ·
              refine ⟨340941823184543595879773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227294548789695730586515 340941823184543595879773)
              ·
                refine ⟨127853183694203848454915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340941823184543595879773 127853183694203848454915)
                ·
                  refine ⟨191779775541305772682373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127853183694203848454915 191779775541305772682373)
                  ·
                    refine ⟨35958707913994832377945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191779775541305772682373 35958707913994832377945)
                    ·
                      rfl

theorem cell22_105044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_105044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105044 prefixEnd_105044 := by exact prefixLift 105044
  have htrace : WordTrace (prefixWord ++ tailWord_105044) baseStart_105044 baseEnd_105044 := by
    simpa [prefixWord, tailWord_105044, baseEnd_105044] using wordTrace_append hprefix tailTrace_105044
  have hstable : (prefixWord ++ tailWord_105044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105044).length < 2 ^ (prefixWord ++ tailWord_105044).sum := by decide
  have hdescent : baseEnd_105044 < baseStart_105044 := by decide
  rcases family_descends (prefixWord ++ tailWord_105044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105177 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 6]
def baseStart_105177 : Nat := 118140960795 + 105177 * 2 ^ 59
def prefixEnd_105177 : Nat := 4983230072969 + 3 ^ 40 * 105177 * 2
def baseEnd_105177 : Nat := 12001412177342272934179

theorem tailTrace_105177 : CollatzResearch.WordTrace tailWord_105177 prefixEnd_105177 12001412177342272934179 := by
  unfold tailWord_105177
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836120339969166646617785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2557413559979444431078523 3836120339969166646617785)
  ·
    refine ⟨2877090254976874984963339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3836120339969166646617785 2877090254976874984963339)
    ·
      refine ⟨4315635382465312477445009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877090254976874984963339 4315635382465312477445009)
      ·
        refine ⟨3236726536848984358083757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4315635382465312477445009 3236726536848984358083757)
        ·
          refine ⟨1213772451318369134281409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3236726536848984358083757 1213772451318369134281409)
          ·
            refine ⟨910329338488776850711057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213772451318369134281409 910329338488776850711057)
            ·
              refine ⟨682747003866582638033293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910329338488776850711057 682747003866582638033293)
              ·
                refine ⟨256030126449968489262485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 682747003866582638033293 256030126449968489262485)
                ·
                  refine ⟨12001412177342272934179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256030126449968489262485 12001412177342272934179)
                  ·
                    rfl

theorem cell22_105177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_105177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105177 prefixEnd_105177 := by exact prefixLift 105177
  have htrace : WordTrace (prefixWord ++ tailWord_105177) baseStart_105177 baseEnd_105177 := by
    simpa [prefixWord, tailWord_105177, baseEnd_105177] using wordTrace_append hprefix tailTrace_105177
  have hstable : (prefixWord ++ tailWord_105177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105177).length < 2 ^ (prefixWord ++ tailWord_105177).sum := by decide
  have hdescent : baseEnd_105177 < baseStart_105177 := by decide
  rcases family_descends (prefixWord ++ tailWord_105177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105376 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_105376 : Nat := 118140960795 + 105376 * 2 ^ 59
def prefixEnd_105376 : Nat := 4983230072969 + 3 ^ 40 * 105376 * 2
def baseEnd_105376 : Nat := 36072358298856633076927

theorem tailTrace_105376 : CollatzResearch.WordTrace tailWord_105376 prefixEnd_105376 36072358298856633076927 := by
  unfold tailWord_105376
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921689233124111816555991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2562252310832149088741321 1921689233124111816555991)
  ·
    refine ⟨2882533849686167724833987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921689233124111816555991 2882533849686167724833987)
    ·
      refine ⟨4323800774529251587250981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882533849686167724833987 4323800774529251587250981)
      ·
        refine ⟨810712645224234672609559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4323800774529251587250981 810712645224234672609559)
        ·
          refine ⟨1216068967836352008914339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810712645224234672609559 1216068967836352008914339)
          ·
            refine ⟨1824103451754528013371509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216068967836352008914339 1824103451754528013371509)
            ·
              refine ⟨171009698601987001253579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1824103451754528013371509 171009698601987001253579)
              ·
                refine ⟨256514547902980501880369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171009698601987001253579 256514547902980501880369)
                ·
                  refine ⟨192385910927235376410277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256514547902980501880369 192385910927235376410277)
                  ·
                    refine ⟨36072358298856633076927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192385910927235376410277 36072358298856633076927)
                    ·
                      rfl

theorem cell22_105376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_105376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105376 prefixEnd_105376 := by exact prefixLift 105376
  have htrace : WordTrace (prefixWord ++ tailWord_105376) baseStart_105376 baseEnd_105376 := by
    simpa [prefixWord, tailWord_105376, baseEnd_105376] using wordTrace_append hprefix tailTrace_105376
  have hstable : (prefixWord ++ tailWord_105376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105376).length < 2 ^ (prefixWord ++ tailWord_105376).sum := by decide
  have hdescent : baseEnd_105376 < baseStart_105376 := by decide
  rcases family_descends (prefixWord ++ tailWord_105376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105412 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_105412 : Nat := 118140960795 + 105412 * 2 ^ 59
def prefixEnd_105412 : Nat := 4983230072969 + 3 ^ 40 * 105412 * 2
def baseEnd_105412 : Nat := 36084681834564539176817

theorem tailTrace_105412 : CollatzResearch.WordTrace tailWord_105412 prefixEnd_105412 36084681834564539176817 := by
  unfold tailWord_105412
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922345747058900890711245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2563127662745201187614993 1922345747058900890711245)
  ·
    refine ⟨720879655147087834016717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1922345747058900890711245 720879655147087834016717)
    ·
      refine ⟨270329870680157937756269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 720879655147087834016717 270329870680157937756269)
      ·
        refine ⟨101373701505059226658601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270329870680157937756269 101373701505059226658601)
        ·
          refine ⟨76030276128794419993951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101373701505059226658601 76030276128794419993951)
          ·
            refine ⟨114045414193191629990927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76030276128794419993951 114045414193191629990927)
            ·
              refine ⟨171068121289787444986391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114045414193191629990927 171068121289787444986391)
              ·
                refine ⟨256602181934681167479587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171068121289787444986391 256602181934681167479587)
                ·
                  refine ⟨384903272902021751219381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256602181934681167479587 384903272902021751219381)
                  ·
                    refine ⟨36084681834564539176817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 384903272902021751219381 36084681834564539176817)
                    ·
                      rfl

theorem cell22_105412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_105412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105412 prefixEnd_105412 := by exact prefixLift 105412
  have htrace : WordTrace (prefixWord ++ tailWord_105412) baseStart_105412 baseEnd_105412 := by
    simpa [prefixWord, tailWord_105412, baseEnd_105412] using wordTrace_append hprefix tailTrace_105412
  have hstable : (prefixWord ++ tailWord_105412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105412).length < 2 ^ (prefixWord ++ tailWord_105412).sum := by decide
  have hdescent : baseEnd_105412 < baseStart_105412 := by decide
  rcases family_descends (prefixWord ++ tailWord_105412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105457 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 1, 3]
def baseStart_105457 : Nat := 118140960795 + 105457 * 2 ^ 59
def prefixEnd_105457 : Nat := 4983230072969 + 3 ^ 40 * 105457 * 2
def baseEnd_105457 : Nat := 36100086254199421801679

theorem tailTrace_105457 : CollatzResearch.WordTrace tailWord_105457 prefixEnd_105457 36100086254199421801679 := by
  unfold tailWord_105457
  simp only [CollatzResearch.WordTrace]
  refine ⟨3846332778954774466810625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2564221852636516311207083 3846332778954774466810625)
  ·
    refine ⟨2884749584216080850107969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3846332778954774466810625 2884749584216080850107969)
    ·
      refine ⟨2163562188162060637580977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2884749584216080850107969 2163562188162060637580977)
      ·
        refine ⟨1622671641121545478185733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2163562188162060637580977 1622671641121545478185733)
        ·
          refine ⟨304250932710289777159825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1622671641121545478185733 304250932710289777159825)
          ·
            refine ⟨228188199532717332869869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304250932710289777159825 228188199532717332869869)
            ·
              refine ⟨85570574824768999826201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228188199532717332869869 85570574824768999826201)
              ·
                refine ⟨64177931118576749869651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85570574824768999826201 64177931118576749869651)
                ·
                  refine ⟨96266896677865124804477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64177931118576749869651 96266896677865124804477)
                  ·
                    refine ⟨36100086254199421801679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96266896677865124804477 36100086254199421801679)
                    ·
                      rfl

theorem cell22_105457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_105457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105457 prefixEnd_105457 := by exact prefixLift 105457
  have htrace : WordTrace (prefixWord ++ tailWord_105457) baseStart_105457 baseEnd_105457 := by
    simpa [prefixWord, tailWord_105457, baseEnd_105457] using wordTrace_append hprefix tailTrace_105457
  have hstable : (prefixWord ++ tailWord_105457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105457).length < 2 ^ (prefixWord ++ tailWord_105457).sum := by decide
  have hdescent : baseEnd_105457 < baseStart_105457 := by decide
  rcases family_descends (prefixWord ++ tailWord_105457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105470 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_105470 : Nat := 118140960795 + 105470 * 2 ^ 59
def prefixEnd_105470 : Nat := 4983230072969 + 3 ^ 40 * 105470 * 2
def baseEnd_105470 : Nat := 12034845473290573742213

theorem tailTrace_105470 : CollatzResearch.WordTrace tailWord_105470 prefixEnd_105470 12034845473290573742213 := by
  unfold tailWord_105470
  simp only [CollatzResearch.WordTrace]
  refine ⟨480850865988459710879233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2564537951938451791355909 480850865988459710879233)
  ·
    refine ⟨360638149491344783159425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 480850865988459710879233 360638149491344783159425)
    ·
      refine ⟨270478612118508587369569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360638149491344783159425 270478612118508587369569)
      ·
        refine ⟨202858959088881440527177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270478612118508587369569 202858959088881440527177)
        ·
          refine ⟨152144219316661080395383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202858959088881440527177 152144219316661080395383)
          ·
            refine ⟨228216328974991620593075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152144219316661080395383 228216328974991620593075)
            ·
              refine ⟨342324493462487430889613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228216328974991620593075 342324493462487430889613)
              ·
                refine ⟨128371685048432786583605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342324493462487430889613 128371685048432786583605)
                ·
                  refine ⟨12034845473290573742213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128371685048432786583605 12034845473290573742213)
                  ·
                    rfl

theorem cell22_105470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_105470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105470 prefixEnd_105470 := by exact prefixLift 105470
  have htrace : WordTrace (prefixWord ++ tailWord_105470) baseStart_105470 baseEnd_105470 := by
    simpa [prefixWord, tailWord_105470, baseEnd_105470] using wordTrace_append hprefix tailTrace_105470
  have hstable : (prefixWord ++ tailWord_105470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105470).length < 2 ^ (prefixWord ++ tailWord_105470).sum := by decide
  have hdescent : baseEnd_105470 < baseStart_105470 := by decide
  rcases family_descends (prefixWord ++ tailWord_105470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105483 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 1, 4]
def baseStart_105483 : Nat := 118140960795 + 105483 * 2 ^ 59
def prefixEnd_105483 : Nat := 4983230072969 + 3 ^ 40 * 105483 * 2
def baseEnd_105483 : Nat := 36108986585544020651599

theorem tailTrace_105483 : CollatzResearch.WordTrace tailWord_105483 prefixEnd_105483 36108986585544020651599 := by
  unfold tailWord_105483
  simp only [CollatzResearch.WordTrace]
  refine ⟨3847281076860580907257103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2564854051240387271504735 3847281076860580907257103)
  ·
    refine ⟨5770921615290871360885655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3847281076860580907257103 5770921615290871360885655)
    ·
      refine ⟨8656382422936307041328483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5770921615290871360885655 8656382422936307041328483)
      ·
        refine ⟨12984573634404460561992725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8656382422936307041328483 12984573634404460561992725)
        ·
          refine ⟨608651889112709088843409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12984573634404460561992725 608651889112709088843409)
          ·
            refine ⟨456488916834531816632557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608651889112709088843409 456488916834531816632557)
            ·
              refine ⟨171183343812949431237209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456488916834531816632557 171183343812949431237209)
              ·
                refine ⟨128387507859712073427907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171183343812949431237209 128387507859712073427907)
                ·
                  refine ⟨192581261789568110141861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128387507859712073427907 192581261789568110141861)
                  ·
                    refine ⟨36108986585544020651599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192581261789568110141861 36108986585544020651599)
                    ·
                      rfl

theorem cell22_105483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 4].length) (baseStart_105483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105483 prefixEnd_105483 := by exact prefixLift 105483
  have htrace : WordTrace (prefixWord ++ tailWord_105483) baseStart_105483 baseEnd_105483 := by
    simpa [prefixWord, tailWord_105483, baseEnd_105483] using wordTrace_append hprefix tailTrace_105483
  have hstable : (prefixWord ++ tailWord_105483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105483).length < 2 ^ (prefixWord ++ tailWord_105483).sum := by decide
  have hdescent : baseEnd_105483 < baseStart_105483 := by decide
  rcases family_descends (prefixWord ++ tailWord_105483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105496 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_105496 : Nat := 118140960795 + 105496 * 2 ^ 59
def prefixEnd_105496 : Nat := 4983230072969 + 3 ^ 40 * 105496 * 2
def baseEnd_105496 : Nat := 36113436751216320076559

theorem tailTrace_105496 : CollatzResearch.WordTrace tailWord_105496 prefixEnd_105496 36113436751216320076559 := by
  unfold tailWord_105496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923877612906742063740171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2565170150542322751653561 1923877612906742063740171)
  ·
    refine ⟨2885816419360113095610257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1923877612906742063740171 2885816419360113095610257)
    ·
      refine ⟨2164362314520084821707693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2885816419360113095610257 2164362314520084821707693)
      ·
        refine ⟨811635867945031808140385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2164362314520084821707693 811635867945031808140385)
        ·
          refine ⟨608726900958773856105289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811635867945031808140385 608726900958773856105289)
          ·
            refine ⟨456545175719080392078967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608726900958773856105289 456545175719080392078967)
            ·
              refine ⟨684817763578620588118451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456545175719080392078967 684817763578620588118451)
              ·
                refine ⟨1027226645367930882177677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684817763578620588118451 1027226645367930882177677)
                ·
                  refine ⟨385209992012974080816629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027226645367930882177677 385209992012974080816629)
                  ·
                    refine ⟨36113436751216320076559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 385209992012974080816629 36113436751216320076559)
                    ·
                      rfl

theorem cell22_105496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_105496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105496 prefixEnd_105496 := by exact prefixLift 105496
  have htrace : WordTrace (prefixWord ++ tailWord_105496) baseStart_105496 baseEnd_105496 := by
    simpa [prefixWord, tailWord_105496, baseEnd_105496] using wordTrace_append hprefix tailTrace_105496
  have hstable : (prefixWord ++ tailWord_105496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105496).length < 2 ^ (prefixWord ++ tailWord_105496).sum := by decide
  have hdescent : baseEnd_105496 < baseStart_105496 := by decide
  rcases family_descends (prefixWord ++ tailWord_105496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105498 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_105498 : Nat := 118140960795 + 105498 * 2 ^ 59
def prefixEnd_105498 : Nat := 4983230072969 + 3 ^ 40 * 105498 * 2
def baseEnd_105498 : Nat := 12038040464029660508851

theorem tailTrace_105498 : CollatzResearch.WordTrace tailWord_105498 prefixEnd_105498 12038040464029660508851 := by
  unfold tailWord_105498
  simp only [CollatzResearch.WordTrace]
  refine ⟨961957042951559617263287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2565218781204158979368765 961957042951559617263287)
  ·
    refine ⟨1442935564427339425894931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961957042951559617263287 1442935564427339425894931)
    ·
      refine ⟨2164403346641009138842397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442935564427339425894931 2164403346641009138842397)
      ·
        refine ⟨811651254990378427065899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2164403346641009138842397 811651254990378427065899)
        ·
          refine ⟨1217476882485567640598849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811651254990378427065899 1217476882485567640598849)
          ·
            refine ⟨913107661864175730449137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217476882485567640598849 913107661864175730449137)
            ·
              refine ⟨684830746398131797836853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913107661864175730449137 684830746398131797836853)
              ·
                refine ⟨64202882474824856047205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 684830746398131797836853 64202882474824856047205)
                ·
                  refine ⟨12038040464029660508851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64202882474824856047205 12038040464029660508851)
                  ·
                    rfl

theorem cell22_105498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_105498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105498 prefixEnd_105498 := by exact prefixLift 105498
  have htrace : WordTrace (prefixWord ++ tailWord_105498) baseStart_105498 baseEnd_105498 := by
    simpa [prefixWord, tailWord_105498, baseEnd_105498] using wordTrace_append hprefix tailTrace_105498
  have hstable : (prefixWord ++ tailWord_105498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105498).length < 2 ^ (prefixWord ++ tailWord_105498).sum := by decide
  have hdescent : baseEnd_105498 < baseStart_105498 := by decide
  rcases family_descends (prefixWord ++ tailWord_105498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105543 : List Nat := [1, 1, 4, 1, 3, 3, 3, 6]
def baseStart_105543 : Nat := 118140960795 + 105543 * 2 ^ 59
def prefixEnd_105543 : Nat := 4983230072969 + 3 ^ 40 * 105543 * 2
def baseEnd_105543 : Nat := 4014391756858207127935

theorem tailTrace_105543 : CollatzResearch.WordTrace tailWord_105543 prefixEnd_105543 4014391756858207127935 := by
  unfold tailWord_105543
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849469456643211154441283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2566312971095474102960855 3849469456643211154441283)
  ·
    refine ⟨5774204184964816731661925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849469456643211154441283 5774204184964816731661925)
    ·
      refine ⟨1082663284680903137186611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5774204184964816731661925 1082663284680903137186611)
      ·
        refine ⟨1623994927021354705779917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082663284680903137186611 1623994927021354705779917)
        ·
          refine ⟨608998097633008014667469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1623994927021354705779917 608998097633008014667469)
          ·
            refine ⟨228374286612378005500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 608998097633008014667469 228374286612378005500301)
            ·
              refine ⟨85640357479641752062613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228374286612378005500301 85640357479641752062613)
              ·
                refine ⟨4014391756858207127935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85640357479641752062613 4014391756858207127935)
                ·
                  rfl

theorem cell22_105543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 6].length) (baseStart_105543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105543 prefixEnd_105543 := by exact prefixLift 105543
  have htrace : WordTrace (prefixWord ++ tailWord_105543) baseStart_105543 baseEnd_105543 := by
    simpa [prefixWord, tailWord_105543, baseEnd_105543] using wordTrace_append hprefix tailTrace_105543
  have hstable : (prefixWord ++ tailWord_105543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105543).length < 2 ^ (prefixWord ++ tailWord_105543).sum := by decide
  have hdescent : baseEnd_105543 < baseStart_105543 := by decide
  rcases family_descends (prefixWord ++ tailWord_105543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105575 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 3, 3]
def baseStart_105575 : Nat := 118140960795 + 105575 * 2 ^ 59
def prefixEnd_105575 : Nat := 4983230072969 + 3 ^ 40 * 105575 * 2
def baseEnd_105575 : Nat := 36140480065686447351317

theorem tailTrace_105575 : CollatzResearch.WordTrace tailWord_105575 prefixEnd_105575 36140480065686447351317 := by
  unfold tailWord_105575
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850636592527280619606179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2567091061684853746404119 3850636592527280619606179)
  ·
    refine ⟨5775954888790920929409269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850636592527280619606179 5775954888790920929409269)
    ·
      refine ⟨541495770824148837132119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5775954888790920929409269 541495770824148837132119)
      ·
        refine ⟨812243656236223255698179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541495770824148837132119 812243656236223255698179)
        ·
          refine ⟨1218365484354334883547269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812243656236223255698179 1218365484354334883547269)
          ·
            refine ⟨228443528316437790665113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1218365484354334883547269 228443528316437790665113)
            ·
              refine ⟨171332646237328342998835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228443528316437790665113 171332646237328342998835)
              ·
                refine ⟨256998969355992514498253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171332646237328342998835 256998969355992514498253)
                ·
                  refine ⟨96374613508497192936845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256998969355992514498253 96374613508497192936845)
                  ·
                    refine ⟨36140480065686447351317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96374613508497192936845 36140480065686447351317)
                    ·
                      rfl

theorem cell22_105575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_105575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105575 prefixEnd_105575 := by exact prefixLift 105575
  have htrace : WordTrace (prefixWord ++ tailWord_105575) baseStart_105575 baseEnd_105575 := by
    simpa [prefixWord, tailWord_105575, baseEnd_105575] using wordTrace_append hprefix tailTrace_105575
  have hstable : (prefixWord ++ tailWord_105575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105575).length < 2 ^ (prefixWord ++ tailWord_105575).sum := by decide
  have hdescent : baseEnd_105575 < baseStart_105575 := by decide
  rcases family_descends (prefixWord ++ tailWord_105575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105663 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 2, 4]
def baseStart_105663 : Nat := 118140960795 + 105663 * 2 ^ 59
def prefixEnd_105663 : Nat := 4983230072969 + 3 ^ 40 * 105663 * 2
def baseEnd_105663 : Nat := 36170604264083551151047

theorem tailTrace_105663 : CollatzResearch.WordTrace tailWord_105663 prefixEnd_105663 36170604264083551151047 := by
  unfold tailWord_105663
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853846216208471648809643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2569230810805647765873095 3853846216208471648809643)
  ·
    refine ⟨5780769324312707473214465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3853846216208471648809643 5780769324312707473214465)
    ·
      refine ⟨4335576993234530604910849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5780769324312707473214465 4335576993234530604910849)
      ·
        refine ⟨3251682744925897953683137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4335576993234530604910849 3251682744925897953683137)
        ·
          refine ⟨2438762058694423465262353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3251682744925897953683137 2438762058694423465262353)
          ·
            refine ⟨1829071544020817598946765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438762058694423465262353 1829071544020817598946765)
            ·
              refine ⟨685901829007806599605037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1829071544020817598946765 685901829007806599605037)
              ·
                refine ⟨257213185877927474851889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 685901829007806599605037 257213185877927474851889)
                ·
                  refine ⟨192909889408445606138917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257213185877927474851889 192909889408445606138917)
                  ·
                    refine ⟨36170604264083551151047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192909889408445606138917 36170604264083551151047)
                    ·
                      rfl

theorem cell22_105663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_105663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105663 prefixEnd_105663 := by exact prefixLift 105663
  have htrace : WordTrace (prefixWord ++ tailWord_105663) baseStart_105663 baseEnd_105663 := by
    simpa [prefixWord, tailWord_105663, baseEnd_105663] using wordTrace_append hprefix tailTrace_105663
  have hstable : (prefixWord ++ tailWord_105663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105663).length < 2 ^ (prefixWord ++ tailWord_105663).sum := by decide
  have hdescent : baseEnd_105663 < baseStart_105663 := by decide
  rcases family_descends (prefixWord ++ tailWord_105663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105665 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_105665 : Nat := 118140960795 + 105665 * 2 ^ 59
def prefixEnd_105665 : Nat := 4983230072969 + 3 ^ 40 * 105665 * 2
def baseEnd_105665 : Nat := 36171288904956212601041

theorem tailTrace_105665 : CollatzResearch.WordTrace tailWord_105665 prefixEnd_105665 36171288904956212601041 := by
  unfold tailWord_105665
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853919162201225990382449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2569279441467483993588299 3853919162201225990382449)
  ·
    refine ⟨2890439371650919492786837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3853919162201225990382449 2890439371650919492786837)
    ·
      refine ⟨135489345546136851224383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2890439371650919492786837 135489345546136851224383)
      ·
        refine ⟨203234018319205276836575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135489345546136851224383 203234018319205276836575)
        ·
          refine ⟨304851027478807915254863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203234018319205276836575 304851027478807915254863)
          ·
            refine ⟨457276541218211872882295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304851027478807915254863 457276541218211872882295)
            ·
              refine ⟨685914811827317809323443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457276541218211872882295 685914811827317809323443)
              ·
                refine ⟨1028872217740976713985165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685914811827317809323443 1028872217740976713985165)
                ·
                  refine ⟨385827081652866267744437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028872217740976713985165 385827081652866267744437)
                  ·
                    refine ⟨36171288904956212601041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 385827081652866267744437 36171288904956212601041)
                    ·
                      rfl

theorem cell22_105665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_105665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105665 prefixEnd_105665 := by exact prefixLift 105665
  have htrace : WordTrace (prefixWord ++ tailWord_105665) baseStart_105665 baseEnd_105665 := by
    simpa [prefixWord, tailWord_105665, baseEnd_105665] using wordTrace_append hprefix tailTrace_105665
  have hstable : (prefixWord ++ tailWord_105665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105665).length < 2 ^ (prefixWord ++ tailWord_105665).sum := by decide
  have hdescent : baseEnd_105665 < baseStart_105665 := by decide
  rcases family_descends (prefixWord ++ tailWord_105665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105678 : List Nat := [4, 1, 1, 1, 5, 10]
def baseStart_105678 : Nat := 118140960795 + 105678 * 2 ^ 59
def prefixEnd_105678 : Nat := 4983230072969 + 3 ^ 40 * 105678 * 2
def baseEnd_105678 : Nat := 446614062600352000321

theorem tailTrace_105678 : CollatzResearch.WordTrace tailWord_105678 prefixEnd_105678 446614062600352000321 := by
  unfold tailWord_105678
  simp only [CollatzResearch.WordTrace]
  refine ⟨481799163894266151325711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2569595540769419473737125 481799163894266151325711)
  ·
    refine ⟨722698745841399226988567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481799163894266151325711 722698745841399226988567)
    ·
      refine ⟨1084048118762098840482851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722698745841399226988567 1084048118762098840482851)
      ·
        refine ⟨1626072178143148260724277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084048118762098840482851 1626072178143148260724277)
        ·
          refine ⟨152444266700920149442901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1626072178143148260724277 152444266700920149442901)
          ·
            refine ⟨446614062600352000321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 152444266700920149442901 446614062600352000321)
            ·
              rfl

theorem cell22_105678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 10].length) (baseStart_105678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105678 prefixEnd_105678 := by exact prefixLift 105678
  have htrace : WordTrace (prefixWord ++ tailWord_105678) baseStart_105678 baseEnd_105678 := by
    simpa [prefixWord, tailWord_105678, baseEnd_105678] using wordTrace_append hprefix tailTrace_105678
  have hstable : (prefixWord ++ tailWord_105678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105678).length < 2 ^ (prefixWord ++ tailWord_105678).sum := by decide
  have hdescent : baseEnd_105678 < baseStart_105678 := by decide
  rcases family_descends (prefixWord ++ tailWord_105678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105682 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_105682 : Nat := 118140960795 + 105682 * 2 ^ 59
def prefixEnd_105682 : Nat := 4983230072969 + 3 ^ 40 * 105682 * 2
def baseEnd_105682 : Nat := 36177108352373834925989

theorem tailTrace_105682 : CollatzResearch.WordTrace tailWord_105682 prefixEnd_105682 36177108352373834925989 := by
  unfold tailWord_105682
  simp only [CollatzResearch.WordTrace]
  refine ⟨963634800784909473437825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2569692802093091929167533 963634800784909473437825)
  ·
    refine ⟨722726100588682105078369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 963634800784909473437825 722726100588682105078369)
    ·
      refine ⟨542044575441511578808777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722726100588682105078369 542044575441511578808777)
      ·
        refine ⟨406533431581133684106583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542044575441511578808777 406533431581133684106583)
        ·
          refine ⟨609800147371700526159875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406533431581133684106583 609800147371700526159875)
          ·
            refine ⟨914700221057550789239813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609800147371700526159875 914700221057550789239813)
            ·
              refine ⟨171506291448290772982465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 914700221057550789239813 171506291448290772982465)
              ·
                refine ⟨128629718586218079736849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171506291448290772982465 128629718586218079736849)
                ·
                  refine ⟨96472288939663559802637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128629718586218079736849 96472288939663559802637)
                  ·
                    refine ⟨36177108352373834925989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96472288939663559802637 36177108352373834925989)
                    ·
                      rfl

theorem cell22_105682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_105682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105682 prefixEnd_105682 := by exact prefixLift 105682
  have htrace : WordTrace (prefixWord ++ tailWord_105682) baseStart_105682 baseEnd_105682 := by
    simpa [prefixWord, tailWord_105682, baseEnd_105682] using wordTrace_append hprefix tailTrace_105682
  have hstable : (prefixWord ++ tailWord_105682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105682).length < 2 ^ (prefixWord ++ tailWord_105682).sum := by decide
  have hdescent : baseEnd_105682 < baseStart_105682 := by decide
  rcases family_descends (prefixWord ++ tailWord_105682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105684 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 4]
def baseStart_105684 : Nat := 118140960795 + 105684 * 2 ^ 59
def prefixEnd_105684 : Nat := 4983230072969 + 3 ^ 40 * 105684 * 2
def baseEnd_105684 : Nat := 12059264331082165458661

theorem tailTrace_105684 : CollatzResearch.WordTrace tailWord_105684 prefixEnd_105684 12059264331082165458661 := by
  unfold tailWord_105684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927306074566196117662053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2569741432754928156882737 1927306074566196117662053)
  ·
    refine ⟨361369888981161772061635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1927306074566196117662053 361369888981161772061635)
    ·
      refine ⟨542054833471742658092453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361369888981161772061635 542054833471742658092453)
      ·
        refine ⟨101635281275951748392335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 542054833471742658092453 101635281275951748392335)
        ·
          refine ⟨152452921913927622588503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101635281275951748392335 152452921913927622588503)
          ·
            refine ⟨228679382870891433882755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152452921913927622588503 228679382870891433882755)
            ·
              refine ⟨343019074306337150824133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228679382870891433882755 343019074306337150824133)
              ·
                refine ⟨64316076432438215779525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343019074306337150824133 64316076432438215779525)
                ·
                  refine ⟨12059264331082165458661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64316076432438215779525 12059264331082165458661)
                  ·
                    rfl

theorem cell22_105684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_105684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105684 prefixEnd_105684 := by exact prefixLift 105684
  have htrace : WordTrace (prefixWord ++ tailWord_105684) baseStart_105684 baseEnd_105684 := by
    simpa [prefixWord, tailWord_105684, baseEnd_105684] using wordTrace_append hprefix tailTrace_105684
  have hstable : (prefixWord ++ tailWord_105684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105684).length < 2 ^ (prefixWord ++ tailWord_105684).sum := by decide
  have hdescent : baseEnd_105684 < baseStart_105684 := by decide
  rcases family_descends (prefixWord ++ tailWord_105684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105710 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_105710 : Nat := 118140960795 + 105710 * 2 ^ 59
def prefixEnd_105710 : Nat := 4983230072969 + 3 ^ 40 * 105710 * 2
def baseEnd_105710 : Nat := 36186693324591095225903

theorem tailTrace_105710 : CollatzResearch.WordTrace tailWord_105710 prefixEnd_105710 36186693324591095225903 := by
  unfold tailWord_105710
  simp only [CollatzResearch.WordTrace]
  refine ⟨481945055879774834471323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2570373631358799117180389 481945055879774834471323)
  ·
    refine ⟨722917583819662251706985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481945055879774834471323 722917583819662251706985)
    ·
      refine ⟨542188187864746688780239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 722917583819662251706985 542188187864746688780239)
      ·
        refine ⟨813282281797120033170359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542188187864746688780239 813282281797120033170359)
        ·
          refine ⟨1219923422695680049755539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813282281797120033170359 1219923422695680049755539)
          ·
            refine ⟨1829885134043520074633309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219923422695680049755539 1829885134043520074633309)
            ·
              refine ⟨686206925266320027987491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1829885134043520074633309 686206925266320027987491)
              ·
                refine ⟨1029310387899480041981237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686206925266320027987491 1029310387899480041981237)
                ·
                  refine ⟨96497848865576253935741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029310387899480041981237 96497848865576253935741)
                  ·
                    refine ⟨36186693324591095225903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96497848865576253935741 36186693324591095225903)
                    ·
                      rfl

theorem cell22_105710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_105710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105710 prefixEnd_105710 := by exact prefixLift 105710
  have htrace : WordTrace (prefixWord ++ tailWord_105710) baseStart_105710 baseEnd_105710 := by
    simpa [prefixWord, tailWord_105710, baseEnd_105710] using wordTrace_append hprefix tailTrace_105710
  have hstable : (prefixWord ++ tailWord_105710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105710).length < 2 ^ (prefixWord ++ tailWord_105710).sum := by decide
  have hdescent : baseEnd_105710 < baseStart_105710 := by decide
  rcases family_descends (prefixWord ++ tailWord_105710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105714 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_105714 : Nat := 118140960795 + 105714 * 2 ^ 59
def prefixEnd_105714 : Nat := 4983230072969 + 3 ^ 40 * 105714 * 2
def baseEnd_105714 : Nat := 36188062606336418125891

theorem tailTrace_105714 : CollatzResearch.WordTrace tailWord_105714 prefixEnd_105714 36188062606336418125891 := by
  unfold tailWord_105714
  simp only [CollatzResearch.WordTrace]
  refine ⟨963926584755926839729049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2570470892682471572610797 963926584755926839729049)
  ·
    refine ⟨722944938566945129796787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 963926584755926839729049 722944938566945129796787)
    ·
      refine ⟨1084417407850417694695181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722944938566945129796787 1084417407850417694695181)
      ·
        refine ⟨406656527943906635510693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1084417407850417694695181 406656527943906635510693)
        ·
          refine ⟨76248098989482494158255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406656527943906635510693 76248098989482494158255)
          ·
            refine ⟨114372148484223741237383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76248098989482494158255 114372148484223741237383)
            ·
              refine ⟨171558222726335611856075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114372148484223741237383 171558222726335611856075)
              ·
                refine ⟨257337334089503417784113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171558222726335611856075 257337334089503417784113)
                ·
                  refine ⟨193003000567127563338085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257337334089503417784113 193003000567127563338085)
                  ·
                    refine ⟨36188062606336418125891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193003000567127563338085 36188062606336418125891)
                    ·
                      rfl

theorem cell22_105714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_105714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105714 prefixEnd_105714 := by exact prefixLift 105714
  have htrace : WordTrace (prefixWord ++ tailWord_105714) baseStart_105714 baseEnd_105714 := by
    simpa [prefixWord, tailWord_105714, baseEnd_105714] using wordTrace_append hprefix tailTrace_105714
  have hstable : (prefixWord ++ tailWord_105714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105714).length < 2 ^ (prefixWord ++ tailWord_105714).sum := by decide
  have hdescent : baseEnd_105714 < baseStart_105714 := by decide
  rcases family_descends (prefixWord ++ tailWord_105714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105727 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 1, 3]
def baseStart_105727 : Nat := 118140960795 + 105727 * 2 ^ 59
def prefixEnd_105727 : Nat := 4983230072969 + 3 ^ 40 * 105727 * 2
def baseEnd_105727 : Nat := 36192512772008717550851

theorem tailTrace_105727 : CollatzResearch.WordTrace tailWord_105727 prefixEnd_105727 36192512772008717550851 := by
  unfold tailWord_105727
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856180487976610579139435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2570786991984407052759623 3856180487976610579139435)
  ·
    refine ⟨5784270731964915868709153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856180487976610579139435 5784270731964915868709153)
    ·
      refine ⟨4338203048973686901531865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5784270731964915868709153 4338203048973686901531865)
      ·
        refine ⟨3253652286730265176148899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338203048973686901531865 3253652286730265176148899)
        ·
          refine ⟨4880478430095397764223349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253652286730265176148899 4880478430095397764223349)
          ·
            refine ⟨457544852821443540395939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4880478430095397764223349 457544852821443540395939)
            ·
              refine ⟨686317279232165310593909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457544852821443540395939 686317279232165310593909)
              ·
                refine ⟨64342244928015497868179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 686317279232165310593909 64342244928015497868179)
                ·
                  refine ⟨96513367392023246802269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64342244928015497868179 96513367392023246802269)
                  ·
                    refine ⟨36192512772008717550851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96513367392023246802269 36192512772008717550851)
                    ·
                      rfl

theorem cell22_105727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_105727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105727 prefixEnd_105727 := by exact prefixLift 105727
  have htrace : WordTrace (prefixWord ++ tailWord_105727) baseStart_105727 baseEnd_105727 := by
    simpa [prefixWord, tailWord_105727, baseEnd_105727] using wordTrace_append hprefix tailTrace_105727
  have hstable : (prefixWord ++ tailWord_105727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105727).length < 2 ^ (prefixWord ++ tailWord_105727).sum := by decide
  have hdescent : baseEnd_105727 < baseStart_105727 := by decide
  rcases family_descends (prefixWord ++ tailWord_105727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
