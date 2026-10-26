import V185TrunkScan23Chunk1361

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8065430 : List Nat := [5, 3, 1, 2, 1, 2, 9]
def baseStart_8065430 : Nat := 118140960795 + 8065430 * 2 ^ 59
def prefixEnd_8065430 : Nat := 4983230072969 + 3 ^ 40 * 8065430 * 2
def baseEnd_8065430 : Nat := 51128916977684990144849

theorem tailTrace_8065430 : CollatzResearch.WordTrace tailWord_8065430 prefixEnd_8065430 51128916977684990144849 := by
  unfold tailWord_8065430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18385649948145753163966109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196113599446888033748971829 18385649948145753163966109)
  ·
    refine ⟨6894618730554657436487291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18385649948145753163966109 6894618730554657436487291)
    ·
      refine ⟨10341928095831986154730937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894618730554657436487291 10341928095831986154730937)
      ·
        refine ⟨7756446071873989616048203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10341928095831986154730937 7756446071873989616048203)
        ·
          refine ⟨11634669107810984424072305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756446071873989616048203 11634669107810984424072305)
          ·
            refine ⟨8726001830858238318054229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11634669107810984424072305 8726001830858238318054229)
            ·
              refine ⟨51128916977684990144849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8726001830858238318054229 51128916977684990144849)
              ·
                rfl

theorem cell23_8065430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 9].length) (baseStart_8065430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065430 prefixEnd_8065430 := by exact prefixLift 8065430
  have htrace : WordTrace (prefixWord ++ tailWord_8065430) baseStart_8065430 baseEnd_8065430 := by
    simpa [prefixWord, tailWord_8065430, baseEnd_8065430] using wordTrace_append hprefix tailTrace_8065430
  have hstable : (prefixWord ++ tailWord_8065430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065430).length < 2 ^ (prefixWord ++ tailWord_8065430).sum := by decide
  have hdescent : baseEnd_8065430 < baseStart_8065430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065486 : List Nat := [4, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_8065486 : Nat := 118140960795 + 8065486 * 2 ^ 59
def prefixEnd_8065486 : Nat := 4983230072969 + 3 ^ 40 * 8065486 * 2
def baseEnd_8065486 : Nat := 460163447789903998070279

theorem tailTrace_8065486 : CollatzResearch.WordTrace tailWord_8065486 prefixEnd_8065486 460163447789903998070279 := by
  unfold tailWord_8065486
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771555207266146523437039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196114961105419448124997541 36771555207266146523437039)
  ·
    refine ⟨55157332810899219785155559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36771555207266146523437039 55157332810899219785155559)
    ·
      refine ⟨82735999216348829677733339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55157332810899219785155559 82735999216348829677733339)
      ·
        refine ⟨124103998824523244516600009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82735999216348829677733339 124103998824523244516600009)
        ·
          refine ⟨93077999118392433387450007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124103998824523244516600009 93077999118392433387450007)
          ·
            refine ⟨139616998677588650081175011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93077999118392433387450007 139616998677588650081175011)
            ·
              refine ⟨209425498016382975121762517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139616998677588650081175011 209425498016382975121762517)
              ·
                refine ⟨4908410109758975979416309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209425498016382975121762517 4908410109758975979416309)
                ·
                  refine ⟨460163447789903998070279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908410109758975979416309 460163447789903998070279)
                  ·
                    rfl

theorem cell23_8065486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_8065486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065486 prefixEnd_8065486 := by exact prefixLift 8065486
  have htrace : WordTrace (prefixWord ++ tailWord_8065486) baseStart_8065486 baseEnd_8065486 := by
    simpa [prefixWord, tailWord_8065486, baseEnd_8065486] using wordTrace_append hprefix tailTrace_8065486
  have hstable : (prefixWord ++ tailWord_8065486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065486).length < 2 ^ (prefixWord ++ tailWord_8065486).sum := by decide
  have hdescent : baseEnd_8065486 < baseStart_8065486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065503 : List Nat := [1, 1, 2, 3, 3, 2, 4, 2, 5]
def baseStart_8065503 : Nat := 118140960795 + 8065503 * 2 ^ 59
def prefixEnd_8065503 : Nat := 4983230072969 + 3 ^ 40 * 8065503 * 2
def baseEnd_8065503 : Nat := 460164417697806935124437

theorem tailTrace_8065503 : CollatzResearch.WordTrace tailWord_8065503 prefixEnd_8065503 460164417697806935124437 := by
  unfold tailWord_8065503
  simp only [CollatzResearch.WordTrace]
  refine ⟨294173061699067584090865163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196115374466045056060576775 294173061699067584090865163)
  ·
    refine ⟨441259592548601376136297745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294173061699067584090865163 441259592548601376136297745)
    ·
      refine ⟨330944694411451032102223309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441259592548601376136297745 330944694411451032102223309)
      ·
        refine ⟨124104260404294137038333741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330944694411451032102223309 124104260404294137038333741)
        ·
          refine ⟨46539097651610301389375153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124104260404294137038333741 46539097651610301389375153)
          ·
            refine ⟨34904323238707726042031365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46539097651610301389375153 34904323238707726042031365)
            ·
              refine ⟨6544560607257698632880881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34904323238707726042031365 6544560607257698632880881)
              ·
                refine ⟨4908420455443273974660661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544560607257698632880881 4908420455443273974660661)
                ·
                  refine ⟨460164417697806935124437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908420455443273974660661 460164417697806935124437)
                  ·
                    rfl

theorem cell23_8065503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 2, 5].length) (baseStart_8065503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065503 prefixEnd_8065503 := by exact prefixLift 8065503
  have htrace : WordTrace (prefixWord ++ tailWord_8065503) baseStart_8065503 baseEnd_8065503 := by
    simpa [prefixWord, tailWord_8065503, baseEnd_8065503] using wordTrace_append hprefix tailTrace_8065503
  have hstable : (prefixWord ++ tailWord_8065503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065503).length < 2 ^ (prefixWord ++ tailWord_8065503).sum := by decide
  have hdescent : baseEnd_8065503 < baseStart_8065503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065519 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_8065519 : Nat := 118140960795 + 8065519 * 2 ^ 59
def prefixEnd_8065519 : Nat := 4983230072969 + 3 ^ 40 * 8065519 * 2
def baseEnd_8065519 : Nat := 4141487974970734353519859

theorem tailTrace_8065519 : CollatzResearch.WordTrace tailWord_8065519 prefixEnd_8065519 4141487974970734353519859 := by
  unfold tailWord_8065519
  simp only [CollatzResearch.WordTrace]
  refine ⟨294173645267009618823447611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196115763511339745882298407 294173645267009618823447611)
  ·
    refine ⟨441260467900514428235171417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294173645267009618823447611 441260467900514428235171417)
    ·
      refine ⟨330945350925385821176378563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441260467900514428235171417 330945350925385821176378563)
      ·
        refine ⟨496418026388078731764567845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330945350925385821176378563 496418026388078731764567845)
        ·
          refine ⟨93078379947764762205856471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496418026388078731764567845 93078379947764762205856471)
          ·
            refine ⟨139617569921647143308784707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93078379947764762205856471 139617569921647143308784707)
            ·
              refine ⟨209426354882470714963177061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139617569921647143308784707 209426354882470714963177061)
              ·
                refine ⟨39267441540463259055595699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209426354882470714963177061 39267441540463259055595699)
                ·
                  refine ⟨58901162310694888583393549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39267441540463259055595699 58901162310694888583393549)
                  ·
                    refine ⟨22087935866510583218772581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58901162310694888583393549 22087935866510583218772581)
                    ·
                      refine ⟨4141487974970734353519859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22087935866510583218772581 4141487974970734353519859)
                      ·
                        rfl

theorem cell23_8065519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_8065519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065519 prefixEnd_8065519 := by exact prefixLift 8065519
  have htrace : WordTrace (prefixWord ++ tailWord_8065519) baseStart_8065519 baseEnd_8065519 := by
    simpa [prefixWord, tailWord_8065519, baseEnd_8065519] using wordTrace_append hprefix tailTrace_8065519
  have hstable : (prefixWord ++ tailWord_8065519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065519).length < 2 ^ (prefixWord ++ tailWord_8065519).sum := by decide
  have hdescent : baseEnd_8065519 < baseStart_8065519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065546 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_8065546 : Nat := 118140960795 + 8065546 * 2 ^ 59
def prefixEnd_8065546 : Nat := 4983230072969 + 3 ^ 40 * 8065546 * 2
def baseEnd_8065546 : Nat := 1380500612982801915960745

theorem tailTrace_8065546 : CollatzResearch.WordTrace tailWord_8065546 prefixEnd_8065546 1380500612982801915960745 := by
  unfold tailWord_8065546
  simp only [CollatzResearch.WordTrace]
  refine ⟨73543657509477950608670123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196116420025274534956453661 73543657509477950608670123)
  ·
    refine ⟨110315486264216925913005185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73543657509477950608670123 110315486264216925913005185)
    ·
      refine ⟨82736614698162694434753889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110315486264216925913005185 82736614698162694434753889)
      ·
        refine ⟨62052461023622020826065417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82736614698162694434753889 62052461023622020826065417)
        ·
          refine ⟨46539345767716515619549063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62052461023622020826065417 46539345767716515619549063)
          ·
            refine ⟨69809018651574773429323595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46539345767716515619549063 69809018651574773429323595)
            ·
              refine ⟨104713527977362160143985393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69809018651574773429323595 104713527977362160143985393)
              ·
                refine ⟨78535145983021620107989045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104713527977362160143985393 78535145983021620107989045)
                ·
                  refine ⟨7362669935908276885123973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78535145983021620107989045 7362669935908276885123973)
                  ·
                    refine ⟨1380500612982801915960745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362669935908276885123973 1380500612982801915960745)
                    ·
                      rfl

theorem cell23_8065546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_8065546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065546 prefixEnd_8065546 := by exact prefixLift 8065546
  have htrace : WordTrace (prefixWord ++ tailWord_8065546) baseStart_8065546 baseEnd_8065546 := by
    simpa [prefixWord, tailWord_8065546, baseEnd_8065546] using wordTrace_append hprefix tailTrace_8065546
  have hstable : (prefixWord ++ tailWord_8065546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065546).length < 2 ^ (prefixWord ++ tailWord_8065546).sum := by decide
  have hdescent : baseEnd_8065546 < baseStart_8065546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065597 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_8065597 : Nat := 118140960795 + 8065597 * 2 ^ 59
def prefixEnd_8065597 : Nat := 4983230072969 + 3 ^ 40 * 8065597 * 2
def baseEnd_8065597 : Nat := 1380509342153928349448167

theorem tailTrace_8065597 : CollatzResearch.WordTrace tailWord_8065597 prefixEnd_8065597 1380509342153928349448167 := by
  unfold tailWord_8065597
  simp only [CollatzResearch.WordTrace]
  refine ⟨294176490160727038144787045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196117660107151358763191363 294176490160727038144787045)
  ·
    refine ⟨55158091905136319652147571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294176490160727038144787045 55158091905136319652147571)
    ·
      refine ⟨82737137857704479478221357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55158091905136319652147571 82737137857704479478221357)
      ·
        refine ⟨31026426696639179804333009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82737137857704479478221357 31026426696639179804333009)
        ·
          refine ⟨23269820022479384853249757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31026426696639179804333009 23269820022479384853249757)
          ·
            refine ⟨8726182508429769319968659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23269820022479384853249757 8726182508429769319968659)
            ·
              refine ⟨13089273762644653979952989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726182508429769319968659 13089273762644653979952989)
              ·
                refine ⟨4908477660991745242482371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13089273762644653979952989 4908477660991745242482371)
                ·
                  refine ⟨7362716491487617863723557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908477660991745242482371 7362716491487617863723557)
                  ·
                    refine ⟨1380509342153928349448167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362716491487617863723557 1380509342153928349448167)
                    ·
                      rfl

theorem cell23_8065597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_8065597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065597 prefixEnd_8065597 := by exact prefixLift 8065597
  have htrace : WordTrace (prefixWord ++ tailWord_8065597) baseStart_8065597 baseEnd_8065597 := by
    simpa [prefixWord, tailWord_8065597, baseEnd_8065597] using wordTrace_append hprefix tailTrace_8065597
  have hstable : (prefixWord ++ tailWord_8065597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065597).length < 2 ^ (prefixWord ++ tailWord_8065597).sum := by decide
  have hdescent : baseEnd_8065597 < baseStart_8065597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065620 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_8065620 : Nat := 118140960795 + 8065620 * 2 ^ 59
def prefixEnd_8065620 : Nat := 4983230072969 + 3 ^ 40 * 8065620 * 2
def baseEnd_8065620 : Nat := 4141539836516838458356895

theorem tailTrace_8065620 : CollatzResearch.WordTrace tailWord_8065620 prefixEnd_8065620 4141539836516838458356895 := by
  unfold tailWord_8065620
  simp only [CollatzResearch.WordTrace]
  refine ⟨147088664519821856536437157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196118219359762475381916209 147088664519821856536437157)
  ·
    refine ⟨27579124597466598100581967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147088664519821856536437157 27579124597466598100581967)
    ·
      refine ⟨41368686896199897150872951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27579124597466598100581967 41368686896199897150872951)
      ·
        refine ⟨62053030344299845726309427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41368686896199897150872951 62053030344299845726309427)
        ·
          refine ⟨93079545516449768589464141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62053030344299845726309427 93079545516449768589464141)
          ·
            refine ⟨34904829568668663221049053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93079545516449768589464141 34904829568668663221049053)
            ·
              refine ⟨13089311088250748707893395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34904829568668663221049053 13089311088250748707893395)
              ·
                refine ⟨19633966632376123061840093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13089311088250748707893395 19633966632376123061840093)
                ·
                  refine ⟨7362737487141046148190035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19633966632376123061840093 7362737487141046148190035)
                  ·
                    refine ⟨11044106230711569222285053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362737487141046148190035 11044106230711569222285053)
                    ·
                      refine ⟨4141539836516838458356895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11044106230711569222285053 4141539836516838458356895)
                      ·
                        rfl

theorem cell23_8065620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_8065620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065620 prefixEnd_8065620 := by exact prefixLift 8065620
  have htrace : WordTrace (prefixWord ++ tailWord_8065620) baseStart_8065620 baseEnd_8065620 := by
    simpa [prefixWord, tailWord_8065620, baseEnd_8065620] using wordTrace_append hprefix tailTrace_8065620
  have hstable : (prefixWord ++ tailWord_8065620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065620).length < 2 ^ (prefixWord ++ tailWord_8065620).sum := by decide
  have hdescent : baseEnd_8065620 < baseStart_8065620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065636 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_8065636 : Nat := 118140960795 + 8065636 * 2 ^ 59
def prefixEnd_8065636 : Nat := 4983230072969 + 3 ^ 40 * 8065636 * 2
def baseEnd_8065636 : Nat := 1380516017402436798585607

theorem tailTrace_8065636 : CollatzResearch.WordTrace tailWord_8065636 prefixEnd_8065636 1380516017402436798585607 := by
  unfold tailWord_8065636
  simp only [CollatzResearch.WordTrace]
  refine ⟨147088956303792873902728381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196118608405057165203637841 147088956303792873902728381)
  ·
    refine ⟨55158358613922327713523143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147088956303792873902728381 55158358613922327713523143)
    ·
      refine ⟨82737537920883491570284715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55158358613922327713523143 82737537920883491570284715)
      ·
        refine ⟨124106306881325237355427073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82737537920883491570284715 124106306881325237355427073)
        ·
          refine ⟨93079730160993928016570305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124106306881325237355427073 93079730160993928016570305)
          ·
            refine ⟨69809797620745446012427729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93079730160993928016570305 69809797620745446012427729)
            ·
              refine ⟨52357348215559084509320797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69809797620745446012427729 52357348215559084509320797)
              ·
                refine ⟨19634005580834656690995299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52357348215559084509320797 19634005580834656690995299)
                ·
                  refine ⟨29451008371251985036492949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19634005580834656690995299 29451008371251985036492949)
                  ·
                    refine ⟨1380516017402436798585607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29451008371251985036492949 1380516017402436798585607)
                    ·
                      rfl

theorem cell23_8065636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_8065636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065636 prefixEnd_8065636 := by exact prefixLift 8065636
  have htrace : WordTrace (prefixWord ++ tailWord_8065636) baseStart_8065636 baseEnd_8065636 := by
    simpa [prefixWord, tailWord_8065636, baseEnd_8065636] using wordTrace_append hprefix tailTrace_8065636
  have hstable : (prefixWord ++ tailWord_8065636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065636).length < 2 ^ (prefixWord ++ tailWord_8065636).sum := by decide
  have hdescent : baseEnd_8065636 < baseStart_8065636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065656 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_8065656 : Nat := 118140960795 + 8065656 * 2 ^ 59
def prefixEnd_8065656 : Nat := 4983230072969 + 3 ^ 40 * 8065656 * 2
def baseEnd_8065656 : Nat := 4141558321820400317506729

theorem tailTrace_8065656 : CollatzResearch.WordTrace tailWord_8065656 prefixEnd_8065656 4141558321820400317506729 := by
  unfold tailWord_8065656
  simp only [CollatzResearch.WordTrace]
  refine ⟨147089321033756645610592411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196119094711675527480789881 147089321033756645610592411)
  ·
    refine ⟨220633981550634968415888617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147089321033756645610592411 220633981550634968415888617)
    ·
      refine ⟨165475486162976226311916463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220633981550634968415888617 165475486162976226311916463)
      ·
        refine ⟨248213229244464339467874695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165475486162976226311916463 248213229244464339467874695)
        ·
          refine ⟨372319843866696509201812043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248213229244464339467874695 372319843866696509201812043)
          ·
            refine ⟨558479765800044763802718065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372319843866696509201812043 558479765800044763802718065)
            ·
              refine ⟨418859824350033572852038549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558479765800044763802718065 418859824350033572852038549)
              ·
                refine ⟨19634054266407823727439307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 418859824350033572852038549 19634054266407823727439307)
                ·
                  refine ⟨29451081399611735591158961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19634054266407823727439307 29451081399611735591158961)
                  ·
                    refine ⟨22088311049708801693369221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29451081399611735591158961 22088311049708801693369221)
                    ·
                      refine ⟨4141558321820400317506729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22088311049708801693369221 4141558321820400317506729)
                      ·
                        rfl

theorem cell23_8065656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_8065656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065656 prefixEnd_8065656 := by exact prefixLift 8065656
  have htrace : WordTrace (prefixWord ++ tailWord_8065656) baseStart_8065656 baseEnd_8065656 := by
    simpa [prefixWord, tailWord_8065656, baseEnd_8065656] using wordTrace_append hprefix tailTrace_8065656
  have hstable : (prefixWord ++ tailWord_8065656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065656).length < 2 ^ (prefixWord ++ tailWord_8065656).sum := by decide
  have hdescent : baseEnd_8065656 < baseStart_8065656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065693 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_8065693 : Nat := 118140960795 + 8065693 * 2 ^ 59
def prefixEnd_8065693 : Nat := 4983230072969 + 3 ^ 40 * 8065693 * 2
def baseEnd_8065693 : Nat := 4141577320604616672744059

theorem tailTrace_8065693 : CollatzResearch.WordTrace tailWord_8065693 prefixEnd_8065693 4141577320604616672744059 := by
  unfold tailWord_8065693
  simp only [CollatzResearch.WordTrace]
  refine ⟨294179991568379246540281733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196119994378919497693521155 294179991568379246540281733)
  ·
    refine ⟨55158748419071108726302825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294179991568379246540281733 55158748419071108726302825)
    ·
      refine ⟨41369061314303331544727119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55158748419071108726302825 41369061314303331544727119)
      ·
        refine ⟨62053591971454997317090679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41369061314303331544727119 62053591971454997317090679)
        ·
          refine ⟨93080387957182495975636019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62053591971454997317090679 93080387957182495975636019)
          ·
            refine ⟨139620581935773743963454029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93080387957182495975636019 139620581935773743963454029)
            ·
              refine ⟨52357718225915153986295261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139620581935773743963454029 52357718225915153986295261)
              ·
                refine ⟨19634144334718182744860723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52357718225915153986295261 19634144334718182744860723)
                ·
                  refine ⟨29451216502077274117291085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19634144334718182744860723 29451216502077274117291085)
                  ·
                    refine ⟨11044206188278977793984157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29451216502077274117291085 11044206188278977793984157)
                    ·
                      refine ⟨4141577320604616672744059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11044206188278977793984157 4141577320604616672744059)
                      ·
                        rfl

theorem cell23_8065693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_8065693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065693 prefixEnd_8065693 := by exact prefixLift 8065693
  have htrace : WordTrace (prefixWord ++ tailWord_8065693) baseStart_8065693 baseEnd_8065693 := by
    simpa [prefixWord, tailWord_8065693, baseEnd_8065693] using wordTrace_append hprefix tailTrace_8065693
  have hstable : (prefixWord ++ tailWord_8065693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065693).length < 2 ^ (prefixWord ++ tailWord_8065693).sum := by decide
  have hdescent : baseEnd_8065693 < baseStart_8065693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065727 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 3]
def baseStart_8065727 : Nat := 118140960795 + 8065727 * 2 ^ 59
def prefixEnd_8065727 : Nat := 4983230072969 + 3 ^ 40 * 8065727 * 2
def baseEnd_8065727 : Nat := 4141594778946869539718903

theorem tailTrace_8065727 : CollatzResearch.WordTrace tailWord_8065727 prefixEnd_8065727 4141594778946869539718903 := by
  unfold tailWord_8065727
  simp only [CollatzResearch.WordTrace]
  refine ⟨294181231650256070347019435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196120821100170713564679623 294181231650256070347019435)
  ·
    refine ⟨441271847475384105520529153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294181231650256070347019435 441271847475384105520529153)
    ·
      refine ⟨330953885606538079140396865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441271847475384105520529153 330953885606538079140396865)
      ·
        refine ⟨248215414204903559355297649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330953885606538079140396865 248215414204903559355297649)
        ·
          refine ⟨186161560653677669516473237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248215414204903559355297649 186161560653677669516473237)
          ·
            refine ⟨8726323155641140758584683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186161560653677669516473237 8726323155641140758584683)
            ·
              refine ⟨13089484733461711137877025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726323155641140758584683 13089484733461711137877025)
              ·
                refine ⟨9817113550096283353407769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13089484733461711137877025 9817113550096283353407769)
                ·
                  refine ⟨7362835162572212515055827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9817113550096283353407769 7362835162572212515055827)
                  ·
                    refine ⟨11044252743858318772583741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362835162572212515055827 11044252743858318772583741)
                    ·
                      refine ⟨4141594778946869539718903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11044252743858318772583741 4141594778946869539718903)
                      ·
                        rfl

theorem cell23_8065727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_8065727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065727 prefixEnd_8065727 := by exact prefixLift 8065727
  have htrace : WordTrace (prefixWord ++ tailWord_8065727) baseStart_8065727 baseEnd_8065727 := by
    simpa [prefixWord, tailWord_8065727, baseEnd_8065727] using wordTrace_append hprefix tailTrace_8065727
  have hstable : (prefixWord ++ tailWord_8065727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065727).length < 2 ^ (prefixWord ++ tailWord_8065727).sum := by decide
  have hdescent : baseEnd_8065727 < baseStart_8065727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065790 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_8065790 : Nat := 118140960795 + 8065790 * 2 ^ 59
def prefixEnd_8065790 : Nat := 4983230072969 + 3 ^ 40 * 8065790 * 2
def baseEnd_8065790 : Nat := 460180792025344754803457

theorem tailTrace_8065790 : CollatzResearch.WordTrace tailWord_8065790 prefixEnd_8065790 460180792025344754803457 := by
  unfold tailWord_8065790
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772941181128479013320353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196122352966018554737708549 36772941181128479013320353)
  ·
    refine ⟨27579705885846359259990265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36772941181128479013320353 27579705885846359259990265)
    ·
      refine ⟨20684779414384769444992699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27579705885846359259990265 20684779414384769444992699)
      ·
        refine ⟨31027169121577154167489049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20684779414384769444992699 31027169121577154167489049)
        ·
          refine ⟨23270376841182865625616787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31027169121577154167489049 23270376841182865625616787)
          ·
            refine ⟨34905565261774298438425181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23270376841182865625616787 34905565261774298438425181)
            ·
              refine ⟨13089586973165361914409443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34905565261774298438425181 13089586973165361914409443)
              ·
                refine ⟨19634380459748042871614165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13089586973165361914409443 19634380459748042871614165)
                ·
                  refine ⟨460180792025344754803457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19634380459748042871614165 460180792025344754803457)
                  ·
                    rfl

theorem cell23_8065790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_8065790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065790 prefixEnd_8065790 := by exact prefixLift 8065790
  have htrace : WordTrace (prefixWord ++ tailWord_8065790) baseStart_8065790 baseEnd_8065790 := by
    simpa [prefixWord, tailWord_8065790, baseEnd_8065790] using wordTrace_append hprefix tailTrace_8065790
  have hstable : (prefixWord ++ tailWord_8065790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065790).length < 2 ^ (prefixWord ++ tailWord_8065790).sum := by decide
  have hdescent : baseEnd_8065790 < baseStart_8065790 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065820 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_8065820 : Nat := 118140960795 + 8065820 * 2 ^ 59
def prefixEnd_8065820 : Nat := 4983230072969 + 3 ^ 40 * 8065820 * 2
def baseEnd_8065820 : Nat := 1380547510882579225285325

theorem tailTrace_8065820 : CollatzResearch.WordTrace tailWord_8065820 prefixEnd_8065820 1380547510882579225285325 := by
  unfold tailWord_8065820
  simp only [CollatzResearch.WordTrace]
  refine ⟨147092311819459573615077457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196123082425946098153436609 147092311819459573615077457)
  ·
    refine ⟨110319233864594680211308093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147092311819459573615077457 110319233864594680211308093)
    ·
      refine ⟨41369712699223005079240535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110319233864594680211308093 41369712699223005079240535)
      ·
        refine ⟨62054569048834507618860803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41369712699223005079240535 62054569048834507618860803)
        ·
          refine ⟨93081853573251761428291205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62054569048834507618860803 93081853573251761428291205)
          ·
            refine ⟨17452847544984705267804601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93081853573251761428291205 17452847544984705267804601)
            ·
              refine ⟨13089635658738528950853451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17452847544984705267804601 13089635658738528950853451)
              ·
                refine ⟨19634453488107793426280177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13089635658738528950853451 19634453488107793426280177)
                ·
                  refine ⟨14725840116080845069710133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19634453488107793426280177 14725840116080845069710133)
                  ·
                    refine ⟨1380547510882579225285325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14725840116080845069710133 1380547510882579225285325)
                    ·
                      rfl

theorem cell23_8065820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_8065820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065820 prefixEnd_8065820 := by exact prefixLift 8065820
  have htrace : WordTrace (prefixWord ++ tailWord_8065820) baseStart_8065820 baseEnd_8065820 := by
    simpa [prefixWord, tailWord_8065820, baseEnd_8065820] using wordTrace_append hprefix tailTrace_8065820
  have hstable : (prefixWord ++ tailWord_8065820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065820).length < 2 ^ (prefixWord ++ tailWord_8065820).sum := by decide
  have hdescent : baseEnd_8065820 < baseStart_8065820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065833 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 5, 4]
def baseStart_8065833 : Nat := 118140960795 + 8065833 * 2 ^ 59
def prefixEnd_8065833 : Nat := 4983230072969 + 3 ^ 40 * 8065833 * 2
def baseEnd_8065833 : Nat := 1380549735965415374997805

theorem tailTrace_8065833 : CollatzResearch.WordTrace tailWord_8065833 prefixEnd_8065833 1380549735965415374997805 := by
  unfold tailWord_8065833
  simp only [CollatzResearch.WordTrace]
  refine ⟨294185097787872050450378153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196123398525248033633585435 294185097787872050450378153)
  ·
    refine ⟨220638823340904037837783615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294185097787872050450378153 220638823340904037837783615)
    ·
      refine ⟨330958235011356056756675423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220638823340904037837783615 330958235011356056756675423)
      ·
        refine ⟨496437352517034085135013135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330958235011356056756675423 496437352517034085135013135)
        ·
          refine ⟨744656028775551127702519703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496437352517034085135013135 744656028775551127702519703)
          ·
            refine ⟨1116984043163326691553779555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744656028775551127702519703 1116984043163326691553779555)
            ·
              refine ⟨1675476064744990037330669333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116984043163326691553779555 1675476064744990037330669333)
              ·
                refine ⟨78537940534921407999875125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1675476064744990037330669333 78537940534921407999875125)
                ·
                  refine ⟨7362931925148881999988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78537940534921407999875125 7362931925148881999988293)
                  ·
                    refine ⟨1380549735965415374997805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362931925148881999988293 1380549735965415374997805)
                    ·
                      rfl

theorem cell23_8065833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_8065833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065833 prefixEnd_8065833 := by exact prefixLift 8065833
  have htrace : WordTrace (prefixWord ++ tailWord_8065833) baseStart_8065833 baseEnd_8065833 := by
    simpa [prefixWord, tailWord_8065833, baseEnd_8065833] using wordTrace_append hprefix tailTrace_8065833
  have hstable : (prefixWord ++ tailWord_8065833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065833).length < 2 ^ (prefixWord ++ tailWord_8065833).sum := by decide
  have hdescent : baseEnd_8065833 < baseStart_8065833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065884 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_8065884 : Nat := 118140960795 + 8065884 * 2 ^ 59
def prefixEnd_8065884 : Nat := 4983230072969 + 3 ^ 40 * 8065884 * 2
def baseEnd_8065884 : Nat := 1380558465136541808485227

theorem tailTrace_8065884 : CollatzResearch.WordTrace tailWord_8065884 prefixEnd_8065884 1380558465136541808485227 := by
  unfold tailWord_8065884
  simp only [CollatzResearch.WordTrace]
  refine ⟨147093478955343643080242353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196124638607124857440323137 147093478955343643080242353)
  ·
    refine ⟨110320109216507732310181765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147093478955343643080242353 110320109216507732310181765)
    ·
      refine ⟨20685020478095199808159081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110320109216507732310181765 20685020478095199808159081)
      ·
        refine ⟨15513765358571399856119311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20685020478095199808159081 15513765358571399856119311)
        ·
          refine ⟨23270648037857099784178967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15513765358571399856119311 23270648037857099784178967)
          ·
            refine ⟨34905972056785649676268451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23270648037857099784178967 34905972056785649676268451)
            ·
              refine ⟨52358958085178474514402677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34905972056785649676268451 52358958085178474514402677)
              ·
                refine ⟨4908652320485481985725251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52358958085178474514402677 4908652320485481985725251)
                ·
                  refine ⟨7362978480728222978587877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908652320485481985725251 7362978480728222978587877)
                  ·
                    refine ⟨1380558465136541808485227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362978480728222978587877 1380558465136541808485227)
                    ·
                      rfl

theorem cell23_8065884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_8065884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065884 prefixEnd_8065884 := by exact prefixLift 8065884
  have htrace : WordTrace (prefixWord ++ tailWord_8065884) baseStart_8065884 baseEnd_8065884 := by
    simpa [prefixWord, tailWord_8065884, baseEnd_8065884] using wordTrace_append hprefix tailTrace_8065884
  have hstable : (prefixWord ++ tailWord_8065884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065884).length < 2 ^ (prefixWord ++ tailWord_8065884).sum := by decide
  have hdescent : baseEnd_8065884 < baseStart_8065884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065927 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 1, 5]
def baseStart_8065927 : Nat := 118140960795 + 8065927 * 2 ^ 59
def prefixEnd_8065927 : Nat := 4983230072969 + 3 ^ 40 * 8065927 * 2
def baseEnd_8065927 : Nat := 1380565825025922919072661

theorem tailTrace_8065927 : CollatzResearch.WordTrace tailWord_8065927 prefixEnd_8065927 1380565825025922919072661 := by
  unfold tailWord_8065927
  simp only [CollatzResearch.WordTrace]
  refine ⟨294188526249531504504300035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196125684166354336336200023 294188526249531504504300035)
  ·
    refine ⟨441282789374297256756450053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294188526249531504504300035 441282789374297256756450053)
    ·
      refine ⟨82740523007680735641834385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441282789374297256756450053 82740523007680735641834385)
      ·
        refine ⟨62055392255760551731375789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82740523007680735641834385 62055392255760551731375789)
        ·
          refine ⟨23270772095910206899265921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62055392255760551731375789 23270772095910206899265921)
          ·
            refine ⟨17453079071932655174449441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23270772095910206899265921 17453079071932655174449441)
            ·
              refine ⟨13089809303949491380837081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17453079071932655174449441 13089809303949491380837081)
              ·
                refine ⟨9817356977962118535627811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13089809303949491380837081 9817356977962118535627811)
                ·
                  refine ⟨14726035466943177803441717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817356977962118535627811 14726035466943177803441717)
                  ·
                    refine ⟨1380565825025922919072661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14726035466943177803441717 1380565825025922919072661)
                    ·
                      rfl

theorem cell23_8065927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_8065927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065927 prefixEnd_8065927 := by exact prefixLift 8065927
  have htrace : WordTrace (prefixWord ++ tailWord_8065927) baseStart_8065927 baseEnd_8065927 := by
    simpa [prefixWord, tailWord_8065927, baseEnd_8065927] using wordTrace_append hprefix tailTrace_8065927
  have hstable : (prefixWord ++ tailWord_8065927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065927).length < 2 ^ (prefixWord ++ tailWord_8065927).sum := by decide
  have hdescent : baseEnd_8065927 < baseStart_8065927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065940 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_8065940 : Nat := 118140960795 + 8065940 * 2 ^ 59
def prefixEnd_8065940 : Nat := 4983230072969 + 3 ^ 40 * 8065940 * 2
def baseEnd_8065940 : Nat := 1380568050108759068785141

theorem tailTrace_8065940 : CollatzResearch.WordTrace tailWord_8065940 prefixEnd_8065940 1380568050108759068785141 := by
  unfold tailWord_8065940
  simp only [CollatzResearch.WordTrace]
  refine ⟨147094500199242203862261637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196126000265656271816348849 147094500199242203862261637)
  ·
    refine ⟨27580218787357913224174057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147094500199242203862261637 27580218787357913224174057)
    ·
      refine ⟨20685164090518434918130543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27580218787357913224174057 20685164090518434918130543)
      ·
        refine ⟨31027746135777652377195815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20685164090518434918130543 31027746135777652377195815)
        ·
          refine ⟨46541619203666478565793723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31027746135777652377195815 46541619203666478565793723)
          ·
            refine ⟨69812428805499717848690585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46541619203666478565793723 69812428805499717848690585)
            ·
              refine ⟨52359321604124788386517939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69812428805499717848690585 52359321604124788386517939)
              ·
                refine ⟨78538982406187182579776909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52359321604124788386517939 78538982406187182579776909)
                ·
                  refine ⟨29452118402320193467416341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78538982406187182579776909 29452118402320193467416341)
                  ·
                    refine ⟨1380568050108759068785141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29452118402320193467416341 1380568050108759068785141)
                    ·
                      rfl

theorem cell23_8065940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_8065940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065940 prefixEnd_8065940 := by exact prefixLift 8065940
  have htrace : WordTrace (prefixWord ++ tailWord_8065940) baseStart_8065940 baseEnd_8065940 := by
    simpa [prefixWord, tailWord_8065940, baseEnd_8065940] using wordTrace_append hprefix tailTrace_8065940
  have hstable : (prefixWord ++ tailWord_8065940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065940).length < 2 ^ (prefixWord ++ tailWord_8065940).sum := by decide
  have hdescent : baseEnd_8065940 < baseStart_8065940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065941 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_8065941 : Nat := 118140960795 + 8065941 * 2 ^ 59
def prefixEnd_8065941 : Nat := 4983230072969 + 3 ^ 40 * 8065941 * 2
def baseEnd_8065941 : Nat := 4141704663806931702442919

theorem tailTrace_8065941 : CollatzResearch.WordTrace tailWord_8065941 prefixEnd_8065941 4141704663806931702442919 := by
  unfold tailWord_8065941
  simp only [CollatzResearch.WordTrace]
  refine ⟨294189036871480784895309677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196126024580987189930206451 294189036871480784895309677)
  ·
    refine ⟨110320888826805294335741129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294189036871480784895309677 110320888826805294335741129)
    ·
      refine ⟨82740666620103970751805847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110320888826805294335741129 82740666620103970751805847)
      ·
        refine ⟨124110999930155956127708771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82740666620103970751805847 124110999930155956127708771)
        ·
          refine ⟨186166499895233934191563157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124110999930155956127708771 186166499895233934191563157)
          ·
            refine ⟨8726554682589090665229523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186166499895233934191563157 8726554682589090665229523)
            ·
              refine ⟨13089832023883635997844285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726554682589090665229523 13089832023883635997844285)
              ·
                refine ⟨4908687008956363499191607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13089832023883635997844285 4908687008956363499191607)
                ·
                  refine ⟨7363030513434545248787411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908687008956363499191607 7363030513434545248787411)
                  ·
                    refine ⟨11044545770151817873181117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7363030513434545248787411 11044545770151817873181117)
                    ·
                      refine ⟨4141704663806931702442919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11044545770151817873181117 4141704663806931702442919)
                      ·
                        rfl

theorem cell23_8065941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_8065941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065941 prefixEnd_8065941 := by exact prefixLift 8065941
  have htrace : WordTrace (prefixWord ++ tailWord_8065941) baseStart_8065941 baseEnd_8065941 := by
    simpa [prefixWord, tailWord_8065941, baseEnd_8065941] using wordTrace_append hprefix tailTrace_8065941
  have hstable : (prefixWord ++ tailWord_8065941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065941).length < 2 ^ (prefixWord ++ tailWord_8065941).sum := by decide
  have hdescent : baseEnd_8065941 < baseStart_8065941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065981 : List Nat := [1, 4, 1, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_8065981 : Nat := 118140960795 + 8065981 * 2 ^ 59
def prefixEnd_8065981 : Nat := 4983230072969 + 3 ^ 40 * 8065981 * 2
def baseEnd_8065981 : Nat := 4141725203033111545942735

theorem tailTrace_8065981 : CollatzResearch.WordTrace tailWord_8065981 prefixEnd_8065981 4141725203033111545942735 := by
  unfold tailWord_8065981
  simp only [CollatzResearch.WordTrace]
  refine ⟨294190495791335871726765797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196126997194223914484510531 294190495791335871726765797)
  ·
    refine ⟨55160717960875475948768587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294190495791335871726765797 55160717960875475948768587)
    ·
      refine ⟨82741076941313213923152881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55160717960875475948768587 82741076941313213923152881)
      ·
        refine ⟨62055807705984910442364661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82741076941313213923152881 62055807705984910442364661)
        ·
          refine ⟨5817731972436085353971687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62055807705984910442364661 5817731972436085353971687)
          ·
            refine ⟨8726597958654128030957531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817731972436085353971687 8726597958654128030957531)
            ·
              refine ⟨13089896937981192046436297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726597958654128030957531 13089896937981192046436297)
              ·
                refine ⟨9817422703485894034827223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13089896937981192046436297 9817422703485894034827223)
                ·
                  refine ⟨14726134055228841052240835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817422703485894034827223 14726134055228841052240835)
                  ·
                    refine ⟨22089201082843261578361253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14726134055228841052240835 22089201082843261578361253)
                    ·
                      refine ⟨4141725203033111545942735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22089201082843261578361253 4141725203033111545942735)
                      ·
                        rfl

theorem cell23_8065981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_8065981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065981 prefixEnd_8065981 := by exact prefixLift 8065981
  have htrace : WordTrace (prefixWord ++ tailWord_8065981) baseStart_8065981 baseEnd_8065981 := by
    simpa [prefixWord, tailWord_8065981, baseEnd_8065981] using wordTrace_append hprefix tailTrace_8065981
  have hstable : (prefixWord ++ tailWord_8065981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065981).length < 2 ^ (prefixWord ++ tailWord_8065981).sum := by decide
  have hdescent : baseEnd_8065981 < baseStart_8065981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065983 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 4, 7]
def baseStart_8065983 : Nat := 118140960795 + 8065983 * 2 ^ 59
def prefixEnd_8065983 : Nat := 4983230072969 + 3 ^ 40 * 8065983 * 2
def baseEnd_8065983 : Nat := 1380575409998140179372575

theorem tailTrace_8065983 : CollatzResearch.WordTrace tailWord_8065983 prefixEnd_8065983 1380575409998140179372575 := by
  unfold tailWord_8065983
  simp only [CollatzResearch.WordTrace]
  refine ⟨294190568737328626068338603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196127045824885750712225735 294190568737328626068338603)
  ·
    refine ⟨441285853105992939102507905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294190568737328626068338603 441285853105992939102507905)
    ·
      refine ⟨330964389829494704326880929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441285853105992939102507905 330964389829494704326880929)
      ·
        refine ⟨248223292372121028245160697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330964389829494704326880929 248223292372121028245160697)
        ·
          refine ⟨186167469279090771183870523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248223292372121028245160697 186167469279090771183870523)
          ·
            refine ⟨279251203918636156775805785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186167469279090771183870523 279251203918636156775805785)
            ·
              refine ⟨209438402938977117581854339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279251203918636156775805785 209438402938977117581854339)
              ·
                refine ⟨314157604408465676372781509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209438402938977117581854339 314157604408465676372781509)
                ·
                  refine ⟨58904550826587314319896533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314157604408465676372781509 58904550826587314319896533)
                  ·
                    refine ⟨1380575409998140179372575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58904550826587314319896533 1380575409998140179372575)
                    ·
                      rfl

theorem cell23_8065983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_8065983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065983 prefixEnd_8065983 := by exact prefixLift 8065983
  have htrace : WordTrace (prefixWord ++ tailWord_8065983) baseStart_8065983 baseEnd_8065983 := by
    simpa [prefixWord, tailWord_8065983, baseEnd_8065983] using wordTrace_append hprefix tailTrace_8065983
  have hstable : (prefixWord ++ tailWord_8065983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065983).length < 2 ^ (prefixWord ++ tailWord_8065983).sum := by decide
  have hdescent : baseEnd_8065983 < baseStart_8065983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065984 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3]
def baseStart_8065984 : Nat := 118140960795 + 8065984 * 2 ^ 59
def prefixEnd_8065984 : Nat := 4983230072969 + 3 ^ 40 * 8065984 * 2
def baseEnd_8065984 : Nat := 4141726743475075034205221

theorem tailTrace_8065984 : CollatzResearch.WordTrace tailWord_8065984 prefixEnd_8065984 4141726743475075034205221 := by
  unfold tailWord_8065984
  simp only [CollatzResearch.WordTrace]
  refine ⟨147095302605162501619562503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196127070140216668826083337 147095302605162501619562503)
  ·
    refine ⟨220642953907743752429343755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147095302605162501619562503 220642953907743752429343755)
    ·
      refine ⟨330964430861615628644015633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220642953907743752429343755 330964430861615628644015633)
      ·
        refine ⟨248223323146211721483011725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330964430861615628644015633 248223323146211721483011725)
        ·
          refine ⟨93083746179829395556129397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248223323146211721483011725 93083746179829395556129397)
          ·
            refine ⟨8726601204359005833387131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93083746179829395556129397 8726601204359005833387131)
            ·
              refine ⟨13089901806538508750080697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726601204359005833387131 13089901806538508750080697)
              ·
                refine ⟨9817426354903881562560523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13089901806538508750080697 9817426354903881562560523)
                ·
                  refine ⟨14726139532355822343840785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817426354903881562560523 14726139532355822343840785)
                  ·
                    refine ⟨11044604649266866757880589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14726139532355822343840785 11044604649266866757880589)
                    ·
                      refine ⟨4141726743475075034205221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11044604649266866757880589 4141726743475075034205221)
                      ·
                        rfl

theorem cell23_8065984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_8065984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065984 prefixEnd_8065984 := by exact prefixLift 8065984
  have htrace : WordTrace (prefixWord ++ tailWord_8065984) baseStart_8065984 baseEnd_8065984 := by
    simpa [prefixWord, tailWord_8065984, baseEnd_8065984] using wordTrace_append hprefix tailTrace_8065984
  have hstable : (prefixWord ++ tailWord_8065984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065984).length < 2 ^ (prefixWord ++ tailWord_8065984).sum := by decide
  have hdescent : baseEnd_8065984 < baseStart_8065984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066015 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 1, 2, 2]
def baseStart_8066015 : Nat := 118140960795 + 8066015 * 2 ^ 59
def prefixEnd_8066015 : Nat := 4983230072969 + 3 ^ 40 * 8066015 * 2
def baseEnd_8066015 : Nat := 4141742661375364412917579

theorem tailTrace_8066015 : CollatzResearch.WordTrace tailWord_8066015 prefixEnd_8066015 4141742661375364412917579 := by
  unfold tailWord_8066015
  simp only [CollatzResearch.WordTrace]
  refine ⟨294191735873212695533503499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196127823915475130355668999 294191735873212695533503499)
  ·
    refine ⟨441287603809819043300255249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294191735873212695533503499 441287603809819043300255249)
    ·
      refine ⟨330965702857364282475191437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441287603809819043300255249 330965702857364282475191437)
      ·
        refine ⟨124112138571511605928196789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330965702857364282475191437 124112138571511605928196789)
        ·
          refine ⟨11635512991079213055768449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124112138571511605928196789 11635512991079213055768449)
          ·
            refine ⟨8726634743309409791826337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11635512991079213055768449 8726634743309409791826337)
            ·
              refine ⟨6544976057482057343869753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726634743309409791826337 6544976057482057343869753)
              ·
                refine ⟨4908732043111543007902315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544976057482057343869753 4908732043111543007902315)
                ·
                  refine ⟨7363098064667314511853473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908732043111543007902315 7363098064667314511853473)
                  ·
                    refine ⟨5522323548500485883890105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7363098064667314511853473 5522323548500485883890105)
                    ·
                      refine ⟨4141742661375364412917579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522323548500485883890105 4141742661375364412917579)
                      ·
                        rfl

theorem cell23_8066015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_8066015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066015 prefixEnd_8066015 := by exact prefixLift 8066015
  have htrace : WordTrace (prefixWord ++ tailWord_8066015) baseStart_8066015 baseEnd_8066015 := by
    simpa [prefixWord, tailWord_8066015, baseEnd_8066015] using wordTrace_append hprefix tailTrace_8066015
  have hstable : (prefixWord ++ tailWord_8066015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066015).length < 2 ^ (prefixWord ++ tailWord_8066015).sum := by decide
  have hdescent : baseEnd_8066015 < baseStart_8066015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066040 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_8066040 : Nat := 118140960795 + 8066040 * 2 ^ 59
def prefixEnd_8066040 : Nat := 4983230072969 + 3 ^ 40 * 8066040 * 2
def baseEnd_8066040 : Nat := 4141755498391726815104963

theorem tailTrace_8066040 : CollatzResearch.WordTrace tailWord_8066040 prefixEnd_8066040 4141755498391726815104963 := by
  unfold tailWord_8066040
  simp only [CollatzResearch.WordTrace]
  refine ⟨147096323849061062401581787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196128431798748083202109049 147096323849061062401581787)
  ·
    refine ⟨220644485773591593602372681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147096323849061062401581787 220644485773591593602372681)
    ·
      refine ⟨165483364330193695201779511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220644485773591593602372681 165483364330193695201779511)
      ·
        refine ⟨248225046495290542802669267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165483364330193695201779511 248225046495290542802669267)
        ·
          refine ⟨372337569742935814204003901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248225046495290542802669267 372337569742935814204003901)
          ·
            refine ⟨139626588653600930326501463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372337569742935814204003901 139626588653600930326501463)
            ·
              refine ⟨209439882980401395489752195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139626588653600930326501463 209439882980401395489752195)
              ·
                refine ⟨314159824470602093234628293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209439882980401395489752195 314159824470602093234628293)
                ·
                  refine ⟨58904967088237892481492805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314159824470602093234628293 58904967088237892481492805)
                  ·
                    refine ⟨11044681329044604840279901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58904967088237892481492805 11044681329044604840279901)
                    ·
                      refine ⟨4141755498391726815104963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11044681329044604840279901 4141755498391726815104963)
                      ·
                        rfl

theorem cell23_8066040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_8066040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066040 prefixEnd_8066040 := by exact prefixLift 8066040
  have htrace : WordTrace (prefixWord ++ tailWord_8066040) baseStart_8066040 baseEnd_8066040 := by
    simpa [prefixWord, tailWord_8066040, baseEnd_8066040] using wordTrace_append hprefix tailTrace_8066040
  have hstable : (prefixWord ++ tailWord_8066040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066040).length < 2 ^ (prefixWord ++ tailWord_8066040).sum := by decide
  have hdescent : baseEnd_8066040 < baseStart_8066040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066058 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_8066058 : Nat := 118140960795 + 8066058 * 2 ^ 59
def prefixEnd_8066058 : Nat := 4983230072969 + 3 ^ 40 * 8066058 * 2
def baseEnd_8066058 : Nat := 4141764741043507744679881

theorem tailTrace_8066058 : CollatzResearch.WordTrace tailWord_8066058 prefixEnd_8066058 4141764741043507744679881 := by
  unfold tailWord_8066058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73548326053014228469329707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196128869474704609251545885 73548326053014228469329707)
  ·
    refine ⟨110322489079521342703994561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73548326053014228469329707 110322489079521342703994561)
    ·
      refine ⟨82741866809641007027995921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110322489079521342703994561 82741866809641007027995921)
      ·
        refine ⟨62056400107230755270996941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82741866809641007027995921 62056400107230755270996941)
        ·
          refine ⟨23271150040211533226623853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62056400107230755270996941 23271150040211533226623853)
          ·
            refine ⟨8726681265079324959983945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23271150040211533226623853 8726681265079324959983945)
            ·
              refine ⟨6545010948809493719987959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726681265079324959983945 6545010948809493719987959)
              ·
                refine ⟨9817516423214240579981939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545010948809493719987959 9817516423214240579981939)
                ·
                  refine ⟨14726274634821360869972909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817516423214240579981939 14726274634821360869972909)
                  ·
                    refine ⟨5522352988058010326239841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14726274634821360869972909 5522352988058010326239841)
                    ·
                      refine ⟨4141764741043507744679881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522352988058010326239841 4141764741043507744679881)
                      ·
                        rfl

theorem cell23_8066058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_8066058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066058 prefixEnd_8066058 := by exact prefixLift 8066058
  have htrace : WordTrace (prefixWord ++ tailWord_8066058) baseStart_8066058 baseEnd_8066058 := by
    simpa [prefixWord, tailWord_8066058, baseEnd_8066058] using wordTrace_append hprefix tailTrace_8066058
  have hstable : (prefixWord ++ tailWord_8066058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066058).length < 2 ^ (prefixWord ++ tailWord_8066058).sum := by decide
  have hdescent : baseEnd_8066058 < baseStart_8066058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066071 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 4, 2, 2]
def baseStart_8066071 : Nat := 118140960795 + 8066071 * 2 ^ 59
def prefixEnd_8066071 : Nat := 4983230072969 + 3 ^ 40 * 8066071 * 2
def baseEnd_8066071 : Nat := 4141771416292016193817321

theorem tailTrace_8066071 : CollatzResearch.WordTrace tailWord_8066071 prefixEnd_8066071 4141771416292016193817321 := by
  unfold tailWord_8066071
  simp only [CollatzResearch.WordTrace]
  refine ⟨294193778361009817097542067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196129185574006544731694711 294193778361009817097542067)
  ·
    refine ⟨441290667541514725646313101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294193778361009817097542067 441290667541514725646313101)
    ·
      refine ⟨165484000328068022117367413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441290667541514725646313101 165484000328068022117367413)
      ·
        refine ⟨15514125030756377073503195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165484000328068022117367413 15514125030756377073503195)
        ·
          refine ⟨23271187546134565610254793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514125030756377073503195 23271187546134565610254793)
          ·
            refine ⟨17453390659600924207691095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23271187546134565610254793 17453390659600924207691095)
            ·
              refine ⟨26180085989401386311536643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453390659600924207691095 26180085989401386311536643)
              ·
                refine ⟨39270128984102079467304965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26180085989401386311536643 39270128984102079467304965)
                ·
                  refine ⟨7363149184519139900119681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39270128984102079467304965 7363149184519139900119681)
                  ·
                    refine ⟨5522361888389354925089761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7363149184519139900119681 5522361888389354925089761)
                    ·
                      refine ⟨4141771416292016193817321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522361888389354925089761 4141771416292016193817321)
                      ·
                        rfl

theorem cell23_8066071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_8066071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066071 prefixEnd_8066071 := by exact prefixLift 8066071
  have htrace : WordTrace (prefixWord ++ tailWord_8066071) baseStart_8066071 baseEnd_8066071 := by
    simpa [prefixWord, tailWord_8066071, baseEnd_8066071] using wordTrace_append hprefix tailTrace_8066071
  have hstable : (prefixWord ++ tailWord_8066071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066071).length < 2 ^ (prefixWord ++ tailWord_8066071).sum := by decide
  have hdescent : baseEnd_8066071 < baseStart_8066071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066137 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 3, 4]
def baseStart_8066137 : Nat := 118140960795 + 8066137 * 2 ^ 59
def prefixEnd_8066137 : Nat := 4983230072969 + 3 ^ 40 * 8066137 * 2
def baseEnd_8066137 : Nat := 1380601768671737645197339

theorem tailTrace_8066137 : CollatzResearch.WordTrace tailWord_8066137 prefixEnd_8066137 1380601768671737645197339 := by
  unfold tailWord_8066137
  simp only [CollatzResearch.WordTrace]
  refine ⟨294196185578770710369444665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196130790385847140246296443 294196185578770710369444665)
  ·
    refine ⟨220647139184078032777083499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294196185578770710369444665 220647139184078032777083499)
    ·
      refine ⟨330970708776117049165625249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220647139184078032777083499 330970708776117049165625249)
      ·
        refine ⟨248228031582087786874218937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330970708776117049165625249 248228031582087786874218937)
        ·
          refine ⟨186171023686565840155664203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248228031582087786874218937 186171023686565840155664203)
          ·
            refine ⟨279256535529848760233496305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186171023686565840155664203 279256535529848760233496305)
            ·
              refine ⟨209442401647386570175122229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279256535529848760233496305 209442401647386570175122229)
              ·
                refine ⟨19635225154442490953917709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209442401647386570175122229 19635225154442490953917709)
                ·
                  refine ⟨7363209432915934107719141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19635225154442490953917709 7363209432915934107719141)
                  ·
                    refine ⟨1380601768671737645197339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7363209432915934107719141 1380601768671737645197339)
                    ·
                      rfl

theorem cell23_8066137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_8066137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066137 prefixEnd_8066137 := by exact prefixLift 8066137
  have htrace : WordTrace (prefixWord ++ tailWord_8066137) baseStart_8066137 baseEnd_8066137 := by
    simpa [prefixWord, tailWord_8066137, baseEnd_8066137] using wordTrace_append hprefix tailTrace_8066137
  have hstable : (prefixWord ++ tailWord_8066137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066137).length < 2 ^ (prefixWord ++ tailWord_8066137).sum := by decide
  have hdescent : baseEnd_8066137 < baseStart_8066137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066147 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 3]
def baseStart_8066147 : Nat := 118140960795 + 8066147 * 2 ^ 59
def prefixEnd_8066147 : Nat := 4983230072969 + 3 ^ 40 * 8066147 * 2
def baseEnd_8066147 : Nat := 4141810440821757896466971

theorem tailTrace_8066147 : CollatzResearch.WordTrace tailWord_8066147 prefixEnd_8066147 4141810440821757896466971 := by
  unfold tailWord_8066147
  simp only [CollatzResearch.WordTrace]
  refine ⟨294196550308734482077308695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196131033539156321384872463 294196550308734482077308695)
  ·
    refine ⟨441294825463101723115963043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294196550308734482077308695 441294825463101723115963043)
    ·
      refine ⟨661942238194652584673944565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441294825463101723115963043 661942238194652584673944565)
      ·
        refine ⟨62057084830748679813182303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 661942238194652584673944565 62057084830748679813182303)
        ·
          refine ⟨93085627246123019719773455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62057084830748679813182303 93085627246123019719773455)
          ·
            refine ⟨139628440869184529579660183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93085627246123019719773455 139628440869184529579660183)
            ·
              refine ⟨209442661303776794369490275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139628440869184529579660183 209442661303776794369490275)
              ·
                refine ⟨314163991955665191554235413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209442661303776794369490275 314163991955665191554235413)
                ·
                  refine ⟨14726437122921805854104785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 314163991955665191554235413 14726437122921805854104785)
                  ·
                    refine ⟨11044827842191354390578589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14726437122921805854104785 11044827842191354390578589)
                    ·
                      refine ⟨4141810440821757896466971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11044827842191354390578589 4141810440821757896466971)
                      ·
                        rfl

theorem cell23_8066147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_8066147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066147 prefixEnd_8066147 := by exact prefixLift 8066147
  have htrace : WordTrace (prefixWord ++ tailWord_8066147) baseStart_8066147 baseEnd_8066147 := by
    simpa [prefixWord, tailWord_8066147, baseEnd_8066147] using wordTrace_append hprefix tailTrace_8066147
  have hstable : (prefixWord ++ tailWord_8066147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066147).length < 2 ^ (prefixWord ++ tailWord_8066147).sum := by decide
  have hdescent : baseEnd_8066147 < baseStart_8066147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066227 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 1, 6]
def baseStart_8066227 : Nat := 118140960795 + 8066227 * 2 ^ 59
def prefixEnd_8066227 : Nat := 4983230072969 + 3 ^ 40 * 8066227 * 2
def baseEnd_8066227 : Nat := 1380617173091372527822201

theorem tailTrace_8066227 : CollatzResearch.WordTrace tailWord_8066227 prefixEnd_8066227 1380617173091372527822201 := by
  unfold tailWord_8066227
  simp only [CollatzResearch.WordTrace]
  refine ⟨294199468148444655740220935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196132978765629770493480623 294199468148444655740220935)
  ·
    refine ⟨441299202222666983610331403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294199468148444655740220935 441299202222666983610331403)
    ·
      refine ⟨661948803334000475415497105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441299202222666983610331403 661948803334000475415497105)
      ·
        refine ⟨496461602500500356561622829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661948803334000475415497105 496461602500500356561622829)
        ·
          refine ⟨186173100937687633710608561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496461602500500356561622829 186173100937687633710608561)
          ·
            refine ⟨139629825703265725282956421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186173100937687633710608561 139629825703265725282956421)
            ·
              refine ⟨26180592319362323490554329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139629825703265725282956421 26180592319362323490554329)
              ·
                refine ⟨19635444239521742617915747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26180592319362323490554329 19635444239521742617915747)
                ·
                  refine ⟨29453166359282613926873621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19635444239521742617915747 29453166359282613926873621)
                  ·
                    refine ⟨1380617173091372527822201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29453166359282613926873621 1380617173091372527822201)
                    ·
                      rfl

theorem cell23_8066227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 6].length) (baseStart_8066227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066227 prefixEnd_8066227 := by exact prefixLift 8066227
  have htrace : WordTrace (prefixWord ++ tailWord_8066227) baseStart_8066227 baseEnd_8066227 := by
    simpa [prefixWord, tailWord_8066227, baseEnd_8066227] using wordTrace_append hprefix tailTrace_8066227
  have hstable : (prefixWord ++ tailWord_8066227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066227).length < 2 ^ (prefixWord ++ tailWord_8066227).sum := by decide
  have hdescent : baseEnd_8066227 < baseStart_8066227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066247 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_8066247 : Nat := 118140960795 + 8066247 * 2 ^ 59
def prefixEnd_8066247 : Nat := 4983230072969 + 3 ^ 40 * 8066247 * 2
def baseEnd_8066247 : Nat := 4141861788887207505216511

theorem tailTrace_8066247 : CollatzResearch.WordTrace tailWord_8066247 prefixEnd_8066247 4141861788887207505216511 := by
  unfold tailWord_8066247
  simp only [CollatzResearch.WordTrace]
  refine ⟨294200197608372199155948995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196133465072248132770632663 294200197608372199155948995)
  ·
    refine ⟨441300296412558298733923493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294200197608372199155948995 441300296412558298733923493)
    ·
      refine ⟨82743805577354681012610655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441300296412558298733923493 82743805577354681012610655)
      ·
        refine ⟨124115708366032021518915983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82743805577354681012610655 124115708366032021518915983)
        ·
          refine ⟨186173562549048032278373975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124115708366032021518915983 186173562549048032278373975)
          ·
            refine ⟨279260343823572048417560963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186173562549048032278373975 279260343823572048417560963)
            ·
              refine ⟨418890515735358072626341445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279260343823572048417560963 418890515735358072626341445)
              ·
                refine ⟨78541971700379638617439021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418890515735358072626341445 78541971700379638617439021)
                ·
                  refine ⟨29453239387642364481539633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78541971700379638617439021 29453239387642364481539633)
                  ·
                    refine ⟨22089929540731773361154725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29453239387642364481539633 22089929540731773361154725)
                    ·
                      refine ⟨4141861788887207505216511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22089929540731773361154725 4141861788887207505216511)
                      ·
                        rfl

theorem cell23_8066247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_8066247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066247 prefixEnd_8066247 := by exact prefixLift 8066247
  have htrace : WordTrace (prefixWord ++ tailWord_8066247) baseStart_8066247 baseEnd_8066247 := by
    simpa [prefixWord, tailWord_8066247, baseEnd_8066247] using wordTrace_append hprefix tailTrace_8066247
  have hstable : (prefixWord ++ tailWord_8066247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066247).length < 2 ^ (prefixWord ++ tailWord_8066247).sum := by decide
  have hdescent : baseEnd_8066247 < baseStart_8066247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066261 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_8066261 : Nat := 118140960795 + 8066261 * 2 ^ 59
def prefixEnd_8066261 : Nat := 4983230072969 + 3 ^ 40 * 8066261 * 2
def baseEnd_8066261 : Nat := 1380622992538790150147149

theorem tailTrace_8066261 : CollatzResearch.WordTrace tailWord_8066261 prefixEnd_8066261 1380622992538790150147149 := by
  unfold tailWord_8066261
  simp only [CollatzResearch.WordTrace]
  refine ⟨294200708230321479546958637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196133805486880986364639091 294200708230321479546958637)
  ·
    refine ⟨110325265586370554830109489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294200708230321479546958637 110325265586370554830109489)
    ·
      refine ⟨82743949189777916122582117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110325265586370554830109489 82743949189777916122582117)
      ·
        refine ⟨15514490473083359272984147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82743949189777916122582117 15514490473083359272984147)
        ·
          refine ⟨23271735709625038909476221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514490473083359272984147 23271735709625038909476221)
          ·
            refine ⟨8726900891109389591053583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23271735709625038909476221 8726900891109389591053583)
            ·
              refine ⟨13090351336664084386580375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726900891109389591053583 13090351336664084386580375)
              ·
                refine ⟨19635527004996126579870563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13090351336664084386580375 19635527004996126579870563)
                ·
                  refine ⟨29453290507494189869805845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19635527004996126579870563 29453290507494189869805845)
                  ·
                    refine ⟨1380622992538790150147149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29453290507494189869805845 1380622992538790150147149)
                    ·
                      rfl

theorem cell23_8066261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_8066261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066261 prefixEnd_8066261 := by exact prefixLift 8066261
  have htrace : WordTrace (prefixWord ++ tailWord_8066261) baseStart_8066261 baseEnd_8066261 := by
    simpa [prefixWord, tailWord_8066261, baseEnd_8066261] using wordTrace_append hprefix tailTrace_8066261
  have hstable : (prefixWord ++ tailWord_8066261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066261).length < 2 ^ (prefixWord ++ tailWord_8066261).sum := by decide
  have hdescent : baseEnd_8066261 < baseStart_8066261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066264 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_8066264 : Nat := 118140960795 + 8066264 * 2 ^ 59
def prefixEnd_8066264 : Nat := 4983230072969 + 3 ^ 40 * 8066264 * 2
def baseEnd_8066264 : Nat := 4141870518058333938703933

theorem tailTrace_8066264 : CollatzResearch.WordTrace tailWord_8066264 prefixEnd_8066264 4141870518058333938703933 := by
  unfold tailWord_8066264
  simp only [CollatzResearch.WordTrace]
  refine ⟨147100408824655305529658923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196133878432873740706211897 147100408824655305529658923)
  ·
    refine ⟨220650613236982958294488385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147100408824655305529658923 220650613236982958294488385)
    ·
      refine ⟨165487959927737218720866289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220650613236982958294488385 165487959927737218720866289)
      ·
        refine ⟨124115969945802914040649717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165487959927737218720866289 124115969945802914040649717)
        ·
          refine ⟨11635872182419023191310911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124115969945802914040649717 11635872182419023191310911)
          ·
            refine ⟨17453808273628534786966367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635872182419023191310911 17453808273628534786966367)
            ·
              refine ⟨26180712410442802180449551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453808273628534786966367 26180712410442802180449551)
              ·
                refine ⟨39271068615664203270674327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26180712410442802180449551 39271068615664203270674327)
                ·
                  refine ⟨58906602923496304906011491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39271068615664203270674327 58906602923496304906011491)
                  ·
                    refine ⟨88359904385244457359017237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58906602923496304906011491 88359904385244457359017237)
                    ·
                      refine ⟨4141870518058333938703933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88359904385244457359017237 4141870518058333938703933)
                      ·
                        rfl

theorem cell23_8066264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_8066264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066264 prefixEnd_8066264 := by exact prefixLift 8066264
  have htrace : WordTrace (prefixWord ++ tailWord_8066264) baseStart_8066264 baseEnd_8066264 := by
    simpa [prefixWord, tailWord_8066264, baseEnd_8066264] using wordTrace_append hprefix tailTrace_8066264
  have hstable : (prefixWord ++ tailWord_8066264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066264).length < 2 ^ (prefixWord ++ tailWord_8066264).sum := by decide
  have hdescent : baseEnd_8066264 < baseStart_8066264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066297 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_8066297 : Nat := 118140960795 + 8066297 * 2 ^ 59
def prefixEnd_8066297 : Nat := 4983230072969 + 3 ^ 40 * 8066297 * 2
def baseEnd_8066297 : Nat := 4141887462919932309591281

theorem tailTrace_8066297 : CollatzResearch.WordTrace tailWord_8066297 prefixEnd_8066297 4141887462919932309591281 := by
  unfold tailWord_8066297
  simp only [CollatzResearch.WordTrace]
  refine ⟨294202021258191057695269145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196134680838794038463512763 294202021258191057695269145)
  ·
    refine ⟨220651515943643293271451859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294202021258191057695269145 220651515943643293271451859)
    ·
      refine ⟨330977273915464939907177789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220651515943643293271451859 330977273915464939907177789)
      ·
        refine ⟨124116477718299352465191671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330977273915464939907177789 124116477718299352465191671)
        ·
          refine ⟨186174716577449028697787507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124116477718299352465191671 186174716577449028697787507)
          ·
            refine ⟨279262074866173543046681261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186174716577449028697787507 279262074866173543046681261)
            ·
              refine ⟨104723278074815078642505473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279262074866173543046681261 104723278074815078642505473)
              ·
                refine ⟨78542458556111308981879105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104723278074815078642505473 78542458556111308981879105)
                ·
                  refine ⟨58906843917083481736409329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78542458556111308981879105 58906843917083481736409329)
                  ·
                    refine ⟨44180132937812611302306997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58906843917083481736409329 44180132937812611302306997)
                    ·
                      refine ⟨4141887462919932309591281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44180132937812611302306997 4141887462919932309591281)
                      ·
                        rfl

theorem cell23_8066297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_8066297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066297 prefixEnd_8066297 := by exact prefixLift 8066297
  have htrace : WordTrace (prefixWord ++ tailWord_8066297) baseStart_8066297 baseEnd_8066297 := by
    simpa [prefixWord, tailWord_8066297, baseEnd_8066297] using wordTrace_append hprefix tailTrace_8066297
  have hstable : (prefixWord ++ tailWord_8066297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066297).length < 2 ^ (prefixWord ++ tailWord_8066297).sum := by decide
  have hdescent : baseEnd_8066297 < baseStart_8066297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066318 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_8066318 : Nat := 118140960795 + 8066318 * 2 ^ 59
def prefixEnd_8066318 : Nat := 4983230072969 + 3 ^ 40 * 8066318 * 2
def baseEnd_8066318 : Nat := 4141898246013676727428685

theorem tailTrace_8066318 : CollatzResearch.WordTrace tailWord_8066318 prefixEnd_8066318 4141898246013676727428685 := by
  unfold tailWord_8066318
  simp only [CollatzResearch.WordTrace]
  refine ⟨36775348398889372285222951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196135191460743318854522405 36775348398889372285222951)
  ·
    refine ⟨55163022598334058427834427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36775348398889372285222951 55163022598334058427834427)
    ·
      refine ⟨82744533897501087641751641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55163022598334058427834427 82744533897501087641751641)
      ·
        refine ⟨62058400423125815731313731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82744533897501087641751641 62058400423125815731313731)
        ·
          refine ⟨93087600634688723596970597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62058400423125815731313731 93087600634688723596970597)
          ·
            refine ⟨17453925119004135674431987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93087600634688723596970597 17453925119004135674431987)
            ·
              refine ⟨26180887678506203511647981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453925119004135674431987 26180887678506203511647981)
              ·
                refine ⟨9817832879439826316867993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26180887678506203511647981 9817832879439826316867993)
                ·
                  refine ⟨7363374659579869737650995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9817832879439826316867993 7363374659579869737650995)
                  ·
                    refine ⟨11045061989369804606476493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7363374659579869737650995 11045061989369804606476493)
                    ·
                      refine ⟨4141898246013676727428685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11045061989369804606476493 4141898246013676727428685)
                      ·
                        rfl

theorem cell23_8066318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_8066318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066318 prefixEnd_8066318 := by exact prefixLift 8066318
  have htrace : WordTrace (prefixWord ++ tailWord_8066318) baseStart_8066318 baseEnd_8066318 := by
    simpa [prefixWord, tailWord_8066318, baseEnd_8066318] using wordTrace_append hprefix tailTrace_8066318
  have hstable : (prefixWord ++ tailWord_8066318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066318).length < 2 ^ (prefixWord ++ tailWord_8066318).sum := by decide
  have hdescent : baseEnd_8066318 < baseStart_8066318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066322 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_8066322 : Nat := 118140960795 + 8066322 * 2 ^ 59
def prefixEnd_8066322 : Nat := 4983230072969 + 3 ^ 40 * 8066322 * 2
def baseEnd_8066322 : Nat := 4141900299936294711778667

theorem tailTrace_8066322 : CollatzResearch.WordTrace tailWord_8066322 prefixEnd_8066322 4141900299936294711778667 := by
  unfold tailWord_8066322
  simp only [CollatzResearch.WordTrace]
  refine ⟨73550733270775121741232305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196135288722066991309952813 73550733270775121741232305)
  ·
    refine ⟨55163049953081341305924229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73550733270775121741232305 55163049953081341305924229)
    ·
      refine ⟨10343071866202751494860793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55163049953081341305924229 10343071866202751494860793)
      ·
        refine ⟨7757303899652063621145595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10343071866202751494860793 7757303899652063621145595)
        ·
          refine ⟨11635955849478095431718393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757303899652063621145595 11635955849478095431718393)
          ·
            refine ⟨8726966887108571573788795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11635955849478095431718393 8726966887108571573788795)
            ·
              refine ⟨13090450330662857360683193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726966887108571573788795 13090450330662857360683193)
              ·
                refine ⟨9817837747997143020512395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13090450330662857360683193 9817837747997143020512395)
                ·
                  refine ⟨14726756621995714530768593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817837747997143020512395 14726756621995714530768593)
                  ·
                    refine ⟨11045067466496785898076445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14726756621995714530768593 11045067466496785898076445)
                    ·
                      refine ⟨4141900299936294711778667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11045067466496785898076445 4141900299936294711778667)
                      ·
                        rfl

theorem cell23_8066322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_8066322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066322 prefixEnd_8066322 := by exact prefixLift 8066322
  have htrace : WordTrace (prefixWord ++ tailWord_8066322) baseStart_8066322 baseEnd_8066322 := by
    simpa [prefixWord, tailWord_8066322, baseEnd_8066322] using wordTrace_append hprefix tailTrace_8066322
  have hstable : (prefixWord ++ tailWord_8066322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066322).length < 2 ^ (prefixWord ++ tailWord_8066322).sum := by decide
  have hdescent : baseEnd_8066322 < baseStart_8066322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066328 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 1, 3, 2]
def baseStart_8066328 : Nat := 118140960795 + 8066328 * 2 ^ 59
def prefixEnd_8066328 : Nat := 4983230072969 + 3 ^ 40 * 8066328 * 2
def baseEnd_8066328 : Nat := 4141903380820221688303639

theorem tailTrace_8066328 : CollatzResearch.WordTrace tailWord_8066328 prefixEnd_8066328 4141903380820221688303639 := by
  unfold tailWord_8066328
  simp only [CollatzResearch.WordTrace]
  refine ⟨147101575960539374994823819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196135434614052499993098425 147101575960539374994823819)
  ·
    refine ⟨220652363940809062492235729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147101575960539374994823819 220652363940809062492235729)
    ·
      refine ⟨165489272955606796869176797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220652363940809062492235729 165489272955606796869176797)
      ·
        refine ⟨62058477358352548825941299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165489272955606796869176797 62058477358352548825941299)
        ·
          refine ⟨93087716037528823238911949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62058477358352548825941299 93087716037528823238911949)
          ·
            refine ⟨34907893514073308714591981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93087716037528823238911949 34907893514073308714591981)
            ·
              refine ⟨13090460067777490767971993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34907893514073308714591981 13090460067777490767971993)
              ·
                refine ⟨9817845050833118075978995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13090460067777490767971993 9817845050833118075978995)
                ·
                  refine ⟨14726767576249677113968493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817845050833118075978995 14726767576249677113968493)
                  ·
                    refine ⟨5522537841093628917738185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14726767576249677113968493 5522537841093628917738185)
                    ·
                      refine ⟨4141903380820221688303639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522537841093628917738185 4141903380820221688303639)
                      ·
                        rfl

theorem cell23_8066328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_8066328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066328 prefixEnd_8066328 := by exact prefixLift 8066328
  have htrace : WordTrace (prefixWord ++ tailWord_8066328) baseStart_8066328 baseEnd_8066328 := by
    simpa [prefixWord, tailWord_8066328, baseEnd_8066328] using wordTrace_append hprefix tailTrace_8066328
  have hstable : (prefixWord ++ tailWord_8066328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066328).length < 2 ^ (prefixWord ++ tailWord_8066328).sum := by decide
  have hdescent : baseEnd_8066328 < baseStart_8066328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066341 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 3, 4, 2]
def baseStart_8066341 : Nat := 118140960795 + 8066341 * 2 ^ 59
def prefixEnd_8066341 : Nat := 4983230072969 + 3 ^ 40 * 8066341 * 2
def baseEnd_8066341 : Nat := 4141910056068730137441079

theorem tailTrace_8066341 : CollatzResearch.WordTrace tailWord_8066341 prefixEnd_8066341 4141910056068730137441079 := by
  unfold tailWord_8066341
  simp only [CollatzResearch.WordTrace]
  refine ⟨294203626070031653209870877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196135750713354435473247251 294203626070031653209870877)
  ·
    refine ⟨110326359776261869953701579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294203626070031653209870877 110326359776261869953701579)
    ·
      refine ⟨165489539664392804930552369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110326359776261869953701579 165489539664392804930552369)
      ·
        refine ⟨124117154748294603697914277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165489539664392804930552369 124117154748294603697914277)
        ·
          refine ⟨23271966515305238193358927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124117154748294603697914277 23271966515305238193358927)
          ·
            refine ⟨34907949772957857290038391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23271966515305238193358927 34907949772957857290038391)
            ·
              refine ⟨52361924659436785935057587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34907949772957857290038391 52361924659436785935057587)
              ·
                refine ⟨78542886989155178902586381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52361924659436785935057587 78542886989155178902586381)
                ·
                  refine ⟨29453582620933192088469893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78542886989155178902586381 29453582620933192088469893)
                  ·
                    refine ⟨5522546741424973516588105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29453582620933192088469893 5522546741424973516588105)
                    ·
                      refine ⟨4141910056068730137441079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522546741424973516588105 4141910056068730137441079)
                      ·
                        rfl

theorem cell23_8066341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_8066341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066341 prefixEnd_8066341 := by exact prefixLift 8066341
  have htrace : WordTrace (prefixWord ++ tailWord_8066341) baseStart_8066341 baseEnd_8066341 := by
    simpa [prefixWord, tailWord_8066341, baseEnd_8066341] using wordTrace_append hprefix tailTrace_8066341
  have hstable : (prefixWord ++ tailWord_8066341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066341).length < 2 ^ (prefixWord ++ tailWord_8066341).sum := by decide
  have hdescent : baseEnd_8066341 < baseStart_8066341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066444 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_8066444 : Nat := 118140960795 + 8066444 * 2 ^ 59
def prefixEnd_8066444 : Nat := 4983230072969 + 3 ^ 40 * 8066444 * 2
def baseEnd_8066444 : Nat := 4141962944576143234453105

theorem tailTrace_8066444 : CollatzResearch.WordTrace tailWord_8066444 prefixEnd_8066444 4141962944576143234453105 := by
  unfold tailWord_8066444
  simp only [CollatzResearch.WordTrace]
  refine ⟨147103691394329250900435193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196138255192439001200580257 147103691394329250900435193)
  ·
    refine ⟨110327768545746938175326395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147103691394329250900435193 110327768545746938175326395)
    ·
      refine ⟨165491652818620407262989593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110327768545746938175326395 165491652818620407262989593)
      ·
        refine ⟨124118739613965305447242195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165491652818620407262989593 124118739613965305447242195)
        ·
          refine ⟨186178109420947958170863293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124118739613965305447242195 186178109420947958170863293)
          ·
            refine ⟨69816791032855484314073735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186178109420947958170863293 69816791032855484314073735)
            ·
              refine ⟨104725186549283226471110603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69816791032855484314073735 104725186549283226471110603)
              ·
                refine ⟨157087779823924839706665905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104725186549283226471110603 157087779823924839706665905)
                ·
                  refine ⟨117815834867943629779999429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157087779823924839706665905 117815834867943629779999429)
                  ·
                    refine ⟨22090469037739430583749893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117815834867943629779999429 22090469037739430583749893)
                    ·
                      refine ⟨4141962944576143234453105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22090469037739430583749893 4141962944576143234453105)
                      ·
                        rfl

theorem cell23_8066444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_8066444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066444 prefixEnd_8066444 := by exact prefixLift 8066444
  have htrace : WordTrace (prefixWord ++ tailWord_8066444) baseStart_8066444 baseEnd_8066444 := by
    simpa [prefixWord, tailWord_8066444, baseEnd_8066444] using wordTrace_append hprefix tailTrace_8066444
  have hstable : (prefixWord ++ tailWord_8066444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066444).length < 2 ^ (prefixWord ++ tailWord_8066444).sum := by decide
  have hdescent : baseEnd_8066444 < baseStart_8066444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066471 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 6]
def baseStart_8066471 : Nat := 118140960795 + 8066471 * 2 ^ 59
def prefixEnd_8066471 : Nat := 4983230072969 + 3 ^ 40 * 8066471 * 2
def baseEnd_8066471 : Nat := 460219645394868292090609

theorem tailTrace_8066471 : CollatzResearch.WordTrace tailWord_8066471 prefixEnd_8066471 460219645394868292090609 := by
  unfold tailWord_8066471
  simp only [CollatzResearch.WordTrace]
  refine ⟨294208367559560685412103267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196138911706373790274735511 294208367559560685412103267)
  ·
    refine ⟨441312551339341028118154901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294208367559560685412103267 441312551339341028118154901)
    ·
      refine ⟨20686525844031610693038511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 441312551339341028118154901 20686525844031610693038511)
      ·
        refine ⟨31029788766047416039557767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20686525844031610693038511 31029788766047416039557767)
        ·
          refine ⟨46544683149071124059336651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31029788766047416039557767 46544683149071124059336651)
          ·
            refine ⟨69817024723606686089004977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46544683149071124059336651 69817024723606686089004977)
            ·
              refine ⟨52362768542705014566753733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69817024723606686089004977 52362768542705014566753733)
              ·
                refine ⟨9818019101757190231266325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52362768542705014566753733 9818019101757190231266325)
                ·
                  refine ⟨460219645394868292090609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9818019101757190231266325 460219645394868292090609)
                  ·
                    rfl

theorem cell23_8066471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 6].length) (baseStart_8066471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066471 prefixEnd_8066471 := by exact prefixLift 8066471
  have htrace : WordTrace (prefixWord ++ tailWord_8066471) baseStart_8066471 baseEnd_8066471 := by
    simpa [prefixWord, tailWord_8066471, baseEnd_8066471] using wordTrace_append hprefix tailTrace_8066471
  have hstable : (prefixWord ++ tailWord_8066471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066471).length < 2 ^ (prefixWord ++ tailWord_8066471).sum := by decide
  have hdescent : baseEnd_8066471 < baseStart_8066471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066525 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_8066525 : Nat := 118140960795 + 8066525 * 2 ^ 59
def prefixEnd_8066525 : Nat := 4983230072969 + 3 ^ 40 * 8066525 * 2
def baseEnd_8066525 : Nat := 4142004536509157417540233

theorem tailTrace_8066525 : CollatzResearch.WordTrace tailWord_8066525 prefixEnd_8066525 4142004536509157417540233 := by
  unfold tailWord_8066525
  simp only [CollatzResearch.WordTrace]
  refine ⟨294210337101365052634569029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196140224734243368423046019 294210337101365052634569029)
  ·
    refine ⟨55164438206505947368981693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294210337101365052634569029 55164438206505947368981693)
    ·
      refine ⟨20686664327439730263368135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55164438206505947368981693 20686664327439730263368135)
      ·
        refine ⟨31029996491159595395052203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20686664327439730263368135 31029996491159595395052203)
        ·
          refine ⟨46544994736739393092578305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31029996491159595395052203 46544994736739393092578305)
          ·
            refine ⟨34908746052554544819433729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46544994736739393092578305 34908746052554544819433729)
            ·
              refine ⟨26181559539415908614575297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34908746052554544819433729 26181559539415908614575297)
              ·
                refine ⟨19636169654561931460931473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26181559539415908614575297 19636169654561931460931473)
                ·
                  refine ⟨14727127240921448595698605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19636169654561931460931473 14727127240921448595698605)
                  ·
                    refine ⟨5522672715345543223386977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14727127240921448595698605 5522672715345543223386977)
                    ·
                      refine ⟨4142004536509157417540233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522672715345543223386977 4142004536509157417540233)
                      ·
                        rfl

theorem cell23_8066525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_8066525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066525 prefixEnd_8066525 := by exact prefixLift 8066525
  have htrace : WordTrace (prefixWord ++ tailWord_8066525) baseStart_8066525 baseEnd_8066525 := by
    simpa [prefixWord, tailWord_8066525, baseEnd_8066525] using wordTrace_append hprefix tailTrace_8066525
  have hstable : (prefixWord ++ tailWord_8066525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066525).length < 2 ^ (prefixWord ++ tailWord_8066525).sum := by decide
  have hdescent : baseEnd_8066525 < baseStart_8066525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066572 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 1, 1, 4]
def baseStart_8066572 : Nat := 118140960795 + 8066572 * 2 ^ 59
def prefixEnd_8066572 : Nat := 4983230072969 + 3 ^ 40 * 8066572 * 2
def baseEnd_8066572 : Nat := 4142028670099918733652517

theorem tailTrace_8066572 : CollatzResearch.WordTrace tailWord_8066572 prefixEnd_8066572 4142028670099918733652517 := by
  unfold tailWord_8066572
  simp only [CollatzResearch.WordTrace]
  refine ⟨147106025666097389830764985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196141367554796519774353313 147106025666097389830764985)
  ·
    refine ⟨110329519249573042373073739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147106025666097389830764985 110329519249573042373073739)
    ·
      refine ⟨165494278874359563559610609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110329519249573042373073739 165494278874359563559610609)
      ·
        refine ⟨124120709155769672669707957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165494278874359563559610609 124120709155769672669707957)
        ·
          refine ⟨11636316483353406812785121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124120709155769672669707957 11636316483353406812785121)
          ·
            refine ⟨8727237362515055109588841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11636316483353406812785121 8727237362515055109588841)
            ·
              refine ⟨6545428021886291332191631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8727237362515055109588841 6545428021886291332191631)
              ·
                refine ⟨9818142032829436998287447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545428021886291332191631 9818142032829436998287447)
                ·
                  refine ⟨14727213049244155497431171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818142032829436998287447 14727213049244155497431171)
                  ·
                    refine ⟨22090819573866233246146757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14727213049244155497431171 22090819573866233246146757)
                    ·
                      refine ⟨4142028670099918733652517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22090819573866233246146757 4142028670099918733652517)
                      ·
                        rfl

theorem cell23_8066572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_8066572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066572 prefixEnd_8066572 := by exact prefixLift 8066572
  have htrace : WordTrace (prefixWord ++ tailWord_8066572) baseStart_8066572 baseEnd_8066572 := by
    simpa [prefixWord, tailWord_8066572, baseEnd_8066572] using wordTrace_append hprefix tailTrace_8066572
  have hstable : (prefixWord ++ tailWord_8066572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066572).length < 2 ^ (prefixWord ++ tailWord_8066572).sum := by decide
  have hdescent : baseEnd_8066572 < baseStart_8066572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066615 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 1, 3, 2]
def baseStart_8066615 : Nat := 118140960795 + 8066615 * 2 ^ 59
def prefixEnd_8066615 : Nat := 4983230072969 + 3 ^ 40 * 8066615 * 2
def baseEnd_8066615 : Nat := 4142050749768062065414819

theorem tailTrace_8066615 : CollatzResearch.WordTrace tailWord_8066615 prefixEnd_8066615 4142050749768062065414819 := by
  unfold tailWord_8066615
  simp only [CollatzResearch.WordTrace]
  refine ⟨294213619671038998005345299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196142413114025998670230199 294213619671038998005345299)
  ·
    refine ⟨441320429506558497008017949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294213619671038998005345299 441320429506558497008017949)
    ·
      refine ⟨165495161064959436378006731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441320429506558497008017949 165495161064959436378006731)
      ·
        refine ⟨248242741597439154567010097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165495161064959436378006731 248242741597439154567010097)
        ·
          refine ⟨186182056198079365925257573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248242741597439154567010097 186182056198079365925257573)
          ·
            refine ⟨34909135537139881110985795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186182056198079365925257573 34909135537139881110985795)
            ·
              refine ⟨52363703305709821666478693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34909135537139881110985795 52363703305709821666478693)
              ·
                refine ⟨9818194369820591562464755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52363703305709821666478693 9818194369820591562464755)
                ·
                  refine ⟨14727291554730887343697133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818194369820591562464755 14727291554730887343697133)
                  ·
                    refine ⟨5522734333024082753886425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14727291554730887343697133 5522734333024082753886425)
                    ·
                      refine ⟨4142050749768062065414819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522734333024082753886425 4142050749768062065414819)
                      ·
                        rfl

theorem cell23_8066615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_8066615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066615 prefixEnd_8066615 := by exact prefixLift 8066615
  have htrace : WordTrace (prefixWord ++ tailWord_8066615) baseStart_8066615 baseEnd_8066615 := by
    simpa [prefixWord, tailWord_8066615, baseEnd_8066615] using wordTrace_append hprefix tailTrace_8066615
  have hstable : (prefixWord ++ tailWord_8066615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066615).length < 2 ^ (prefixWord ++ tailWord_8066615).sum := by decide
  have hdescent : baseEnd_8066615 < baseStart_8066615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066696 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_8066696 : Nat := 118140960795 + 8066696 * 2 ^ 59
def prefixEnd_8066696 : Nat := 4983230072969 + 3 ^ 40 * 8066696 * 2
def baseEnd_8066696 : Nat := 4142092341701076248501947

theorem tailTrace_8066696 : CollatzResearch.WordTrace tailWord_8066696 prefixEnd_8066696 4142092341701076248501947 := by
  unfold tailWord_8066696
  simp only [CollatzResearch.WordTrace]
  refine ⟨147108286991872774419521971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196144382655830365892695961 147108286991872774419521971)
  ·
    refine ⟨220662430487809161629282957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147108286991872774419521971 220662430487809161629282957)
    ·
      refine ⟨82748411432928435610981109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220662430487809161629282957 82748411432928435610981109)
      ·
        refine ⟨7757663571837040838529479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82748411432928435610981109 7757663571837040838529479)
        ·
          refine ⟨11636495357755561257794219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757663571837040838529479 11636495357755561257794219)
          ·
            refine ⟨17454743036633341886691329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11636495357755561257794219 17454743036633341886691329)
            ·
              refine ⟨13091057277475006415018497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17454743036633341886691329 13091057277475006415018497)
              ·
                refine ⟨9818292958106254811263873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091057277475006415018497 9818292958106254811263873)
                ·
                  refine ⟨7363719718579691108447905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818292958106254811263873 7363719718579691108447905)
                  ·
                    refine ⟨5522789788934768331335929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7363719718579691108447905 5522789788934768331335929)
                    ·
                      refine ⟨4142092341701076248501947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522789788934768331335929 4142092341701076248501947)
                      ·
                        rfl

theorem cell23_8066696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_8066696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066696 prefixEnd_8066696 := by exact prefixLift 8066696
  have htrace : WordTrace (prefixWord ++ tailWord_8066696) baseStart_8066696 baseEnd_8066696 := by
    simpa [prefixWord, tailWord_8066696, baseEnd_8066696] using wordTrace_append hprefix tailTrace_8066696
  have hstable : (prefixWord ++ tailWord_8066696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066696).length < 2 ^ (prefixWord ++ tailWord_8066696).sum := by decide
  have hdescent : baseEnd_8066696 < baseStart_8066696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066702 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_8066702 : Nat := 118140960795 + 8066702 * 2 ^ 59
def prefixEnd_8066702 : Nat := 4983230072969 + 3 ^ 40 * 8066702 * 2
def baseEnd_8066702 : Nat := 460232824731667025002991

theorem tailTrace_8066702 : CollatzResearch.WordTrace tailWord_8066702 prefixEnd_8066702 460232824731667025002991 := by
  unfold tailWord_8066702
  simp only [CollatzResearch.WordTrace]
  refine ⟨36777099102715476482970295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196144528547815874575841573 36777099102715476482970295)
  ·
    refine ⟨55165648654073214724455443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36777099102715476482970295 55165648654073214724455443)
    ·
      refine ⟨82748472981109822086683165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55165648654073214724455443 82748472981109822086683165)
      ·
        refine ⟨31030677367916183282506187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82748472981109822086683165 31030677367916183282506187)
        ·
          refine ⟨46546016051874274923759281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31030677367916183282506187 46546016051874274923759281)
          ·
            refine ⟨34909512038905706192819461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46546016051874274923759281 34909512038905706192819461)
            ·
              refine ⟨6545533507294819911153649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34909512038905706192819461 6545533507294819911153649)
              ·
                refine ⟨4909150130471114933365237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545533507294819911153649 4909150130471114933365237)
                ·
                  refine ⟨460232824731667025002991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4909150130471114933365237 460232824731667025002991)
                  ·
                    rfl

theorem cell23_8066702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_8066702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066702 prefixEnd_8066702 := by exact prefixLift 8066702
  have htrace : WordTrace (prefixWord ++ tailWord_8066702) baseStart_8066702 baseEnd_8066702 := by
    simpa [prefixWord, tailWord_8066702, baseEnd_8066702] using wordTrace_append hprefix tailTrace_8066702
  have hstable : (prefixWord ++ tailWord_8066702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066702).length < 2 ^ (prefixWord ++ tailWord_8066702).sum := by decide
  have hdescent : baseEnd_8066702 < baseStart_8066702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066748 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_8066748 : Nat := 118140960795 + 8066748 * 2 ^ 59
def prefixEnd_8066748 : Nat := 4983230072969 + 3 ^ 40 * 8066748 * 2
def baseEnd_8066748 : Nat := 4142119042695110045051707

theorem tailTrace_8066748 : CollatzResearch.WordTrace tailWord_8066748 prefixEnd_8066748 4142119042695110045051707 := by
  unfold tailWord_8066748
  simp only [CollatzResearch.WordTrace]
  refine ⟨147109235289778580859968449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196145647053038107813291265 147109235289778580859968449)
  ·
    refine ⟨110331926467333935644976337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147109235289778580859968449 110331926467333935644976337)
    ·
      refine ⟨82748944850500451733732253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110331926467333935644976337 82748944850500451733732253)
      ·
        refine ⟨31030854318937669400149595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82748944850500451733732253 31030854318937669400149595)
        ·
          refine ⟨46546281478406504100224393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31030854318937669400149595 46546281478406504100224393)
          ·
            refine ⟨34909711108804878075168295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46546281478406504100224393 34909711108804878075168295)
            ·
              refine ⟨52364566663207317112752443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34909711108804878075168295 52364566663207317112752443)
              ·
                refine ⟨78546849994810975669128665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52364566663207317112752443 78546849994810975669128665)
                ·
                  refine ⟨58910137496108231751846499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78546849994810975669128665 58910137496108231751846499)
                  ·
                    refine ⟨88365206244162347627769749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58910137496108231751846499 88365206244162347627769749)
                    ·
                      refine ⟨4142119042695110045051707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88365206244162347627769749 4142119042695110045051707)
                      ·
                        rfl

theorem cell23_8066748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_8066748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066748 prefixEnd_8066748 := by exact prefixLift 8066748
  have htrace : WordTrace (prefixWord ++ tailWord_8066748) baseStart_8066748 baseEnd_8066748 := by
    simpa [prefixWord, tailWord_8066748, baseEnd_8066748] using wordTrace_append hprefix tailTrace_8066748
  have hstable : (prefixWord ++ tailWord_8066748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066748).length < 2 ^ (prefixWord ++ tailWord_8066748).sum := by decide
  have hdescent : baseEnd_8066748 < baseStart_8066748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066762 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_8066762 : Nat := 118140960795 + 8066762 * 2 ^ 59
def prefixEnd_8066762 : Nat := 4983230072969 + 3 ^ 40 * 8066762 * 2
def baseEnd_8066762 : Nat := 1380708743808090996758881

theorem tailTrace_8066762 : CollatzResearch.WordTrace tailWord_8066762 prefixEnd_8066762 1380708743808090996758881 := by
  unfold tailWord_8066762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73554745300376610527736635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196145987467670961407297693 73554745300376610527736635)
  ·
    refine ⟨110332117950564915791604953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73554745300376610527736635 110332117950564915791604953)
    ·
      refine ⟨82749088462923686843703715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110332117950564915791604953 82749088462923686843703715)
      ·
        refine ⟨124123632694385530265555573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82749088462923686843703715 124123632694385530265555573)
        ·
          refine ⟨11636590565098643462395835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124123632694385530265555573 11636590565098643462395835)
          ·
            refine ⟨17454885847647965193593753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11636590565098643462395835 17454885847647965193593753)
            ·
              refine ⟨13091164385735973895195315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17454885847647965193593753 13091164385735973895195315)
              ·
                refine ⟨19636746578603960842792973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13091164385735973895195315 19636746578603960842792973)
                ·
                  refine ⟨7363779966976485316047365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19636746578603960842792973 7363779966976485316047365)
                  ·
                    refine ⟨1380708743808090996758881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7363779966976485316047365 1380708743808090996758881)
                    ·
                      rfl

theorem cell23_8066762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_8066762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066762 prefixEnd_8066762 := by exact prefixLift 8066762
  have htrace : WordTrace (prefixWord ++ tailWord_8066762) baseStart_8066762 baseEnd_8066762 := by
    simpa [prefixWord, tailWord_8066762, baseEnd_8066762] using wordTrace_append hprefix tailTrace_8066762
  have hstable : (prefixWord ++ tailWord_8066762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066762).length < 2 ^ (prefixWord ++ tailWord_8066762).sum := by decide
  have hdescent : baseEnd_8066762 < baseStart_8066762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066775 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 6]
def baseStart_8066775 : Nat := 118140960795 + 8066775 * 2 ^ 59
def prefixEnd_8066775 : Nat := 4983230072969 + 3 ^ 40 * 8066775 * 2
def baseEnd_8066775 : Nat := 460236989630309048823787

theorem tailTrace_8066775 : CollatzResearch.WordTrace tailWord_8066775 prefixEnd_8066775 460236989630309048823787 := by
  unfold tailWord_8066775
  simp only [CollatzResearch.WordTrace]
  refine ⟨294219455350459345331169779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196146303566972896887446519 294219455350459345331169779)
  ·
    refine ⟨441329183025689017996754669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294219455350459345331169779 441329183025689017996754669)
    ·
      refine ⟨165498443634633381748783001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441329183025689017996754669 165498443634633381748783001)
      ·
        refine ⟨124123832725975036311587251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165498443634633381748783001 124123832725975036311587251)
        ·
          refine ⟨186185749088962554467380877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124123832725975036311587251 186185749088962554467380877)
          ·
            refine ⟨69819655908360957925267829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186185749088962554467380877 69819655908360957925267829)
            ·
              refine ⟨6545592741408839805493859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69819655908360957925267829 6545592741408839805493859)
              ·
                refine ⟨9818389112113259708240789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545592741408839805493859 9818389112113259708240789)
                ·
                  refine ⟨460236989630309048823787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9818389112113259708240789 460236989630309048823787)
                  ·
                    rfl

theorem cell23_8066775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 6].length) (baseStart_8066775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066775 prefixEnd_8066775 := by exact prefixLift 8066775
  have htrace : WordTrace (prefixWord ++ tailWord_8066775) baseStart_8066775 baseEnd_8066775 := by
    simpa [prefixWord, tailWord_8066775, baseEnd_8066775] using wordTrace_append hprefix tailTrace_8066775
  have hstable : (prefixWord ++ tailWord_8066775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066775).length < 2 ^ (prefixWord ++ tailWord_8066775).sum := by decide
  have hdescent : baseEnd_8066775 < baseStart_8066775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066795 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 1, 5, 2]
def baseStart_8066795 : Nat := 118140960795 + 8066795 * 2 ^ 59
def prefixEnd_8066795 : Nat := 4983230072969 + 3 ^ 40 * 8066795 * 2
def baseEnd_8066795 : Nat := 4142143176285871361163991

theorem tailTrace_8066795 : CollatzResearch.WordTrace tailWord_8066795 prefixEnd_8066795 4142143176285871361163991 := by
  unfold tailWord_8066795
  simp only [CollatzResearch.WordTrace]
  refine ⟨294220184810386888746897839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196146789873591259164598559 294220184810386888746897839)
  ·
    refine ⟨441330277215580333120346759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294220184810386888746897839 441330277215580333120346759)
    ·
      refine ⟨661995415823370499680520139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441330277215580333120346759 661995415823370499680520139)
      ·
        refine ⟨992993123735055749520780209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661995415823370499680520139 992993123735055749520780209)
        ·
          refine ⟨744744842801291812140585157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992993123735055749520780209 744744842801291812140585157)
          ·
            refine ⟨139639658025242214776359717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 744744842801291812140585157 139639658025242214776359717)
            ·
              refine ⟨26182435879732915270567447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139639658025242214776359717 26182435879732915270567447)
              ·
                refine ⟨39273653819599372905851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26182435879732915270567447 39273653819599372905851171)
                ·
                  refine ⟨58910480729399059358776757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39273653819599372905851171 58910480729399059358776757)
                  ·
                    refine ⟨5522857568381161814885321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58910480729399059358776757 5522857568381161814885321)
                    ·
                      refine ⟨4142143176285871361163991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522857568381161814885321 4142143176285871361163991)
                      ·
                        rfl

theorem cell23_8066795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5, 2].length) (baseStart_8066795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066795 prefixEnd_8066795 := by exact prefixLift 8066795
  have htrace : WordTrace (prefixWord ++ tailWord_8066795) baseStart_8066795 baseEnd_8066795 := by
    simpa [prefixWord, tailWord_8066795, baseEnd_8066795] using wordTrace_append hprefix tailTrace_8066795
  have hstable : (prefixWord ++ tailWord_8066795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066795).length < 2 ^ (prefixWord ++ tailWord_8066795).sum := by decide
  have hdescent : baseEnd_8066795 < baseStart_8066795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066812 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_8066812 : Nat := 118140960795 + 8066812 * 2 ^ 59
def prefixEnd_8066812 : Nat := 4983230072969 + 3 ^ 40 * 8066812 * 2
def baseEnd_8066812 : Nat := 4142151905456997794651413

theorem tailTrace_8066812 : CollatzResearch.WordTrace tailWord_8066812 prefixEnd_8066812 4142151905456997794651413 := by
  unfold tailWord_8066812
  simp only [CollatzResearch.WordTrace]
  refine ⟨147110402425662650325133345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196147203234216867100177793 147110402425662650325133345)
  ·
    refine ⟨110332801819246987743850009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147110402425662650325133345 110332801819246987743850009)
    ·
      refine ⟨82749601364435240807887507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110332801819246987743850009 82749601364435240807887507)
      ·
        refine ⟨124124402046652861211831261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82749601364435240807887507 124124402046652861211831261)
        ·
          refine ⟨46546650767494822954436723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124124402046652861211831261 46546650767494822954436723)
          ·
            refine ⟨69819976151242234431655085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46546650767494822954436723 69819976151242234431655085)
            ·
              refine ⟨26182491056715837911870657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69819976151242234431655085 26182491056715837911870657)
              ·
                refine ⟨19636868292536878433902993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26182491056715837911870657 19636868292536878433902993)
                ·
                  refine ⟨14727651219402658825427245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19636868292536878433902993 14727651219402658825427245)
                  ·
                    refine ⟨5522869207275997059535217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14727651219402658825427245 5522869207275997059535217)
                    ·
                      refine ⟨4142151905456997794651413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522869207275997059535217 4142151905456997794651413)
                      ·
                        rfl

theorem cell23_8066812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_8066812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066812 prefixEnd_8066812 := by exact prefixLift 8066812
  have htrace : WordTrace (prefixWord ++ tailWord_8066812) baseStart_8066812 baseEnd_8066812 := by
    simpa [prefixWord, tailWord_8066812, baseEnd_8066812] using wordTrace_append hprefix tailTrace_8066812
  have hstable : (prefixWord ++ tailWord_8066812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066812).length < 2 ^ (prefixWord ++ tailWord_8066812).sum := by decide
  have hdescent : baseEnd_8066812 < baseStart_8066812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066842 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_8066842 : Nat := 118140960795 + 8066842 * 2 ^ 59
def prefixEnd_8066842 : Nat := 4983230072969 + 3 ^ 40 * 8066842 * 2
def baseEnd_8066842 : Nat := 4142167309876632677276275

theorem tailTrace_8066842 : CollatzResearch.WordTrace tailWord_8066842 prefixEnd_8066842 4142167309876632677276275 := by
  unfold tailWord_8066842
  simp only [CollatzResearch.WordTrace]
  refine ⟨73555474760304153943464695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196147932694144410515905853 73555474760304153943464695)
  ·
    refine ⟨110333212140456230915197043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73555474760304153943464695 110333212140456230915197043)
    ·
      refine ⟨165499818210684346372795565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110333212140456230915197043 165499818210684346372795565)
      ·
        refine ⟨62062431829006629889798337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165499818210684346372795565 62062431829006629889798337)
        ·
          refine ⟨46546823871754972417348753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62062431829006629889798337 46546823871754972417348753)
          ·
            refine ⟨34910117903816229313011565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46546823871754972417348753 34910117903816229313011565)
            ·
              refine ⟨13091294213931085992379337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34910117903816229313011565 13091294213931085992379337)
              ·
                refine ⟨9818470660448314494284503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091294213931085992379337 9818470660448314494284503)
                ·
                  refine ⟨14727705990672471741426755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818470660448314494284503 14727705990672471741426755)
                  ·
                    refine ⟨22091558986008707612140133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14727705990672471741426755 22091558986008707612140133)
                    ·
                      refine ⟨4142167309876632677276275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22091558986008707612140133 4142167309876632677276275)
                      ·
                        rfl

theorem cell23_8066842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_8066842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066842 prefixEnd_8066842 := by exact prefixLift 8066842
  have htrace : WordTrace (prefixWord ++ tailWord_8066842) baseStart_8066842 baseEnd_8066842 := by
    simpa [prefixWord, tailWord_8066842, baseEnd_8066842] using wordTrace_append hprefix tailTrace_8066842
  have hstable : (prefixWord ++ tailWord_8066842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066842).length < 2 ^ (prefixWord ++ tailWord_8066842).sum := by decide
  have hdescent : baseEnd_8066842 < baseStart_8066842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066848 : List Nat := [2, 1, 1, 5, 1, 1, 1, 11]
def baseStart_8066848 : Nat := 118140960795 + 8066848 * 2 ^ 59
def prefixEnd_8066848 : Nat := 4983230072969 + 3 ^ 40 * 8066848 * 2
def baseEnd_8066848 : Nat := 153413718176317024214861

theorem tailTrace_8066848 : CollatzResearch.WordTrace tailWord_8066848 prefixEnd_8066848 153413718176317024214861 := by
  unfold tailWord_8066848
  simp only [CollatzResearch.WordTrace]
  refine ⟨147111058939597439399288599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196148078586129919199051465 147111058939597439399288599)
  ·
    refine ⟨220666588409396159098932899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147111058939597439399288599 220666588409396159098932899)
    ·
      refine ⟨330999882614094238648399349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220666588409396159098932899 330999882614094238648399349)
      ·
        refine ⟨31031238995071334873287439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330999882614094238648399349 31031238995071334873287439)
        ·
          refine ⟨46546858492607002309931159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31031238995071334873287439 46546858492607002309931159)
          ·
            refine ⟨69820287738910503464896739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46546858492607002309931159 69820287738910503464896739)
            ·
              refine ⟨104730431608365755197345109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69820287738910503464896739 104730431608365755197345109)
              ·
                refine ⟨153413718176317024214861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 104730431608365755197345109 153413718176317024214861)
                ·
                  rfl

theorem cell23_8066848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 11].length) (baseStart_8066848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066848 prefixEnd_8066848 := by exact prefixLift 8066848
  have htrace : WordTrace (prefixWord ++ tailWord_8066848) baseStart_8066848 baseEnd_8066848 := by
    simpa [prefixWord, tailWord_8066848, baseEnd_8066848] using wordTrace_append hprefix tailTrace_8066848
  have hstable : (prefixWord ++ tailWord_8066848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066848).length < 2 ^ (prefixWord ++ tailWord_8066848).sum := by decide
  have hdescent : baseEnd_8066848 < baseStart_8066848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066869 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_8066869 : Nat := 118140960795 + 8066869 * 2 ^ 59
def prefixEnd_8066869 : Nat := 4983230072969 + 3 ^ 40 * 8066869 * 2
def baseEnd_8066869 : Nat := 1380727057951434690546217

theorem tailTrace_8066869 : CollatzResearch.WordTrace tailWord_8066869 prefixEnd_8066869 1380727057951434690546217 := by
  unfold tailWord_8066869
  simp only [CollatzResearch.WordTrace]
  refine ⟨294222883812118799385091661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196148589208079199590061107 294222883812118799385091661)
  ·
    refine ⟨110333581429544549769409373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294222883812118799385091661 110333581429544549769409373)
    ·
      refine ⟨41375093036079206163528515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110333581429544549769409373 41375093036079206163528515)
      ·
        refine ⟨62062639554118809245292773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41375093036079206163528515 62062639554118809245292773)
        ·
          refine ⟨11636744916397276733492395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62062639554118809245292773 11636744916397276733492395)
          ·
            refine ⟨17455117374595915100238593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11636744916397276733492395 17455117374595915100238593)
            ·
              refine ⟨13091338030946936325178945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17455117374595915100238593 13091338030946936325178945)
              ·
                refine ⟨9818503523210202243884209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091338030946936325178945 9818503523210202243884209)
                ·
                  refine ⟨7363877642407651682913157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818503523210202243884209 7363877642407651682913157)
                  ·
                    refine ⟨1380727057951434690546217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7363877642407651682913157 1380727057951434690546217)
                    ·
                      rfl

theorem cell23_8066869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_8066869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066869 prefixEnd_8066869 := by exact prefixLift 8066869
  have htrace : WordTrace (prefixWord ++ tailWord_8066869) baseStart_8066869 baseEnd_8066869 := by
    simpa [prefixWord, tailWord_8066869, baseEnd_8066869] using wordTrace_append hprefix tailTrace_8066869
  have hstable : (prefixWord ++ tailWord_8066869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066869).length < 2 ^ (prefixWord ++ tailWord_8066869).sum := by decide
  have hdescent : baseEnd_8066869 < baseStart_8066869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066870 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_8066870 : Nat := 118140960795 + 8066870 * 2 ^ 59
def prefixEnd_8066870 : Nat := 4983230072969 + 3 ^ 40 * 8066870 * 2
def baseEnd_8066870 : Nat := 4142181687334958567726147

theorem tailTrace_8066870 : CollatzResearch.WordTrace tailWord_8066870 prefixEnd_8066870 4142181687334958567726147 := by
  unfold tailWord_8066870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388932517819698534742379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196148613523410117703918709 18388932517819698534742379)
  ·
    refine ⟨27583398776729547802113569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18388932517819698534742379 27583398776729547802113569)
    ·
      refine ⟨20687549082547160851585177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27583398776729547802113569 20687549082547160851585177)
      ·
        refine ⟨15515661811910370638688883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20687549082547160851585177 15515661811910370638688883)
        ·
          refine ⟨23273492717865555958033325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15515661811910370638688883 23273492717865555958033325)
          ·
            refine ⟨8727559769199583484262497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23273492717865555958033325 8727559769199583484262497)
            ·
              refine ⟨6545669826899687613196873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8727559769199583484262497 6545669826899687613196873)
              ·
                refine ⟨4909252370174765709897655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545669826899687613196873 4909252370174765709897655)
                ·
                  refine ⟨7363878555262148564846483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909252370174765709897655 7363878555262148564846483)
                  ·
                    refine ⟨11045817832893222847269725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7363878555262148564846483 11045817832893222847269725)
                    ·
                      refine ⟨4142181687334958567726147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11045817832893222847269725 4142181687334958567726147)
                      ·
                        rfl

theorem cell23_8066870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_8066870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066870 prefixEnd_8066870 := by exact prefixLift 8066870
  have htrace : WordTrace (prefixWord ++ tailWord_8066870) baseStart_8066870 baseEnd_8066870 := by
    simpa [prefixWord, tailWord_8066870, baseEnd_8066870] using wordTrace_append hprefix tailTrace_8066870
  have hstable : (prefixWord ++ tailWord_8066870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066870).length < 2 ^ (prefixWord ++ tailWord_8066870).sum := by decide
  have hdescent : baseEnd_8066870 < baseStart_8066870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066886 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_8066886 : Nat := 118140960795 + 8066886 * 2 ^ 59
def prefixEnd_8066886 : Nat := 4983230072969 + 3 ^ 40 * 8066886 * 2
def baseEnd_8066886 : Nat := 1380729967675143501708691

theorem tailTrace_8066886 : CollatzResearch.WordTrace tailWord_8066886 prefixEnd_8066886 1380729967675143501708691 := by
  unfold tailWord_8066886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194484495408037852764391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196149002568704807525640341 9194484495408037852764391)
  ·
    refine ⟨13791726743112056779146587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9194484495408037852764391 13791726743112056779146587)
    ·
      refine ⟨20687590114668085168719881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13791726743112056779146587 20687590114668085168719881)
      ·
        refine ⟨15515692586001063876539911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20687590114668085168719881 15515692586001063876539911)
        ·
          refine ⟨23273538879001595814809867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15515692586001063876539911 23273538879001595814809867)
          ·
            refine ⟨34910308318502393722214801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23273538879001595814809867 34910308318502393722214801)
            ·
              refine ⟨26182731238876795291661101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34910308318502393722214801 26182731238876795291661101)
              ·
                refine ⟨9818524214578798234372913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26182731238876795291661101 9818524214578798234372913)
                ·
                  refine ⟨7363893160934098675779685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818524214578798234372913 7363893160934098675779685)
                  ·
                    refine ⟨1380729967675143501708691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7363893160934098675779685 1380729967675143501708691)
                    ·
                      rfl

theorem cell23_8066886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_8066886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066886 prefixEnd_8066886 := by exact prefixLift 8066886
  have htrace : WordTrace (prefixWord ++ tailWord_8066886) baseStart_8066886 baseEnd_8066886 := by
    simpa [prefixWord, tailWord_8066886, baseEnd_8066886] using wordTrace_append hprefix tailTrace_8066886
  have hstable : (prefixWord ++ tailWord_8066886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066886).length < 2 ^ (prefixWord ++ tailWord_8066886).sum := by decide
  have hdescent : baseEnd_8066886 < baseStart_8066886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066919 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_8066919 : Nat := 118140960795 + 8066919 * 2 ^ 59
def prefixEnd_8066919 : Nat := 4983230072969 + 3 ^ 40 * 8066919 * 2
def baseEnd_8066919 : Nat := 4142206847887028876013421

theorem tailTrace_8066919 : CollatzResearch.WordTrace tailWord_8066919 prefixEnd_8066919 4142206847887028876013421 := by
  unfold tailWord_8066919
  simp only [CollatzResearch.WordTrace]
  refine ⟨294224707461937657924411811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196149804974625105282941207 294224707461937657924411811)
  ·
    refine ⟨441337061192906486886617717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294224707461937657924411811 441337061192906486886617717)
    ·
      refine ⟨41375349486834983145620411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441337061192906486886617717 41375349486834983145620411)
      ·
        refine ⟨62063024230252474718430617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41375349486834983145620411 62063024230252474718430617)
        ·
          refine ⟨46547268172689356038822963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62063024230252474718430617 46547268172689356038822963)
          ·
            refine ⟨69820902259034034058234445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46547268172689356038822963 69820902259034034058234445)
            ·
              refine ⟨26182838347137762771837917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69820902259034034058234445 26182838347137762771837917)
              ·
                refine ⟨9818564380176661039439219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26182838347137762771837917 9818564380176661039439219)
                ·
                  refine ⟨14727846570264991559158829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818564380176661039439219 14727846570264991559158829)
                  ·
                    refine ⟨5522942463849371834684561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14727846570264991559158829 5522942463849371834684561)
                    ·
                      refine ⟨4142206847887028876013421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5522942463849371834684561 4142206847887028876013421)
                      ·
                        rfl

theorem cell23_8066919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_8066919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066919 prefixEnd_8066919 := by exact prefixLift 8066919
  have htrace : WordTrace (prefixWord ++ tailWord_8066919) baseStart_8066919 baseEnd_8066919 := by
    simpa [prefixWord, tailWord_8066919, baseEnd_8066919] using wordTrace_append hprefix tailTrace_8066919
  have hstable : (prefixWord ++ tailWord_8066919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066919).length < 2 ^ (prefixWord ++ tailWord_8066919).sum := by decide
  have hdescent : baseEnd_8066919 < baseStart_8066919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066925 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_8066925 : Nat := 118140960795 + 8066925 * 2 ^ 59
def prefixEnd_8066925 : Nat := 4983230072969 + 3 ^ 40 * 8066925 * 2
def baseEnd_8066925 : Nat := 1380736642923651950846131

theorem tailTrace_8066925 : CollatzResearch.WordTrace tailWord_8066925 prefixEnd_8066925 1380736642923651950846131 := by
  unfold tailWord_8066925
  simp only [CollatzResearch.WordTrace]
  refine ⟨294224926299915920949130229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196149950866610613966086819 294224926299915920949130229)
  ·
    refine ⟨27583586840617117588980959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294224926299915920949130229 27583586840617117588980959)
    ·
      refine ⟨41375380260925676383471439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27583586840617117588980959 41375380260925676383471439)
      ·
        refine ⟨62063070391388514575207159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41375380260925676383471439 62063070391388514575207159)
        ·
          refine ⟨93094605587082771862810739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62063070391388514575207159 93094605587082771862810739)
          ·
            refine ⟨139641908380624157794216109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93094605587082771862810739 139641908380624157794216109)
            ·
              refine ⟨52365715642734059172831041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139641908380624157794216109 52365715642734059172831041)
              ·
                refine ⟨39274286732050544379623281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52365715642734059172831041 39274286732050544379623281)
                ·
                  refine ⟨29455715049037908284717461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39274286732050544379623281 29455715049037908284717461)
                  ·
                    refine ⟨1380736642923651950846131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29455715049037908284717461 1380736642923651950846131)
                    ·
                      rfl

theorem cell23_8066925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_8066925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066925 prefixEnd_8066925 := by exact prefixLift 8066925
  have htrace : WordTrace (prefixWord ++ tailWord_8066925) baseStart_8066925 baseEnd_8066925 := by
    simpa [prefixWord, tailWord_8066925, baseEnd_8066925] using wordTrace_append hprefix tailTrace_8066925
  have hstable : (prefixWord ++ tailWord_8066925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066925).length < 2 ^ (prefixWord ++ tailWord_8066925).sum := by decide
  have hdescent : baseEnd_8066925 < baseStart_8066925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066926 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_8066926 : Nat := 118140960795 + 8066926 * 2 ^ 59
def prefixEnd_8066926 : Nat := 4983230072969 + 3 ^ 40 * 8066926 * 2
def baseEnd_8066926 : Nat := 4142210442251610348625889

theorem tailTrace_8066926 : CollatzResearch.WordTrace tailWord_8066926 prefixEnd_8066926 4142210442251610348625889 := by
  unfold tailWord_8066926
  simp only [CollatzResearch.WordTrace]
  refine ⟨36778120346614037264989579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196149975181941532079944421 36778120346614037264989579)
  ·
    refine ⟨55167180519921055897484369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36778120346614037264989579 55167180519921055897484369)
    ·
      refine ⟨41375385389940791923113277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55167180519921055897484369 41375385389940791923113277)
      ·
        refine ⟨15515769521227796971167479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41375385389940791923113277 15515769521227796971167479)
        ·
          refine ⟨23273654281841695456751219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15515769521227796971167479 23273654281841695456751219)
          ·
            refine ⟨34910481422762543185126829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23273654281841695456751219 34910481422762543185126829)
            ·
              refine ⟨13091430533535953694422561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34910481422762543185126829 13091430533535953694422561)
              ·
                refine ⟨9818572900151965270816921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091430533535953694422561 9818572900151965270816921)
                ·
                  refine ⟨7363929675113973953112691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818572900151965270816921 7363929675113973953112691)
                  ·
                    refine ⟨11045894512670960929669037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7363929675113973953112691 11045894512670960929669037)
                    ·
                      refine ⟨4142210442251610348625889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11045894512670960929669037 4142210442251610348625889)
                      ·
                        rfl

theorem cell23_8066926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_8066926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066926 prefixEnd_8066926 := by exact prefixLift 8066926
  have htrace : WordTrace (prefixWord ++ tailWord_8066926) baseStart_8066926 baseEnd_8066926 := by
    simpa [prefixWord, tailWord_8066926, baseEnd_8066926] using wordTrace_append hprefix tailTrace_8066926
  have hstable : (prefixWord ++ tailWord_8066926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066926).length < 2 ^ (prefixWord ++ tailWord_8066926).sum := by decide
  have hdescent : baseEnd_8066926 < baseStart_8066926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8066995 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5]
def baseStart_8066995 : Nat := 118140960795 + 8066995 * 2 ^ 59
def prefixEnd_8066995 : Nat := 4983230072969 + 3 ^ 40 * 8066995 * 2
def baseEnd_8066995 : Nat := 4142245872416770578663071

theorem tailTrace_8066995 : CollatzResearch.WordTrace tailWord_8066995 prefixEnd_8066995 4142245872416770578663071 := by
  unfold tailWord_8066995
  simp only [CollatzResearch.WordTrace]
  refine ⟨294227479409662322904178439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196151652939774881936118959 294227479409662322904178439)
  ·
    refine ⟨441341219114493484356267659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294227479409662322904178439 441341219114493484356267659)
    ·
      refine ⟨662011828671740226534401489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441341219114493484356267659 662011828671740226534401489)
      ·
        refine ⟨496508871503805169900801117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662011828671740226534401489 496508871503805169900801117)
        ·
          refine ⟨186190826813926938712800419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496508871503805169900801117 186190826813926938712800419)
          ·
            refine ⟨279286240220890408069200629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186190826813926938712800419 279286240220890408069200629)
            ·
              refine ⟨26183085020708475756487559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279286240220890408069200629 26183085020708475756487559)
              ·
                refine ⟨39274627531062713634731339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26183085020708475756487559 39274627531062713634731339)
                ·
                  refine ⟨58911941296594070452097009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39274627531062713634731339 58911941296594070452097009)
                  ·
                    refine ⟨44183955972445552839072757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58911941296594070452097009 44183955972445552839072757)
                    ·
                      refine ⟨4142245872416770578663071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44183955972445552839072757 4142245872416770578663071)
                      ·
                        rfl

theorem cell23_8066995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_8066995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8066995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8066995 prefixEnd_8066995 := by exact prefixLift 8066995
  have htrace : WordTrace (prefixWord ++ tailWord_8066995) baseStart_8066995 baseEnd_8066995 := by
    simpa [prefixWord, tailWord_8066995, baseEnd_8066995] using wordTrace_append hprefix tailTrace_8066995
  have hstable : (prefixWord ++ tailWord_8066995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8066995).length < 2 ^ (prefixWord ++ tailWord_8066995).sum := by decide
  have hdescent : baseEnd_8066995 < baseStart_8066995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8066995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067076 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8067076 : Nat := 118140960795 + 8067076 * 2 ^ 59
def prefixEnd_8067076 : Nat := 4983230072969 + 3 ^ 40 * 8067076 * 2
def baseEnd_8067076 : Nat := 4142287464349784761750199

theorem tailTrace_8067076 : CollatzResearch.WordTrace tailWord_8067076 prefixEnd_8067076 4142287464349784761750199 := by
  unfold tailWord_8067076
  simp only [CollatzResearch.WordTrace]
  refine ⟨147115216861184436868938541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196153622481579249158584721 147115216861184436868938541)
  ·
    refine ⟨55168206322944163825851953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147115216861184436868938541 55168206322944163825851953)
    ·
      refine ⟨41376154742208122869388965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55168206322944163825851953 41376154742208122869388965)
      ·
        refine ⟨7758029014164023038010431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41376154742208122869388965 7758029014164023038010431)
        ·
          refine ⟨11637043521246034557015647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758029014164023038010431 11637043521246034557015647)
          ·
            refine ⟨17455565281869051835523471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637043521246034557015647 17455565281869051835523471)
            ·
              refine ⟨26183347922803577753285207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17455565281869051835523471 26183347922803577753285207)
              ·
                refine ⟨39275021884205366629927811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26183347922803577753285207 39275021884205366629927811)
                ·
                  refine ⟨58912532826308049944891717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39275021884205366629927811 58912532826308049944891717)
                  ·
                    refine ⟨11046099904932759364667197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58912532826308049944891717 11046099904932759364667197)
                    ·
                      refine ⟨4142287464349784761750199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046099904932759364667197 4142287464349784761750199)
                      ·
                        rfl

theorem cell23_8067076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8067076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067076 prefixEnd_8067076 := by exact prefixLift 8067076
  have htrace : WordTrace (prefixWord ++ tailWord_8067076) baseStart_8067076 baseEnd_8067076 := by
    simpa [prefixWord, tailWord_8067076, baseEnd_8067076] using wordTrace_append hprefix tailTrace_8067076
  have hstable : (prefixWord ++ tailWord_8067076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067076).length < 2 ^ (prefixWord ++ tailWord_8067076).sum := by decide
  have hdescent : baseEnd_8067076 < baseStart_8067076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067106 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_8067106 : Nat := 118140960795 + 8067106 * 2 ^ 59
def prefixEnd_8067106 : Nat := 4983230072969 + 3 ^ 40 * 8067106 * 2
def baseEnd_8067106 : Nat := 4142302868769419644375061

theorem tailTrace_8067106 : CollatzResearch.WordTrace tailWord_8067106 prefixEnd_8067106 4142302868769419644375061 := by
  unfold tailWord_8067106
  simp only [CollatzResearch.WordTrace]
  refine ⟨73557881978065047215367293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196154351941506792574312781 73557881978065047215367293)
  ·
    refine ⟨27584205741774392705762735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73557881978065047215367293 27584205741774392705762735)
    ·
      refine ⟨41376308612661589058644103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27584205741774392705762735 41376308612661589058644103)
      ·
        refine ⟨62064462918992383587966155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41376308612661589058644103 62064462918992383587966155)
        ·
          refine ⟨93096694378488575381949233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62064462918992383587966155 93096694378488575381949233)
          ·
            refine ⟨69822520783866431536461925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93096694378488575381949233 69822520783866431536461925)
            ·
              refine ⟨13091722646974955913086611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69822520783866431536461925 13091722646974955913086611)
              ·
                refine ⟨19637583970462433869629917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13091722646974955913086611 19637583970462433869629917)
                ·
                  refine ⟨7364093988923412701111219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19637583970462433869629917 7364093988923412701111219)
                  ·
                    refine ⟨11046140983385119051666829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7364093988923412701111219 11046140983385119051666829)
                    ·
                      refine ⟨4142302868769419644375061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046140983385119051666829 4142302868769419644375061)
                      ·
                        rfl

theorem cell23_8067106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_8067106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067106 prefixEnd_8067106 := by exact prefixLift 8067106
  have htrace : WordTrace (prefixWord ++ tailWord_8067106) baseStart_8067106 baseEnd_8067106 := by
    simpa [prefixWord, tailWord_8067106, baseEnd_8067106] using wordTrace_append hprefix tailTrace_8067106
  have hstable : (prefixWord ++ tailWord_8067106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067106).length < 2 ^ (prefixWord ++ tailWord_8067106).sum := by decide
  have hdescent : baseEnd_8067106 < baseStart_8067106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067126 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_8067126 : Nat := 118140960795 + 8067126 * 2 ^ 59
def prefixEnd_8067126 : Nat := 4983230072969 + 3 ^ 40 * 8067126 * 2
def baseEnd_8067126 : Nat := 1380771046127503188708323

theorem tailTrace_8067126 : CollatzResearch.WordTrace tailWord_8067126 prefixEnd_8067126 1380771046127503188708323 := by
  unfold tailWord_8067126
  simp only [CollatzResearch.WordTrace]
  refine ⟨18389516085761733267324827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196154838248125154851464821 18389516085761733267324827)
  ·
    refine ⟨27584274128642599900987241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18389516085761733267324827 27584274128642599900987241)
    ·
      refine ⟨20688205596481949925740431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27584274128642599900987241 20688205596481949925740431)
      ·
        refine ⟨31032308394722924888610647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20688205596481949925740431 31032308394722924888610647)
        ·
          refine ⟨46548462592084387332915971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31032308394722924888610647 46548462592084387332915971)
          ·
            refine ⟨69822693888126580999373957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46548462592084387332915971 69822693888126580999373957)
            ·
              refine ⟨13091755104023733937382617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69822693888126580999373957 13091755104023733937382617)
              ·
                refine ⟨9818816328017800453036963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091755104023733937382617 9818816328017800453036963)
                ·
                  refine ⟨14728224492026700679555445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818816328017800453036963 14728224492026700679555445)
                  ·
                    refine ⟨1380771046127503188708323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14728224492026700679555445 1380771046127503188708323)
                    ·
                      rfl

theorem cell23_8067126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_8067126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067126 prefixEnd_8067126 := by exact prefixLift 8067126
  have htrace : WordTrace (prefixWord ++ tailWord_8067126) baseStart_8067126 baseEnd_8067126 := by
    simpa [prefixWord, tailWord_8067126, baseEnd_8067126] using wordTrace_append hprefix tailTrace_8067126
  have hstable : (prefixWord ++ tailWord_8067126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067126).length < 2 ^ (prefixWord ++ tailWord_8067126).sum := by decide
  have hdescent : baseEnd_8067126 < baseStart_8067126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067132 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_8067132 : Nat := 118140960795 + 8067132 * 2 ^ 59
def prefixEnd_8067132 : Nat := 4983230072969 + 3 ^ 40 * 8067132 * 2
def baseEnd_8067132 : Nat := 4142316219266436542649941

theorem tailTrace_8067132 : CollatzResearch.WordTrace tailWord_8067132 prefixEnd_8067132 4142316219266436542649941 := by
  unfold tailWord_8067132
  simp only [CollatzResearch.WordTrace]
  refine ⟨147116238105082997650957825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196154984140110663534610433 147116238105082997650957825)
  ·
    refine ⟨110337178578812248238218369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147116238105082997650957825 110337178578812248238218369)
    ·
      refine ⟨82752883934109186178663777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110337178578812248238218369 82752883934109186178663777)
      ·
        refine ⟨62064662950581889633997833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82752883934109186178663777 62064662950581889633997833)
        ·
          refine ⟨46548497212936417225498375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62064662950581889633997833 46548497212936417225498375)
          ·
            refine ⟨69822745819404625838247563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46548497212936417225498375 69822745819404625838247563)
            ·
              refine ⟨104734118729106938757371345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69822745819404625838247563 104734118729106938757371345)
              ·
                refine ⟨78550589046830204068028509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104734118729106938757371345 78550589046830204068028509)
                ·
                  refine ⟨29456470892561326525510691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78550589046830204068028509 29456470892561326525510691)
                  ·
                    refine ⟨44184706338841989788266037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29456470892561326525510691 44184706338841989788266037)
                    ·
                      refine ⟨4142316219266436542649941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44184706338841989788266037 4142316219266436542649941)
                      ·
                        rfl

theorem cell23_8067132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_8067132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067132 prefixEnd_8067132 := by exact prefixLift 8067132
  have htrace : WordTrace (prefixWord ++ tailWord_8067132) baseStart_8067132 baseEnd_8067132 := by
    simpa [prefixWord, tailWord_8067132, baseEnd_8067132] using wordTrace_append hprefix tailTrace_8067132
  have hstable : (prefixWord ++ tailWord_8067132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067132).length < 2 ^ (prefixWord ++ tailWord_8067132).sum := by decide
  have hdescent : baseEnd_8067132 < baseStart_8067132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067173 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_8067173 : Nat := 118140960795 + 8067173 * 2 ^ 59
def prefixEnd_8067173 : Nat := 4983230072969 + 3 ^ 40 * 8067173 * 2
def baseEnd_8067173 : Nat := 1380779090657756960745751

theorem tailTrace_8067173 : CollatzResearch.WordTrace tailWord_8067173 prefixEnd_8067173 1380779090657756960745751 := by
  unfold tailWord_8067173
  simp only [CollatzResearch.WordTrace]
  refine ⟨294233971603017459304158173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196155981068678306202772115 294233971603017459304158173)
  ·
    refine ⟨110337739351131547239059315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294233971603017459304158173 110337739351131547239059315)
    ·
      refine ⟨165506609026697320858588973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110337739351131547239059315 165506609026697320858588973)
      ·
        refine ⟨62064978385011495321970865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165506609026697320858588973 62064978385011495321970865)
        ·
          refine ⟨46548733788758621491478149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62064978385011495321970865 46548733788758621491478149)
          ·
            refine ⟨8727887585392241529652153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46548733788758621491478149 8727887585392241529652153)
            ·
              refine ⟨6545915689044181147239115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8727887585392241529652153 6545915689044181147239115)
              ·
                refine ⟨9818873533566271720858673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545915689044181147239115 9818873533566271720858673)
                ·
                  refine ⟨7364155150174703790644005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818873533566271720858673 7364155150174703790644005)
                  ·
                    refine ⟨1380779090657756960745751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364155150174703790644005 1380779090657756960745751)
                    ·
                      rfl

theorem cell23_8067173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_8067173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067173 prefixEnd_8067173 := by exact prefixLift 8067173
  have htrace : WordTrace (prefixWord ++ tailWord_8067173) baseStart_8067173 baseEnd_8067173 := by
    simpa [prefixWord, tailWord_8067173, baseEnd_8067173] using wordTrace_append hprefix tailTrace_8067173
  have hstable : (prefixWord ++ tailWord_8067173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067173).length < 2 ^ (prefixWord ++ tailWord_8067173).sum := by decide
  have hdescent : baseEnd_8067173 < baseStart_8067173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067214 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_8067214 : Nat := 118140960795 + 8067214 * 2 ^ 59
def prefixEnd_8067214 : Nat := 4983230072969 + 3 ^ 40 * 8067214 * 2
def baseEnd_8067214 : Nat := 4142358324680105221824565

theorem tailTrace_8067214 : CollatzResearch.WordTrace tailWord_8067214 prefixEnd_8067214 4142358324680105221824565 := by
  unfold tailWord_8067214
  simp only [CollatzResearch.WordTrace]
  refine ⟨36779433374483615413300087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196156977997245948870933797 36779433374483615413300087)
  ·
    refine ⟨55169150061725423119950131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36779433374483615413300087 55169150061725423119950131)
    ·
      refine ⟨82753725092588134679925197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55169150061725423119950131 82753725092588134679925197)
      ·
        refine ⟨31032646909720550504971949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82753725092588134679925197 31032646909720550504971949)
        ·
          refine ⟨11637242591145206439364481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31032646909720550504971949 11637242591145206439364481)
          ·
            refine ⟨8727931943358904829523361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11637242591145206439364481 8727931943358904829523361)
            ·
              refine ⟨6545948957519178622142521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8727931943358904829523361 6545948957519178622142521)
              ·
                refine ⟨4909461718139383966606891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545948957519178622142521 4909461718139383966606891)
                ·
                  refine ⟨7364192577209075949910337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909461718139383966606891 7364192577209075949910337)
                  ·
                    refine ⟨5523144432906806962432753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7364192577209075949910337 5523144432906806962432753)
                    ·
                      refine ⟨4142358324680105221824565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523144432906806962432753 4142358324680105221824565)
                      ·
                        rfl

theorem cell23_8067214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_8067214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067214 prefixEnd_8067214 := by exact prefixLift 8067214
  have htrace : WordTrace (prefixWord ++ tailWord_8067214) baseStart_8067214 baseEnd_8067214 := by
    simpa [prefixWord, tailWord_8067214, baseEnd_8067214] using wordTrace_append hprefix tailTrace_8067214
  have hstable : (prefixWord ++ tailWord_8067214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067214).length < 2 ^ (prefixWord ++ tailWord_8067214).sum := by decide
  have hdescent : baseEnd_8067214 < baseStart_8067214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067219 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 5, 4, 2]
def baseStart_8067219 : Nat := 118140960795 + 8067219 * 2 ^ 59
def prefixEnd_8067219 : Nat := 4983230072969 + 3 ^ 40 * 8067219 * 2
def baseEnd_8067219 : Nat := 4142360892083377702262041

theorem tailTrace_8067219 : CollatzResearch.WordTrace tailWord_8067219 prefixEnd_8067219 4142360892083377702262041 := by
  unfold tailWord_8067219
  simp only [CollatzResearch.WordTrace]
  refine ⟨294235649360850809160332711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196157099573900539440221807 294235649360850809160332711)
  ·
    refine ⟨441353474041276213740499067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294235649360850809160332711 441353474041276213740499067)
    ·
      refine ⟨662030211061914320610748601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441353474041276213740499067 662030211061914320610748601)
      ·
        refine ⟨496522658296435740458061451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662030211061914320610748601 496522658296435740458061451)
        ·
          refine ⟨744783987444653610687092177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496522658296435740458061451 744783987444653610687092177)
          ·
            refine ⟨558587990583490208015319133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744783987444653610687092177 558587990583490208015319133)
            ·
              refine ⟨209470496468808828005744675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558587990583490208015319133 209470496468808828005744675)
              ·
                refine ⟨314205744703213242008617013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209470496468808828005744675 314205744703213242008617013)
                ·
                  refine ⟨29456788565926241438307845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314205744703213242008617013 29456788565926241438307845)
                  ·
                    refine ⟨5523147856111170269682721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29456788565926241438307845 5523147856111170269682721)
                    ·
                      refine ⟨4142360892083377702262041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523147856111170269682721 4142360892083377702262041)
                      ·
                        rfl

theorem cell23_8067219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4, 2].length) (baseStart_8067219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067219 prefixEnd_8067219 := by exact prefixLift 8067219
  have htrace : WordTrace (prefixWord ++ tailWord_8067219) baseStart_8067219 baseEnd_8067219 := by
    simpa [prefixWord, tailWord_8067219, baseEnd_8067219] using wordTrace_append hprefix tailTrace_8067219
  have hstable : (prefixWord ++ tailWord_8067219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067219).length < 2 ^ (prefixWord ++ tailWord_8067219).sum := by decide
  have hdescent : baseEnd_8067219 < baseStart_8067219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067229 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_8067229 : Nat := 118140960795 + 8067229 * 2 ^ 59
def prefixEnd_8067229 : Nat := 4983230072969 + 3 ^ 40 * 8067229 * 2
def baseEnd_8067229 : Nat := 1380788675629974221045665

theorem tailTrace_8067229 : CollatzResearch.WordTrace tailWord_8067229 prefixEnd_8067229 1380788675629974221045665 := by
  unfold tailWord_8067229
  simp only [CollatzResearch.WordTrace]
  refine ⟨294236014090814580868196741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196157342727209720578797827 294236014090814580868196741)
  ·
    refine ⟨55169252642027733912786889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294236014090814580868196741 55169252642027733912786889)
    ·
      refine ⟨41376939481520800434590167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55169252642027733912786889 41376939481520800434590167)
      ·
        refine ⟨62065409222281200651885251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41376939481520800434590167 62065409222281200651885251)
        ·
          refine ⟨93098113833421800977827877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62065409222281200651885251 93098113833421800977827877)
          ·
            refine ⟨17455896343766587683342727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93098113833421800977827877 17455896343766587683342727)
            ·
              refine ⟨26183844515649881525014091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17455896343766587683342727 26183844515649881525014091)
              ·
                refine ⟨39275766773474822287521137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26183844515649881525014091 39275766773474822287521137)
                ·
                  refine ⟨29456825080106116715640853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39275766773474822287521137 29456825080106116715640853)
                  ·
                    refine ⟨1380788675629974221045665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29456825080106116715640853 1380788675629974221045665)
                    ·
                      rfl

theorem cell23_8067229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_8067229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067229 prefixEnd_8067229 := by exact prefixLift 8067229
  have htrace : WordTrace (prefixWord ++ tailWord_8067229) baseStart_8067229 baseEnd_8067229 := by
    simpa [prefixWord, tailWord_8067229, baseEnd_8067229] using wordTrace_append hprefix tailTrace_8067229
  have hstable : (prefixWord ++ tailWord_8067229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067229).length < 2 ^ (prefixWord ++ tailWord_8067229).sum := by decide
  have hdescent : baseEnd_8067229 < baseStart_8067229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067269 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_8067269 : Nat := 118140960795 + 8067269 * 2 ^ 59
def prefixEnd_8067269 : Nat := 4983230072969 + 3 ^ 40 * 8067269 * 2
def baseEnd_8067269 : Nat := 4142386566116102506636811

theorem tailTrace_8067269 : CollatzResearch.WordTrace tailWord_8067269 prefixEnd_8067269 4142386566116102506636811 := by
  unfold tailWord_8067269
  simp only [CollatzResearch.WordTrace]
  refine ⟨294237473010669667699652861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196158315340446445133101907 294237473010669667699652861)
  ·
    refine ⟨110339052379001125387369823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294237473010669667699652861 110339052379001125387369823)
    ·
      refine ⟨165508578568501688081054735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110339052379001125387369823 165508578568501688081054735)
      ·
        refine ⟨248262867852752532121582103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165508578568501688081054735 248262867852752532121582103)
        ·
          refine ⟨372394301779128798182373155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248262867852752532121582103 372394301779128798182373155)
          ·
            refine ⟨558591452668693197273559733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372394301779128798182373155 558591452668693197273559733)
            ·
              refine ⟨52367948687689987244396225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558591452668693197273559733 52367948687689987244396225)
              ·
                refine ⟨39275961515767490433297169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52367948687689987244396225 39275961515767490433297169)
                ·
                  refine ⟨29456971136825617824972877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39275961515767490433297169 29456971136825617824972877)
                  ·
                    refine ⟨11046364176309606684364829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29456971136825617824972877 11046364176309606684364829)
                    ·
                      refine ⟨4142386566116102506636811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046364176309606684364829 4142386566116102506636811)
                      ·
                        rfl

theorem cell23_8067269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_8067269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067269 prefixEnd_8067269 := by exact prefixLift 8067269
  have htrace : WordTrace (prefixWord ++ tailWord_8067269) baseStart_8067269 baseEnd_8067269 := by
    simpa [prefixWord, tailWord_8067269, baseEnd_8067269] using wordTrace_append hprefix tailTrace_8067269
  have hstable : (prefixWord ++ tailWord_8067269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067269).length < 2 ^ (prefixWord ++ tailWord_8067269).sum := by decide
  have hdescent : baseEnd_8067269 < baseStart_8067269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067376 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 7, 1, 3]
def baseStart_8067376 : Nat := 118140960795 + 8067376 * 2 ^ 59
def prefixEnd_8067376 : Nat := 4983230072969 + 3 ^ 40 * 8067376 * 2
def baseEnd_8067376 : Nat := 4142441508546133587998819

theorem tailTrace_8067376 : CollatzResearch.WordTrace tailWord_8067376 prefixEnd_8067376 4142441508546133587998819 := by
  unfold tailWord_8067376
  simp only [CollatzResearch.WordTrace]
  refine ⟨147120687810641012486898991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196160917080854683315865321 147120687810641012486898991)
  ·
    refine ⟨220681031715961518730348487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147120687810641012486898991 220681031715961518730348487)
    ·
      refine ⟨331021547573942278095522731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220681031715961518730348487 331021547573942278095522731)
      ·
        refine ⟨496532321360913417143284097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331021547573942278095522731 496532321360913417143284097)
        ·
          refine ⟨372399241020685062857463073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496532321360913417143284097 372399241020685062857463073)
          ·
            refine ⟨279299430765513797143097305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372399241020685062857463073 279299430765513797143097305)
            ·
              refine ⟨209474573074135347857322979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279299430765513797143097305 209474573074135347857322979)
              ·
                refine ⟨314211859611203021785984469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209474573074135347857322979 314211859611203021785984469)
                ·
                  refine ⟨7364340459637570823109011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 314211859611203021785984469 7364340459637570823109011)
                  ·
                    refine ⟨11046510689456356234663517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7364340459637570823109011 11046510689456356234663517)
                    ·
                      refine ⟨4142441508546133587998819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046510689456356234663517 4142441508546133587998819)
                      ·
                        rfl

theorem cell23_8067376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_8067376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067376 prefixEnd_8067376 := by exact prefixLift 8067376
  have htrace : WordTrace (prefixWord ++ tailWord_8067376) baseStart_8067376 baseEnd_8067376 := by
    simpa [prefixWord, tailWord_8067376, baseEnd_8067376] using wordTrace_append hprefix tailTrace_8067376
  have hstable : (prefixWord ++ tailWord_8067376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067376).length < 2 ^ (prefixWord ++ tailWord_8067376).sum := by decide
  have hdescent : baseEnd_8067376 < baseStart_8067376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067416 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 8, 2]
def baseStart_8067416 : Nat := 118140960795 + 8067416 * 2 ^ 59
def prefixEnd_8067416 : Nat := 4983230072969 + 3 ^ 40 * 8067416 * 2
def baseEnd_8067416 : Nat := 4142462047772313431498635

theorem tailTrace_8067416 : CollatzResearch.WordTrace tailWord_8067416 prefixEnd_8067416 4142462047772313431498635 := by
  unfold tailWord_8067416
  simp only [CollatzResearch.WordTrace]
  refine ⟨147121417270568555902627051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196161889694091407870169401 147121417270568555902627051)
  ·
    refine ⟨220682125905852833853940577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147121417270568555902627051 220682125905852833853940577)
    ·
      refine ⟨165511594429389625390455433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220682125905852833853940577 165511594429389625390455433)
      ·
        refine ⟨124133695822042219042841575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165511594429389625390455433 124133695822042219042841575)
        ·
          refine ⟨186200543733063328564262363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124133695822042219042841575 186200543733063328564262363)
          ·
            refine ⟨279300815599594992846393545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186200543733063328564262363 279300815599594992846393545)
            ·
              refine ⟨209475611699696244634795159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279300815599594992846393545 209475611699696244634795159)
              ·
                refine ⟨314213417549544366952192739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209475611699696244634795159 314213417549544366952192739)
                ·
                  refine ⟨471320126324316550428289109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314213417549544366952192739 471320126324316550428289109)
                  ·
                    refine ⟨5523282730363084575331513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 471320126324316550428289109 5523282730363084575331513)
                    ·
                      refine ⟨4142462047772313431498635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523282730363084575331513 4142462047772313431498635)
                      ·
                        rfl

theorem cell23_8067416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_8067416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067416 prefixEnd_8067416 := by exact prefixLift 8067416
  have htrace : WordTrace (prefixWord ++ tailWord_8067416) baseStart_8067416 baseEnd_8067416 := by
    simpa [prefixWord, tailWord_8067416, baseEnd_8067416] using wordTrace_append hprefix tailTrace_8067416
  have hstable : (prefixWord ++ tailWord_8067416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067416).length < 2 ^ (prefixWord ++ tailWord_8067416).sum := by decide
  have hdescent : baseEnd_8067416 < baseStart_8067416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067433 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 5, 2, 2]
def baseStart_8067433 : Nat := 118140960795 + 8067433 * 2 ^ 59
def prefixEnd_8067433 : Nat := 4983230072969 + 3 ^ 40 * 8067433 * 2
def baseEnd_8067433 : Nat := 4142470776943439864986057

theorem tailTrace_8067433 : CollatzResearch.WordTrace tailWord_8067433 prefixEnd_8067433 4142470776943439864986057 := by
  unfold tailWord_8067433
  simp only [CollatzResearch.WordTrace]
  refine ⟨294243454582075523708622953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196162303054717015805748635 294243454582075523708622953)
  ·
    refine ⟨220682590936556642781467215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294243454582075523708622953 220682590936556642781467215)
    ·
      refine ⟨331023886404834964172200823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220682590936556642781467215 331023886404834964172200823)
      ·
        refine ⟨496535829607252446258301235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331023886404834964172200823 496535829607252446258301235)
        ·
          refine ⟨744803744410878669387451853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496535829607252446258301235 744803744410878669387451853)
          ·
            refine ⟨279301404154079501020294445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744803744410878669387451853 279301404154079501020294445)
            ·
              refine ⟨104738026557779812882610417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279301404154079501020294445 104738026557779812882610417)
              ·
                refine ⟨78553519918334859661957813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104738026557779812882610417 78553519918334859661957813)
                ·
                  refine ⟨7364392492343893093308545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78553519918334859661957813 7364392492343893093308545)
                  ·
                    refine ⟨5523294369257919819981409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7364392492343893093308545 5523294369257919819981409)
                    ·
                      refine ⟨4142470776943439864986057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523294369257919819981409 4142470776943439864986057)
                      ·
                        rfl

theorem cell23_8067433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 2, 2].length) (baseStart_8067433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067433 prefixEnd_8067433 := by exact prefixLift 8067433
  have htrace : WordTrace (prefixWord ++ tailWord_8067433) baseStart_8067433 baseEnd_8067433 := by
    simpa [prefixWord, tailWord_8067433, baseEnd_8067433] using wordTrace_append hprefix tailTrace_8067433
  have hstable : (prefixWord ++ tailWord_8067433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067433).length < 2 ^ (prefixWord ++ tailWord_8067433).sum := by decide
  have hdescent : baseEnd_8067433 < baseStart_8067433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067449 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_8067449 : Nat := 118140960795 + 8067449 * 2 ^ 59
def prefixEnd_8067449 : Nat := 4983230072969 + 3 ^ 40 * 8067449 * 2
def baseEnd_8067449 : Nat := 4142478992633911802385983

theorem tailTrace_8067449 : CollatzResearch.WordTrace tailWord_8067449 prefixEnd_8067449 4142478992633911802385983 := by
  unfold tailWord_8067449
  simp only [CollatzResearch.WordTrace]
  refine ⟨294244038150017558441205401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196162692100011705627470267 294244038150017558441205401)
  ·
    refine ⟨220683028612513168830904051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294244038150017558441205401 220683028612513168830904051)
    ·
      refine ⟨331024542918769753246356077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220683028612513168830904051 331024542918769753246356077)
      ·
        refine ⟨124134203594538657467383529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331024542918769753246356077 124134203594538657467383529)
        ·
          refine ⟨93100652695903993100537647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124134203594538657467383529 93100652695903993100537647)
          ·
            refine ⟨139650979043855989650806471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93100652695903993100537647 139650979043855989650806471)
            ·
              refine ⟨209476468565783984476209707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139650979043855989650806471 209476468565783984476209707)
              ·
                refine ⟨314214702848675976714314561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209476468565783984476209707 314214702848675976714314561)
                ·
                  refine ⟨235661027136506982535735921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314214702848675976714314561 235661027136506982535735921)
                  ·
                    refine ⟨176745770352380236901801941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235661027136506982535735921 176745770352380236901801941)
                    ·
                      refine ⟨4142478992633911802385983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176745770352380236901801941 4142478992633911802385983)
                      ·
                        rfl

theorem cell23_8067449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_8067449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067449 prefixEnd_8067449 := by exact prefixLift 8067449
  have htrace : WordTrace (prefixWord ++ tailWord_8067449) baseStart_8067449 baseEnd_8067449 := by
    simpa [prefixWord, tailWord_8067449, baseEnd_8067449] using wordTrace_append hprefix tailTrace_8067449
  have hstable : (prefixWord ++ tailWord_8067449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067449).length < 2 ^ (prefixWord ++ tailWord_8067449).sum := by decide
  have hdescent : baseEnd_8067449 < baseStart_8067449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067460 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_8067460 : Nat := 118140960795 + 8067460 * 2 ^ 59
def prefixEnd_8067460 : Nat := 4983230072969 + 3 ^ 40 * 8067460 * 2
def baseEnd_8067460 : Nat := 1380828213640370419782811

theorem tailTrace_8067460 : CollatzResearch.WordTrace tailWord_8067460 prefixEnd_8067460 1380828213640370419782811 := by
  unfold tailWord_8067460
  simp only [CollatzResearch.WordTrace]
  refine ⟨147122219676488853659927917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196162959568651804879903889 147122219676488853659927917)
  ·
    refine ⟨55170832378683320122472969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147122219676488853659927917 55170832378683320122472969)
    ·
      refine ⟨41378124284012490091854727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55170832378683320122472969 41378124284012490091854727)
      ·
        refine ⟨62067186426018735137782091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41378124284012490091854727 62067186426018735137782091)
        ·
          refine ⟨93100779639028102706673137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62067186426018735137782091 93100779639028102706673137)
          ·
            refine ⟨69825584729271077030004853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93100779639028102706673137 69825584729271077030004853)
            ·
              refine ⟨6546148568369163471562955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69825584729271077030004853 6546148568369163471562955)
              ·
                refine ⟨9819222852553745207344433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546148568369163471562955 9819222852553745207344433)
                ·
                  refine ⟨7364417139415308905508325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9819222852553745207344433 7364417139415308905508325)
                  ·
                    refine ⟨1380828213640370419782811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364417139415308905508325 1380828213640370419782811)
                    ·
                      rfl

theorem cell23_8067460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_8067460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067460 prefixEnd_8067460 := by exact prefixLift 8067460
  have htrace : WordTrace (prefixWord ++ tailWord_8067460) baseStart_8067460 baseEnd_8067460 := by
    simpa [prefixWord, tailWord_8067460, baseEnd_8067460] using wordTrace_append hprefix tailTrace_8067460
  have hstable : (prefixWord ++ tailWord_8067460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067460).length < 2 ^ (prefixWord ++ tailWord_8067460).sum := by decide
  have hdescent : baseEnd_8067460 < baseStart_8067460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067470 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_8067470 : Nat := 118140960795 + 8067470 * 2 ^ 59
def prefixEnd_8067470 : Nat := 4983230072969 + 3 ^ 40 * 8067470 * 2
def baseEnd_8067470 : Nat := 4142489775727656220223387

theorem tailTrace_8067470 : CollatzResearch.WordTrace tailWord_8067470 prefixEnd_8067470 4142489775727656220223387 := by
  unfold tailWord_8067470
  simp only [CollatzResearch.WordTrace]
  refine ⟨36780600510367684878464983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196163202721960986018479909 36780600510367684878464983)
  ·
    refine ⟨55170900765551527317697475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36780600510367684878464983 55170900765551527317697475)
    ·
      refine ⟨82756351148327290976546213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55170900765551527317697475 82756351148327290976546213)
      ·
        refine ⟨15516815840311367058102415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82756351148327290976546213 15516815840311367058102415)
        ·
          refine ⟨23275223760467050587153623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15516815840311367058102415 23275223760467050587153623)
          ·
            refine ⟨34912835640700575880730435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23275223760467050587153623 34912835640700575880730435)
            ·
              refine ⟨52369253461050863821095653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34912835640700575880730435 52369253461050863821095653)
              ·
                refine ⟨9819235023947036966455435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52369253461050863821095653 9819235023947036966455435)
                ·
                  refine ⟨14728852535920555449683153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9819235023947036966455435 14728852535920555449683153)
                  ·
                    refine ⟨11046639401940416587262365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14728852535920555449683153 11046639401940416587262365)
                    ·
                      refine ⟨4142489775727656220223387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046639401940416587262365 4142489775727656220223387)
                      ·
                        rfl

theorem cell23_8067470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_8067470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067470 prefixEnd_8067470 := by exact prefixLift 8067470
  have htrace : WordTrace (prefixWord ++ tailWord_8067470) baseStart_8067470 baseEnd_8067470 := by
    simpa [prefixWord, tailWord_8067470, baseEnd_8067470] using wordTrace_append hprefix tailTrace_8067470
  have hstable : (prefixWord ++ tailWord_8067470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067470).length < 2 ^ (prefixWord ++ tailWord_8067470).sum := by decide
  have hdescent : baseEnd_8067470 < baseStart_8067470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067501 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_8067501 : Nat := 118140960795 + 8067501 * 2 ^ 59
def prefixEnd_8067501 : Nat := 4983230072969 + 3 ^ 40 * 8067501 * 2
def baseEnd_8067501 : Nat := 4142505693627945598935745

theorem tailTrace_8067501 : CollatzResearch.WordTrace tailWord_8067501 prefixEnd_8067501 4142505693627945598935745 := by
  unfold tailWord_8067501
  simp only [CollatzResearch.WordTrace]
  refine ⟨294245934745829171322098357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196163956497219447548065571 294245934745829171322098357)
  ·
    refine ⟨27585556382421484811446721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294245934745829171322098357 27585556382421484811446721)
    ·
      refine ⟨20689167286816113608585041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27585556382421484811446721 20689167286816113608585041)
      ·
        refine ⟨15516875465112085206438781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20689167286816113608585041 15516875465112085206438781)
        ·
          refine ⟨5818828299417031952414543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15516875465112085206438781 5818828299417031952414543)
          ·
            refine ⟨8728242449125547928621815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818828299417031952414543 8728242449125547928621815)
            ·
              refine ⟨13092363673688321892932723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728242449125547928621815 13092363673688321892932723)
              ·
                refine ⟨19638545510532482839399085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13092363673688321892932723 19638545510532482839399085)
                ·
                  refine ⟨7364454566449681064774657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19638545510532482839399085 7364454566449681064774657)
                  ·
                    refine ⟨5523340924837260798580993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7364454566449681064774657 5523340924837260798580993)
                    ·
                      refine ⟨4142505693627945598935745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523340924837260798580993 4142505693627945598935745)
                      ·
                        rfl

theorem cell23_8067501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_8067501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067501 prefixEnd_8067501 := by exact prefixLift 8067501
  have htrace : WordTrace (prefixWord ++ tailWord_8067501) baseStart_8067501 baseEnd_8067501 := by
    simpa [prefixWord, tailWord_8067501, baseEnd_8067501] using wordTrace_append hprefix tailTrace_8067501
  have hstable : (prefixWord ++ tailWord_8067501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067501).length < 2 ^ (prefixWord ++ tailWord_8067501).sum := by decide
  have hdescent : baseEnd_8067501 < baseStart_8067501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067506 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_8067506 : Nat := 118140960795 + 8067506 * 2 ^ 59
def prefixEnd_8067506 : Nat := 4983230072969 + 3 ^ 40 * 8067506 * 2
def baseEnd_8067506 : Nat := 4142508261031218079373221

theorem tailTrace_8067506 : CollatzResearch.WordTrace tailWord_8067506 prefixEnd_8067506 4142508261031218079373221 := by
  unfold tailWord_8067506
  simp only [CollatzResearch.WordTrace]
  refine ⟨73561529277702764294007593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196164078073874038117353581 73561529277702764294007593)
  ·
    refine ⟨55171146958277073220505695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73561529277702764294007593 55171146958277073220505695)
    ·
      refine ⟨82756720437415609830758543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55171146958277073220505695 82756720437415609830758543)
      ·
        refine ⟨124135080656123414746137815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82756720437415609830758543 124135080656123414746137815)
        ·
          refine ⟨186202620984185122119206723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124135080656123414746137815 186202620984185122119206723)
          ·
            refine ⟨279303931476277683178810085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186202620984185122119206723 279303931476277683178810085)
            ·
              refine ⟨52369487151802065596026891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279303931476277683178810085 52369487151802065596026891)
              ·
                refine ⟨78554230727703098394040337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52369487151802065596026891 78554230727703098394040337)
                ·
                  refine ⟨58915673045777323795530253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78554230727703098394040337 58915673045777323795530253)
                  ·
                    refine ⟨22093377392166496423323845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58915673045777323795530253 22093377392166496423323845)
                    ·
                      refine ⟨4142508261031218079373221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22093377392166496423323845 4142508261031218079373221)
                      ·
                        rfl

theorem cell23_8067506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_8067506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067506 prefixEnd_8067506 := by exact prefixLift 8067506
  have htrace : WordTrace (prefixWord ++ tailWord_8067506) baseStart_8067506 baseEnd_8067506 := by
    simpa [prefixWord, tailWord_8067506, baseEnd_8067506] using wordTrace_append hprefix tailTrace_8067506
  have hstable : (prefixWord ++ tailWord_8067506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067506).length < 2 ^ (prefixWord ++ tailWord_8067506).sum := by decide
  have hdescent : baseEnd_8067506 < baseStart_8067506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067517 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_8067517 : Nat := 118140960795 + 8067517 * 2 ^ 59
def prefixEnd_8067517 : Nat := 4983230072969 + 3 ^ 40 * 8067517 * 2
def baseEnd_8067517 : Nat := 4142513909318417536335671

theorem tailTrace_8067517 : CollatzResearch.WordTrace tailWord_8067517 prefixEnd_8067517 4142513909318417536335671 := by
  unfold tailWord_8067517
  simp only [CollatzResearch.WordTrace]
  refine ⟨294246518313771206054680805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196164345542514137369787203 294246518313771206054680805)
  ·
    refine ⟨55171222183832101135252651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294246518313771206054680805 55171222183832101135252651)
    ·
      refine ⟨82756833275748151702878977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55171222183832101135252651 82756833275748151702878977)
      ·
        refine ⟨62067624956811113777159233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82756833275748151702878977 62067624956811113777159233)
        ·
          refine ⟨46550718717608335332869425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62067624956811113777159233 46550718717608335332869425)
          ·
            refine ⟨34913039038206251499652069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46550718717608335332869425 34913039038206251499652069)
            ·
              refine ⟨6546194819663672156184763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34913039038206251499652069 6546194819663672156184763)
              ·
                refine ⟨9819292229495508234277145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546194819663672156184763 9819292229495508234277145)
                ·
                  refine ⟨7364469172121631175707859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9819292229495508234277145 7364469172121631175707859)
                  ·
                    refine ⟨11046703758182446763561789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7364469172121631175707859 11046703758182446763561789)
                    ·
                      refine ⟨4142513909318417536335671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046703758182446763561789 4142513909318417536335671)
                      ·
                        rfl

theorem cell23_8067517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_8067517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067517 prefixEnd_8067517 := by exact prefixLift 8067517
  have htrace : WordTrace (prefixWord ++ tailWord_8067517) baseStart_8067517 baseEnd_8067517 := by
    simpa [prefixWord, tailWord_8067517, baseEnd_8067517] using wordTrace_append hprefix tailTrace_8067517
  have hstable : (prefixWord ++ tailWord_8067517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067517).length < 2 ^ (prefixWord ++ tailWord_8067517).sum := by decide
  have hdescent : baseEnd_8067517 < baseStart_8067517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067521 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_8067521 : Nat := 118140960795 + 8067521 * 2 ^ 59
def prefixEnd_8067521 : Nat := 4983230072969 + 3 ^ 40 * 8067521 * 2
def baseEnd_8067521 : Nat := 4142515963241035520685653

theorem tailTrace_8067521 : CollatzResearch.WordTrace tailWord_8067521 prefixEnd_8067521 4142515963241035520685653 := by
  unfold tailWord_8067521
  simp only [CollatzResearch.WordTrace]
  refine ⟨294246664205756714737826417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196164442803837809825217611 294246664205756714737826417)
  ·
    refine ⟨220684998154317536053369813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294246664205756714737826417 220684998154317536053369813)
    ·
      refine ⟨5172304644241817251250855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 220684998154317536053369813 5172304644241817251250855)
      ·
        refine ⟨7758456966362725876876283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172304644241817251250855 7758456966362725876876283)
        ·
          refine ⟨11637685449544088815314425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758456966362725876876283 11637685449544088815314425)
          ·
            refine ⟨8728264087158066611485819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11637685449544088815314425 8728264087158066611485819)
            ·
              refine ⟨13092396130737099917228729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728264087158066611485819 13092396130737099917228729)
              ·
                refine ⟨9819297098052824937921547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13092396130737099917228729 9819297098052824937921547)
                ·
                  refine ⟨14728945647079237406882321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9819297098052824937921547 14728945647079237406882321)
                  ·
                    refine ⟨11046709235309428055161741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14728945647079237406882321 11046709235309428055161741)
                    ·
                      refine ⟨4142515963241035520685653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046709235309428055161741 4142515963241035520685653)
                      ·
                        rfl

theorem cell23_8067521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_8067521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067521 prefixEnd_8067521 := by exact prefixLift 8067521
  have htrace : WordTrace (prefixWord ++ tailWord_8067521) baseStart_8067521 baseEnd_8067521 := by
    simpa [prefixWord, tailWord_8067521, baseEnd_8067521] using wordTrace_append hprefix tailTrace_8067521
  have hstable : (prefixWord ++ tailWord_8067521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067521).length < 2 ^ (prefixWord ++ tailWord_8067521).sum := by decide
  have hdescent : baseEnd_8067521 < baseStart_8067521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067523 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 1, 4, 2]
def baseStart_8067523 : Nat := 118140960795 + 8067523 * 2 ^ 59
def prefixEnd_8067523 : Nat := 4983230072969 + 3 ^ 40 * 8067523 * 2
def baseEnd_8067523 : Nat := 4142516990202344512860643

theorem tailTrace_8067523 : CollatzResearch.WordTrace tailWord_8067523 prefixEnd_8067523 4142516990202344512860643 := by
  unfold tailWord_8067523
  simp only [CollatzResearch.WordTrace]
  refine ⟨294246737151749469079399223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196164491434499646052932815 294246737151749469079399223)
  ·
    refine ⟨441370105727624203619098835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294246737151749469079399223 441370105727624203619098835)
    ·
      refine ⟨662055158591436305428648253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441370105727624203619098835 662055158591436305428648253)
      ·
        refine ⟨248270684471788614535743095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662055158591436305428648253 248270684471788614535743095)
        ·
          refine ⟨372406026707682921803614643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248270684471788614535743095 372406026707682921803614643)
          ·
            refine ⟨558609040061524382705421965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372406026707682921803614643 558609040061524382705421965)
            ·
              refine ⟨209478390023071643514533237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558609040061524382705421965 209478390023071643514533237)
              ·
                refine ⟨19638599064662966579487491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209478390023071643514533237 19638599064662966579487491)
                ·
                  refine ⟨29457898596994449869231237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19638599064662966579487491 29457898596994449869231237)
                  ·
                    refine ⟨5523355986936459350480857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29457898596994449869231237 5523355986936459350480857)
                    ·
                      refine ⟨4142516990202344512860643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523355986936459350480857 4142516990202344512860643)
                      ·
                        rfl

theorem cell23_8067523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_8067523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067523 prefixEnd_8067523 := by exact prefixLift 8067523
  have htrace : WordTrace (prefixWord ++ tailWord_8067523) baseStart_8067523 baseEnd_8067523 := by
    simpa [prefixWord, tailWord_8067523, baseEnd_8067523] using wordTrace_append hprefix tailTrace_8067523
  have hstable : (prefixWord ++ tailWord_8067523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067523).length < 2 ^ (prefixWord ++ tailWord_8067523).sum := by decide
  have hdescent : baseEnd_8067523 < baseStart_8067523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067527 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_8067527 : Nat := 118140960795 + 8067527 * 2 ^ 59
def prefixEnd_8067527 : Nat := 4983230072969 + 3 ^ 40 * 8067527 * 2
def baseEnd_8067527 : Nat := 4142519044124962497210625

theorem tailTrace_8067527 : CollatzResearch.WordTrace tailWord_8067527 prefixEnd_8067527 4142519044124962497210625 := by
  unfold tailWord_8067527
  simp only [CollatzResearch.WordTrace]
  refine ⟨294246883043734977762544835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196164588695823318508363223 294246883043734977762544835)
  ·
    refine ⟨441370324565602466643817253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294246883043734977762544835 441370324565602466643817253)
    ·
      refine ⟨82756935856050462495715735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441370324565602466643817253 82756935856050462495715735)
      ·
        refine ⟨124135403784075693743573603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82756935856050462495715735 124135403784075693743573603)
        ·
          refine ⟨186203105676113540615360405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124135403784075693743573603 186203105676113540615360405)
          ·
            refine ⟨8728270578567822216345019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186203105676113540615360405 8728270578567822216345019)
            ·
              refine ⟨13092405867851733324517529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728270578567822216345019 13092405867851733324517529)
              ·
                refine ⟨9819304400888799993388147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13092405867851733324517529 9819304400888799993388147)
                ·
                  refine ⟨14728956601333199990082221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9819304400888799993388147 14728956601333199990082221)
                  ·
                    refine ⟨5523358725499949996280833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14728956601333199990082221 5523358725499949996280833)
                    ·
                      refine ⟨4142519044124962497210625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523358725499949996280833 4142519044124962497210625)
                      ·
                        rfl

theorem cell23_8067527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_8067527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067527 prefixEnd_8067527 := by exact prefixLift 8067527
  have htrace : WordTrace (prefixWord ++ tailWord_8067527) baseStart_8067527 baseEnd_8067527 := by
    simpa [prefixWord, tailWord_8067527, baseEnd_8067527] using wordTrace_append hprefix tailTrace_8067527
  have hstable : (prefixWord ++ tailWord_8067527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067527).length < 2 ^ (prefixWord ++ tailWord_8067527).sum := by decide
  have hdescent : baseEnd_8067527 < baseStart_8067527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067540 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_8067540 : Nat := 118140960795 + 8067540 * 2 ^ 59
def prefixEnd_8067540 : Nat := 4983230072969 + 3 ^ 40 * 8067540 * 2
def baseEnd_8067540 : Nat := 4142525719373470946348065

theorem tailTrace_8067540 : CollatzResearch.WordTrace tailWord_8067540 prefixEnd_8067540 4142525719373470946348065 := by
  unfold tailWord_8067540
  simp only [CollatzResearch.WordTrace]
  refine ⟨147123678596343940491384037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196164904795125253988512049 147123678596343940491384037)
  ·
    refine ⟨27585689736814488842134507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147123678596343940491384037 27585689736814488842134507)
    ·
      refine ⟨41378534605221733263201761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27585689736814488842134507 41378534605221733263201761)
      ·
        refine ⟨31033900953916299947401321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41378534605221733263201761 31033900953916299947401321)
        ·
          refine ⟨23275425715437224960550991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31033900953916299947401321 23275425715437224960550991)
          ·
            refine ⟨34913138573155837440826487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23275425715437224960550991 34913138573155837440826487)
            ·
              refine ⟨52369707859733756161239731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34913138573155837440826487 52369707859733756161239731)
              ·
                refine ⟨78554561789600634241859597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52369707859733756161239731 78554561789600634241859597)
                ·
                  refine ⟨29457960671100237840697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78554561789600634241859597 29457960671100237840697349)
                  ·
                    refine ⟨5523367625831294595130753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29457960671100237840697349 5523367625831294595130753)
                    ·
                      refine ⟨4142525719373470946348065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523367625831294595130753 4142525719373470946348065)
                      ·
                        rfl

theorem cell23_8067540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_8067540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067540 prefixEnd_8067540 := by exact prefixLift 8067540
  have htrace : WordTrace (prefixWord ++ tailWord_8067540) baseStart_8067540 baseEnd_8067540 := by
    simpa [prefixWord, tailWord_8067540, baseEnd_8067540] using wordTrace_append hprefix tailTrace_8067540
  have hstable : (prefixWord ++ tailWord_8067540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067540).length < 2 ^ (prefixWord ++ tailWord_8067540).sum := by decide
  have hdescent : baseEnd_8067540 < baseStart_8067540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067563 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 5]
def baseStart_8067563 : Nat := 118140960795 + 8067563 * 2 ^ 59
def prefixEnd_8067563 : Nat := 4983230072969 + 3 ^ 40 * 8067563 * 2
def baseEnd_8067563 : Nat := 460281947714280484040051

theorem tailTrace_8067563 : CollatzResearch.WordTrace tailWord_8067563 prefixEnd_8067563 460281947714280484040051 := by
  unfold tailWord_8067563
  simp only [CollatzResearch.WordTrace]
  refine ⟨294248196071604555910855343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196165464047736370607236895 294248196071604555910855343)
  ·
    refine ⟨441372294107406833866283015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294248196071604555910855343 441372294107406833866283015)
    ·
      refine ⟨662058441161110250799424523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441372294107406833866283015 662058441161110250799424523)
      ·
        refine ⟨993087661741665376199136785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662058441161110250799424523 993087661741665376199136785)
        ·
          refine ⟨744815746306249032149352589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993087661741665376199136785 744815746306249032149352589)
          ·
            refine ⟨279305904864843387056007221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744815746306249032149352589 279305904864843387056007221)
            ·
              refine ⟨26184928581079067536500677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279305904864843387056007221 26184928581079067536500677)
              ·
                refine ⟨4909674108952325163093877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26184928581079067536500677 4909674108952325163093877)
                ·
                  refine ⟨460281947714280484040051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4909674108952325163093877 460281947714280484040051)
                  ·
                    rfl

theorem cell23_8067563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 5].length) (baseStart_8067563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067563 prefixEnd_8067563 := by exact prefixLift 8067563
  have htrace : WordTrace (prefixWord ++ tailWord_8067563) baseStart_8067563 baseEnd_8067563 := by
    simpa [prefixWord, tailWord_8067563, baseEnd_8067563] using wordTrace_append hprefix tailTrace_8067563
  have hstable : (prefixWord ++ tailWord_8067563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067563).length < 2 ^ (prefixWord ++ tailWord_8067563).sum := by decide
  have hdescent : baseEnd_8067563 < baseStart_8067563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067570 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_8067570 : Nat := 118140960795 + 8067570 * 2 ^ 59
def prefixEnd_8067570 : Nat := 4983230072969 + 3 ^ 40 * 8067570 * 2
def baseEnd_8067570 : Nat := 4142541123793105828972927

theorem tailTrace_8067570 : CollatzResearch.WordTrace tailWord_8067570 prefixEnd_8067570 4142541123793105828972927 := by
  unfold tailWord_8067570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73562112845644799026590041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196165634255052797404240109 73562112845644799026590041)
  ·
    refine ⟨55171584634233599269942531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73562112845644799026590041 55171584634233599269942531)
    ·
      refine ⟨82757376951350398904913797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55171584634233599269942531 82757376951350398904913797)
      ·
        refine ⟨15517008178378199794671337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82757376951350398904913797 15517008178378199794671337)
        ·
          refine ⟨11637756133783649846003503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15517008178378199794671337 11637756133783649846003503)
          ·
            refine ⟨17456634200675474769005255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637756133783649846003503 17456634200675474769005255)
            ·
              refine ⟨26184951301013212153507883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17456634200675474769005255 26184951301013212153507883)
              ·
                refine ⟨39277426951519818230261825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26184951301013212153507883 39277426951519818230261825)
                ·
                  refine ⟨29458070213639863672696369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39277426951519818230261825 29458070213639863672696369)
                  ·
                    refine ⟨22093552660229897754522277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29458070213639863672696369 22093552660229897754522277)
                    ·
                      refine ⟨4142541123793105828972927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22093552660229897754522277 4142541123793105828972927)
                      ·
                        rfl

theorem cell23_8067570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_8067570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067570 prefixEnd_8067570 := by exact prefixLift 8067570
  have htrace : WordTrace (prefixWord ++ tailWord_8067570) baseStart_8067570 baseEnd_8067570 := by
    simpa [prefixWord, tailWord_8067570, baseEnd_8067570] using wordTrace_append hprefix tailTrace_8067570
  have hstable : (prefixWord ++ tailWord_8067570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067570).length < 2 ^ (prefixWord ++ tailWord_8067570).sum := by decide
  have hdescent : baseEnd_8067570 < baseStart_8067570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067576 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_8067576 : Nat := 118140960795 + 8067576 * 2 ^ 59
def prefixEnd_8067576 : Nat := 4983230072969 + 3 ^ 40 * 8067576 * 2
def baseEnd_8067576 : Nat := 1380848068225677601832633

theorem tailTrace_8067576 : CollatzResearch.WordTrace tailWord_8067576 prefixEnd_8067576 1380848068225677601832633 := by
  unfold tailWord_8067576
  simp only [CollatzResearch.WordTrace]
  refine ⟨147124335110278729565539291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196165780147038306087385721 147124335110278729565539291)
  ·
    refine ⟨220686502665418094348308937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147124335110278729565539291 220686502665418094348308937)
    ·
      refine ⟨165514876999063570761231703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220686502665418094348308937 165514876999063570761231703)
      ·
        refine ⟨248272315498595356141847555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165514876999063570761231703 248272315498595356141847555)
        ·
          refine ⟨372408473247893034212771333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248272315498595356141847555 372408473247893034212771333)
          ·
            refine ⟨69826588733979943914894625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372408473247893034212771333 69826588733979943914894625)
            ·
              refine ⟨52369941550484957936170969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69826588733979943914894625 52369941550484957936170969)
              ·
                refine ⟨39277456162863718452128227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52369941550484957936170969 39277456162863718452128227)
                ·
                  refine ⟨58916184244295577678192341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39277456162863718452128227 58916184244295577678192341)
                  ·
                    refine ⟨1380848068225677601832633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58916184244295577678192341 1380848068225677601832633)
                    ·
                      rfl

theorem cell23_8067576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_8067576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067576 prefixEnd_8067576 := by exact prefixLift 8067576
  have htrace : WordTrace (prefixWord ++ tailWord_8067576) baseStart_8067576 baseEnd_8067576 := by
    simpa [prefixWord, tailWord_8067576, baseEnd_8067576] using wordTrace_append hprefix tailTrace_8067576
  have hstable : (prefixWord ++ tailWord_8067576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067576).length < 2 ^ (prefixWord ++ tailWord_8067576).sum := by decide
  have hdescent : baseEnd_8067576 < baseStart_8067576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067583 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 2, 5, 2]
def baseStart_8067583 : Nat := 118140960795 + 8067583 * 2 ^ 59
def prefixEnd_8067583 : Nat := 4983230072969 + 3 ^ 40 * 8067583 * 2
def baseEnd_8067583 : Nat := 4142547799041614278110367

theorem tailTrace_8067583 : CollatzResearch.WordTrace tailWord_8067583 prefixEnd_8067583 4142547799041614278110367 := by
  unfold tailWord_8067583
  simp only [CollatzResearch.WordTrace]
  refine ⟨294248925531532099326583403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196165950354354732884388935 294248925531532099326583403)
  ·
    refine ⟨441373388297298148989875105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294248925531532099326583403 441373388297298148989875105)
    ·
      refine ⟨331030041222973611742406329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441373388297298148989875105 331030041222973611742406329)
      ·
        refine ⟨248272530917230208806804747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331030041222973611742406329 248272530917230208806804747)
        ·
          refine ⟨372408796375845313210207121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248272530917230208806804747 372408796375845313210207121)
          ·
            refine ⟨279306597281883984907655341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372408796375845313210207121 279306597281883984907655341)
            ·
              refine ⟨104739973980706494340370753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279306597281883984907655341 104739973980706494340370753)
              ·
                refine ⟨78554980485529870755278065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104739973980706494340370753 78554980485529870755278065)
                ·
                  refine ⟨58916235364147403066458549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78554980485529870755278065 58916235364147403066458549)
                  ·
                    refine ⟨5523397065388819037480489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58916235364147403066458549 5523397065388819037480489)
                    ·
                      refine ⟨4142547799041614278110367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523397065388819037480489 4142547799041614278110367)
                      ·
                        rfl

theorem cell23_8067583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_8067583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067583 prefixEnd_8067583 := by exact prefixLift 8067583
  have htrace : WordTrace (prefixWord ++ tailWord_8067583) baseStart_8067583 baseEnd_8067583 := by
    simpa [prefixWord, tailWord_8067583, baseEnd_8067583] using wordTrace_append hprefix tailTrace_8067583
  have hstable : (prefixWord ++ tailWord_8067583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067583).length < 2 ^ (prefixWord ++ tailWord_8067583).sum := by decide
  have hdescent : baseEnd_8067583 < baseStart_8067583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067633 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_8067633 : Nat := 118140960795 + 8067633 * 2 ^ 59
def prefixEnd_8067633 : Nat := 4983230072969 + 3 ^ 40 * 8067633 * 2
def baseEnd_8067633 : Nat := 4142573473074339082485137

theorem tailTrace_8067633 : CollatzResearch.WordTrace tailWord_8067633 prefixEnd_8067633 4142573473074339082485137 := by
  unfold tailWord_8067633
  simp only [CollatzResearch.WordTrace]
  refine ⟨294250749181350957865903553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196167166120900638577269035 294250749181350957865903553)
  ·
    refine ⟨220688061886013218399427665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294250749181350957865903553 220688061886013218399427665)
    ·
      refine ⟨165516046414509913799570749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220688061886013218399427665 165516046414509913799570749)
      ·
        refine ⟨62068517405441217674839031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165516046414509913799570749 62068517405441217674839031)
        ·
          refine ⟨93102776108161826512258547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62068517405441217674839031 93102776108161826512258547)
          ·
            refine ⟨139654164162242739768387821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93102776108161826512258547 139654164162242739768387821)
            ·
              refine ⟨52370311560841027413145433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139654164162242739768387821 52370311560841027413145433)
              ·
                refine ⟨39277733670630770559859075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52370311560841027413145433 39277733670630770559859075)
                ·
                  refine ⟨58916600505946155839788613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39277733670630770559859075 58916600505946155839788613)
                  ·
                    refine ⟨11046862594864904219960365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58916600505946155839788613 11046862594864904219960365)
                    ·
                      refine ⟨4142573473074339082485137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11046862594864904219960365 4142573473074339082485137)
                      ·
                        rfl

theorem cell23_8067633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_8067633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067633 prefixEnd_8067633 := by exact prefixLift 8067633
  have htrace : WordTrace (prefixWord ++ tailWord_8067633) baseStart_8067633 baseEnd_8067633 := by
    simpa [prefixWord, tailWord_8067633, baseEnd_8067633] using wordTrace_append hprefix tailTrace_8067633
  have hstable : (prefixWord ++ tailWord_8067633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067633).length < 2 ^ (prefixWord ++ tailWord_8067633).sum := by decide
  have hdescent : baseEnd_8067633 < baseStart_8067633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067683 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 3, 5]
def baseStart_8067683 : Nat := 118140960795 + 8067683 * 2 ^ 59
def prefixEnd_8067683 : Nat := 4983230072969 + 3 ^ 40 * 8067683 * 2
def baseEnd_8067683 : Nat := 1380866382369021295619969

theorem tailTrace_8067683 : CollatzResearch.WordTrace tailWord_8067683 prefixEnd_8067683 1380866382369021295619969 := by
  unfold tailWord_8067683
  simp only [CollatzResearch.WordTrace]
  refine ⟨294252572831169816405223703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196168381887446544270149135 294252572831169816405223703)
  ·
    refine ⟨441378859246754724607835555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294252572831169816405223703 441378859246754724607835555)
    ·
      refine ⟨662068288870132086911753333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441378859246754724607835555 662068288870132086911753333)
      ·
        refine ⟨62068902081574883147976875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 662068288870132086911753333 62068902081574883147976875)
        ·
          refine ⟨93103353122362324721965313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62068902081574883147976875 93103353122362324721965313)
          ·
            refine ⟨69827514841771743541473985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93103353122362324721965313 69827514841771743541473985)
            ·
              refine ⟨52370636131328807656105489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69827514841771743541473985 52370636131328807656105489)
              ·
                refine ⟨39277977098496605742079117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52370636131328807656105489 39277977098496605742079117)
                ·
                  refine ⟨14729241411936227153279669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39277977098496605742079117 14729241411936227153279669)
                  ·
                    refine ⟨1380866382369021295619969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14729241411936227153279669 1380866382369021295619969)
                    ·
                      rfl

theorem cell23_8067683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 5].length) (baseStart_8067683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067683 prefixEnd_8067683 := by exact prefixLift 8067683
  have htrace : WordTrace (prefixWord ++ tailWord_8067683) baseStart_8067683 baseEnd_8067683 := by
    simpa [prefixWord, tailWord_8067683, baseEnd_8067683] using wordTrace_append hprefix tailTrace_8067683
  have hstable : (prefixWord ++ tailWord_8067683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067683).length < 2 ^ (prefixWord ++ tailWord_8067683).sum := by decide
  have hdescent : baseEnd_8067683 < baseStart_8067683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067717 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_8067717 : Nat := 118140960795 + 8067717 * 2 ^ 59
def prefixEnd_8067717 : Nat := 4983230072969 + 3 ^ 40 * 8067717 * 2
def baseEnd_8067717 : Nat := 1380872201816438917944917

theorem tailTrace_8067717 : CollatzResearch.WordTrace tailWord_8067717 prefixEnd_8067717 1380872201816438917944917 := by
  unfold tailWord_8067717
  simp only [CollatzResearch.WordTrace]
  refine ⟨294253812913046640211961405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196169208608697760141307603 294253812913046640211961405)
  ·
    refine ⟨110345179842392490079485527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294253812913046640211961405 110345179842392490079485527)
    ·
      refine ⟨165517769763588735119228291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110345179842392490079485527 165517769763588735119228291)
      ·
        refine ⟨248276654645383102678842437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165517769763588735119228291 248276654645383102678842437)
        ·
          refine ⟨46551872746009331752282957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248276654645383102678842437 46551872746009331752282957)
          ·
            refine ⟨17456952279753499407106109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46551872746009331752282957 17456952279753499407106109)
            ·
              refine ⟨6546357104907562277664791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17456952279753499407106109 6546357104907562277664791)
              ·
                refine ⟨9819535657361343416497187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546357104907562277664791 9819535657361343416497187)
                ·
                  refine ⟨14729303486042015124745781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9819535657361343416497187 14729303486042015124745781)
                  ·
                    refine ⟨1380872201816438917944917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14729303486042015124745781 1380872201816438917944917)
                    ·
                      rfl

theorem cell23_8067717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_8067717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067717 prefixEnd_8067717 := by exact prefixLift 8067717
  have htrace : WordTrace (prefixWord ++ tailWord_8067717) baseStart_8067717 baseEnd_8067717 := by
    simpa [prefixWord, tailWord_8067717, baseEnd_8067717] using wordTrace_append hprefix tailTrace_8067717
  have hstable : (prefixWord ++ tailWord_8067717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067717).length < 2 ^ (prefixWord ++ tailWord_8067717).sum := by decide
  have hdescent : baseEnd_8067717 < baseStart_8067717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067723 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5]
def baseStart_8067723 : Nat := 118140960795 + 8067723 * 2 ^ 59
def prefixEnd_8067723 : Nat := 4983230072969 + 3 ^ 40 * 8067723 * 2
def baseEnd_8067723 : Nat := 4142619686333243730359723

theorem tailTrace_8067723 : CollatzResearch.WordTrace tailWord_8067723 prefixEnd_8067723 4142619686333243730359723 := by
  unfold tailWord_8067723
  simp only [CollatzResearch.WordTrace]
  refine ⟨294254031751024903236679823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196169354500683268824453215 294254031751024903236679823)
  ·
    refine ⟨441381047626537354855019735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294254031751024903236679823 441381047626537354855019735)
    ·
      refine ⟨662071571439806032282529603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441381047626537354855019735 662071571439806032282529603)
      ·
        refine ⟨993107357159709048423794405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662071571439806032282529603 993107357159709048423794405)
        ·
          refine ⟨186207629467445446579461451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 993107357159709048423794405 186207629467445446579461451)
          ·
            refine ⟨279311444201168169869192177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186207629467445446579461451 279311444201168169869192177)
            ·
              refine ⟨209483583150876127401894133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279311444201168169869192177 209483583150876127401894133)
              ·
                refine ⟨19639085920394636943927575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209483583150876127401894133 19639085920394636943927575)
                ·
                  refine ⟨29458628880591955415891363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19639085920394636943927575 29458628880591955415891363)
                  ·
                    refine ⟨44187943320887933123837045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29458628880591955415891363 44187943320887933123837045)
                    ·
                      refine ⟨4142619686333243730359723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44187943320887933123837045 4142619686333243730359723)
                      ·
                        rfl

theorem cell23_8067723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].length) (baseStart_8067723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067723 prefixEnd_8067723 := by exact prefixLift 8067723
  have htrace : WordTrace (prefixWord ++ tailWord_8067723) baseStart_8067723 baseEnd_8067723 := by
    simpa [prefixWord, tailWord_8067723, baseEnd_8067723] using wordTrace_append hprefix tailTrace_8067723
  have hstable : (prefixWord ++ tailWord_8067723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067723).length < 2 ^ (prefixWord ++ tailWord_8067723).sum := by decide
  have hdescent : baseEnd_8067723 < baseStart_8067723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067737 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 3, 2, 2]
def baseStart_8067737 : Nat := 118140960795 + 8067737 * 2 ^ 59
def prefixEnd_8067737 : Nat := 4983230072969 + 3 ^ 40 * 8067737 * 2
def baseEnd_8067737 : Nat := 4142626875062406675584659

theorem tailTrace_8067737 : CollatzResearch.WordTrace tailWord_8067737 prefixEnd_8067737 4142626875062406675584659 := by
  unfold tailWord_8067737
  simp only [CollatzResearch.WordTrace]
  refine ⟨294254542372974183627689465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196169694915316122418459643 294254542372974183627689465)
  ·
    refine ⟨220690906779730637720767099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294254542372974183627689465 220690906779730637720767099)
    ·
      refine ⟨331036360169595956581150649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220690906779730637720767099 331036360169595956581150649)
      ·
        refine ⟨248277270127196967435862987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331036360169595956581150649 248277270127196967435862987)
        ·
          refine ⟨372415905190795451153794481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248277270127196967435862987 372415905190795451153794481)
          ·
            refine ⟨279311928893096588365345861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372415905190795451153794481 279311928893096588365345861)
            ·
              refine ⟨52370986667455610318502349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279311928893096588365345861 52370986667455610318502349)
              ·
                refine ⟨19639120000295853869438381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52370986667455610318502349 19639120000295853869438381)
                ·
                  refine ⟨7364670000110945201039393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19639120000295853869438381 7364670000110945201039393)
                  ·
                    refine ⟨5523502500083208900779545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7364670000110945201039393 5523502500083208900779545)
                    ·
                      refine ⟨4142626875062406675584659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523502500083208900779545 4142626875062406675584659)
                      ·
                        rfl

theorem cell23_8067737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_8067737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067737 prefixEnd_8067737 := by exact prefixLift 8067737
  have htrace : WordTrace (prefixWord ++ tailWord_8067737) baseStart_8067737 baseEnd_8067737 := by
    simpa [prefixWord, tailWord_8067737, baseEnd_8067737] using wordTrace_append hprefix tailTrace_8067737
  have hstable : (prefixWord ++ tailWord_8067737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067737).length < 2 ^ (prefixWord ++ tailWord_8067737).sum := by decide
  have hdescent : baseEnd_8067737 < baseStart_8067737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067757 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_8067757 : Nat := 118140960795 + 8067757 * 2 ^ 59
def prefixEnd_8067757 : Nat := 4983230072969 + 3 ^ 40 * 8067757 * 2
def baseEnd_8067757 : Nat := 4142637144675496597334567

theorem tailTrace_8067757 : CollatzResearch.WordTrace tailWord_8067757 prefixEnd_8067757 4142637144675496597334567 := by
  unfold tailWord_8067757
  simp only [CollatzResearch.WordTrace]
  refine ⟨294255271832901727043417525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196170181221934484695611683 294255271832901727043417525)
  ·
    refine ⟨27586431734334536910320393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294255271832901727043417525 27586431734334536910320393)
    ·
      refine ⟨20689823800750902682740295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27586431734334536910320393 20689823800750902682740295)
      ·
        refine ⟨31034735701126354024110443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20689823800750902682740295 31034735701126354024110443)
        ·
          refine ⟨46552103551689531036165665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31034735701126354024110443 46552103551689531036165665)
          ·
            refine ⟨34914077663767148277124249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46552103551689531036165665 34914077663767148277124249)
            ·
              refine ⟨26185558247825361207843187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34914077663767148277124249 26185558247825361207843187)
              ·
                refine ⟨39278337371738041811764781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26185558247825361207843187 39278337371738041811764781)
                ·
                  refine ⟨14729376514401765679411793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39278337371738041811764781 14729376514401765679411793)
                  ·
                    refine ⟨11047032385801324259558845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14729376514401765679411793 11047032385801324259558845)
                    ·
                      refine ⟨4142637144675496597334567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047032385801324259558845 4142637144675496597334567)
                      ·
                        rfl

theorem cell23_8067757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_8067757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067757 prefixEnd_8067757 := by exact prefixLift 8067757
  have htrace : WordTrace (prefixWord ++ tailWord_8067757) baseStart_8067757 baseEnd_8067757 := by
    simpa [prefixWord, tailWord_8067757, baseEnd_8067757] using wordTrace_append hprefix tailTrace_8067757
  have hstable : (prefixWord ++ tailWord_8067757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067757).length < 2 ^ (prefixWord ++ tailWord_8067757).sum := by decide
  have hdescent : baseEnd_8067757 < baseStart_8067757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067770 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_8067770 : Nat := 118140960795 + 8067770 * 2 ^ 59
def prefixEnd_8067770 : Nat := 4983230072969 + 3 ^ 40 * 8067770 * 2
def baseEnd_8067770 : Nat := 4142643819924005046472007

theorem tailTrace_8067770 : CollatzResearch.WordTrace tailWord_8067770 prefixEnd_8067770 4142643819924005046472007 := by
  unfold tailWord_8067770
  simp only [CollatzResearch.WordTrace]
  refine ⟨73563936495463657565910191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196170497321236420175760509 73563936495463657565910191)
  ·
    refine ⟨110345904743195486348865287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73563936495463657565910191 110345904743195486348865287)
    ·
      refine ⟨165518857114793229523297931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110345904743195486348865287 165518857114793229523297931)
      ·
        refine ⟨248278285672189844284946897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165518857114793229523297931 248278285672189844284946897)
        ·
          refine ⟨186208714254142383213710173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248278285672189844284946897 186208714254142383213710173)
          ·
            refine ⟨69828267845303393705141315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186208714254142383213710173 69828267845303393705141315)
            ·
              refine ⟨104742401767955090557711973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69828267845303393705141315 104742401767955090557711973)
              ·
                refine ⟨19639200331491579479570995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104742401767955090557711973 19639200331491579479570995)
                ·
                  refine ⟨29458800497237369219356493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19639200331491579479570995 29458800497237369219356493)
                  ·
                    refine ⟨11047050186464013457258685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29458800497237369219356493 11047050186464013457258685)
                    ·
                      refine ⟨4142643819924005046472007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047050186464013457258685 4142643819924005046472007)
                      ·
                        rfl

theorem cell23_8067770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_8067770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067770 prefixEnd_8067770 := by exact prefixLift 8067770
  have htrace : WordTrace (prefixWord ++ tailWord_8067770) baseStart_8067770 baseEnd_8067770 := by
    simpa [prefixWord, tailWord_8067770, baseEnd_8067770] using wordTrace_append hprefix tailTrace_8067770
  have hstable : (prefixWord ++ tailWord_8067770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067770).length < 2 ^ (prefixWord ++ tailWord_8067770).sum := by decide
  have hdescent : baseEnd_8067770 < baseStart_8067770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067777 : List Nat := [1, 2, 6, 2, 1, 1, 10]
def baseStart_8067777 : Nat := 118140960795 + 8067777 * 2 ^ 59
def prefixEnd_8067777 : Nat := 4983230072969 + 3 ^ 40 * 8067777 * 2
def baseEnd_8067777 : Nat := 51143795238130697766475

theorem tailTrace_8067777 : CollatzResearch.WordTrace tailWord_8067777 prefixEnd_8067777 51143795238130697766475 := by
  unfold tailWord_8067777
  simp only [CollatzResearch.WordTrace]
  refine ⟨294256001292829270459145585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196170667528552846972763723 294256001292829270459145585)
  ·
    refine ⟨220692000969621952844359189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294256001292829270459145585 220692000969621952844359189)
    ·
      refine ⟨10344937545451029039579337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220692000969621952844359189 10344937545451029039579337)
      ·
        refine ⟨7758703159088271779684503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10344937545451029039579337 7758703159088271779684503)
        ·
          refine ⟨11638054738632407669526755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758703159088271779684503 11638054738632407669526755)
          ·
            refine ⟨17457082107948611504290133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638054738632407669526755 17457082107948611504290133)
            ·
              refine ⟨51143795238130697766475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17457082107948611504290133 51143795238130697766475)
              ·
                rfl

theorem cell23_8067777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 10].length) (baseStart_8067777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067777 prefixEnd_8067777 := by exact prefixLift 8067777
  have htrace : WordTrace (prefixWord ++ tailWord_8067777) baseStart_8067777 baseEnd_8067777 := by
    simpa [prefixWord, tailWord_8067777, baseEnd_8067777] using wordTrace_append hprefix tailTrace_8067777
  have hstable : (prefixWord ++ tailWord_8067777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067777).length < 2 ^ (prefixWord ++ tailWord_8067777).sum := by decide
  have hdescent : baseEnd_8067777 < baseStart_8067777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067783 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_8067783 : Nat := 118140960795 + 8067783 * 2 ^ 59
def prefixEnd_8067783 : Nat := 4983230072969 + 3 ^ 40 * 8067783 * 2
def baseEnd_8067783 : Nat := 4142650495172513495609447

theorem tailTrace_8067783 : CollatzResearch.WordTrace tailWord_8067783 prefixEnd_8067783 4142650495172513495609447 := by
  unfold tailWord_8067783
  simp only [CollatzResearch.WordTrace]
  refine ⟨294256220130807533483864003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196170813420538355655909335 294256220130807533483864003)
  ·
    refine ⟨441384330196211300225796005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294256220130807533483864003 441384330196211300225796005)
    ·
      refine ⟨82759561911789618792336751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441384330196211300225796005 82759561911789618792336751)
      ·
        refine ⟨124139342867684428188505127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82759561911789618792336751 124139342867684428188505127)
        ·
          refine ⟨186209014301526642282757691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124139342867684428188505127 186209014301526642282757691)
          ·
            refine ⟨279313521452289963424136537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186209014301526642282757691 279313521452289963424136537)
            ·
              refine ⟨209485141089217472568102403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279313521452289963424136537 209485141089217472568102403)
              ·
                refine ⟨314227711633826208852153605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209485141089217472568102403 314227711633826208852153605)
                ·
                  refine ⟨58917695931342414159778801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314227711633826208852153605 58917695931342414159778801)
                  ·
                    refine ⟨44188271948506810619834101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58917695931342414159778801 44188271948506810619834101)
                    ·
                      refine ⟨4142650495172513495609447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44188271948506810619834101 4142650495172513495609447)
                      ·
                        rfl

theorem cell23_8067783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_8067783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067783 prefixEnd_8067783 := by exact prefixLift 8067783
  have htrace : WordTrace (prefixWord ++ tailWord_8067783) baseStart_8067783 baseEnd_8067783 := by
    simpa [prefixWord, tailWord_8067783, baseEnd_8067783] using wordTrace_append hprefix tailTrace_8067783
  have hstable : (prefixWord ++ tailWord_8067783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067783).length < 2 ^ (prefixWord ++ tailWord_8067783).sum := by decide
  have hdescent : baseEnd_8067783 < baseStart_8067783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067804 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_8067804 : Nat := 118140960795 + 8067804 * 2 ^ 59
def prefixEnd_8067804 : Nat := 4983230072969 + 3 ^ 40 * 8067804 * 2
def baseEnd_8067804 : Nat := 4142661278266257913446851

theorem tailTrace_8067804 : CollatzResearch.WordTrace tailWord_8067804 prefixEnd_8067804 4142661278266257913446851 := by
  unfold tailWord_8067804
  simp only [CollatzResearch.WordTrace]
  refine ⟨147128493031865727035189233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196171324042487636046918977 147128493031865727035189233)
  ·
    refine ⟨110346369773899295276391925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147128493031865727035189233 110346369773899295276391925)
    ·
      refine ⟨10344972166303058932161743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110346369773899295276391925 10344972166303058932161743)
      ·
        refine ⟨15517458249454588398242615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10344972166303058932161743 15517458249454588398242615)
        ·
          refine ⟨23276187374181882597363923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15517458249454588398242615 23276187374181882597363923)
          ·
            refine ⟨34914281061272823896045885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23276187374181882597363923 34914281061272823896045885)
            ·
              refine ⟨13092855397977308961017207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34914281061272823896045885 13092855397977308961017207)
              ·
                refine ⟨19639283096965963441525811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13092855397977308961017207 19639283096965963441525811)
                ·
                  refine ⟨29458924645448945162288717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19639283096965963441525811 29458924645448945162288717)
                  ·
                    refine ⟨11047096742043354435858269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29458924645448945162288717 11047096742043354435858269)
                    ·
                      refine ⟨4142661278266257913446851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047096742043354435858269 4142661278266257913446851)
                      ·
                        rfl

theorem cell23_8067804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_8067804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067804 prefixEnd_8067804 := by exact prefixLift 8067804
  have htrace : WordTrace (prefixWord ++ tailWord_8067804) baseStart_8067804 baseEnd_8067804 := by
    simpa [prefixWord, tailWord_8067804, baseEnd_8067804] using wordTrace_append hprefix tailTrace_8067804
  have hstable : (prefixWord ++ tailWord_8067804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067804).length < 2 ^ (prefixWord ++ tailWord_8067804).sum := by decide
  have hdescent : baseEnd_8067804 < baseStart_8067804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067833 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 9]
def baseStart_8067833 : Nat := 118140960795 + 8067833 * 2 ^ 59
def prefixEnd_8067833 : Nat := 4983230072969 + 3 ^ 40 * 8067833 * 2
def baseEnd_8067833 : Nat := 460297352133915366664913

theorem tailTrace_8067833 : CollatzResearch.WordTrace tailWord_8067833 prefixEnd_8067833 460297352133915366664913 := by
  unfold tailWord_8067833
  simp only [CollatzResearch.WordTrace]
  refine ⟨294258043780626392023184153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196172029187084261348789435 294258043780626392023184153)
  ·
    refine ⟨220693532835469794017388115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294258043780626392023184153 220693532835469794017388115)
    ·
      refine ⟨331040299253204691026082173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220693532835469794017388115 331040299253204691026082173)
      ·
        refine ⟨124140112219951759134780815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331040299253204691026082173 124140112219951759134780815)
        ·
          refine ⟨186210168329927638702171223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124140112219951759134780815 186210168329927638702171223)
          ·
            refine ⟨279315252494891458053256835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186210168329927638702171223 279315252494891458053256835)
            ·
              refine ⟨418972878742337187079885253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279315252494891458053256835 418972878742337187079885253)
              ·
                refine ⟨78557414764188222577478485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418972878742337187079885253 78557414764188222577478485)
                ·
                  refine ⟨460297352133915366664913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78557414764188222577478485 460297352133915366664913)
                  ·
                    rfl

theorem cell23_8067833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_8067833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067833 prefixEnd_8067833 := by exact prefixLift 8067833
  have htrace : WordTrace (prefixWord ++ tailWord_8067833) baseStart_8067833 baseEnd_8067833 := by
    simpa [prefixWord, tailWord_8067833, baseEnd_8067833] using wordTrace_append hprefix tailTrace_8067833
  have hstable : (prefixWord ++ tailWord_8067833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067833).length < 2 ^ (prefixWord ++ tailWord_8067833).sum := by decide
  have hdescent : baseEnd_8067833 < baseStart_8067833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067843 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_8067843 : Nat := 118140960795 + 8067843 * 2 ^ 59
def prefixEnd_8067843 : Nat := 4983230072969 + 3 ^ 40 * 8067843 * 2
def baseEnd_8067843 : Nat := 4142681304011783260859171

theorem tailTrace_8067843 : CollatzResearch.WordTrace tailWord_8067843 prefixEnd_8067843 4142681304011783260859171 := by
  unfold tailWord_8067843
  simp only [CollatzResearch.WordTrace]
  refine ⟨294258408510590163731048183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196172272340393442487365455 294258408510590163731048183)
  ·
    refine ⟨441387612765885245596572275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294258408510590163731048183 441387612765885245596572275)
    ·
      refine ⟨662081419148827868394858413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441387612765885245596572275 662081419148827868394858413)
      ·
        refine ⟨248280532180810450648071905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662081419148827868394858413 248280532180810450648071905)
        ·
          refine ⟨186210399135607837986053929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248280532180810450648071905 186210399135607837986053929)
          ·
            refine ⟨139657799351705878489540447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186210399135607837986053929 139657799351705878489540447)
            ·
              refine ⟨209486699027558817734310671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139657799351705878489540447 209486699027558817734310671)
              ·
                refine ⟨314230048541338226601466007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209486699027558817734310671 314230048541338226601466007)
                ·
                  refine ⟨471345072812007339902199011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314230048541338226601466007 471345072812007339902199011)
                  ·
                    refine ⟨707017609218011009853298517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471345072812007339902199011 707017609218011009853298517)
                    ·
                      refine ⟨4142681304011783260859171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 707017609218011009853298517 4142681304011783260859171)
                      ·
                        rfl

theorem cell23_8067843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_8067843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067843 prefixEnd_8067843 := by exact prefixLift 8067843
  have htrace : WordTrace (prefixWord ++ tailWord_8067843) baseStart_8067843 baseEnd_8067843 := by
    simpa [prefixWord, tailWord_8067843, baseEnd_8067843] using wordTrace_append hprefix tailTrace_8067843
  have hstable : (prefixWord ++ tailWord_8067843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067843).length < 2 ^ (prefixWord ++ tailWord_8067843).sum := by decide
  have hdescent : baseEnd_8067843 < baseStart_8067843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067844 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_8067844 : Nat := 118140960795 + 8067844 * 2 ^ 59
def prefixEnd_8067844 : Nat := 4983230072969 + 3 ^ 40 * 8067844 * 2
def baseEnd_8067844 : Nat := 4142681817492437756946667

theorem tailTrace_8067844 : CollatzResearch.WordTrace tailWord_8067844 prefixEnd_8067844 4142681817492437756946667 := by
  unfold tailWord_8067844
  simp only [CollatzResearch.WordTrace]
  refine ⟨147129222491793270450917293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196172296655724360601223057 147129222491793270450917293)
  ·
    refine ⟨55173458434422476419093985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147129222491793270450917293 55173458434422476419093985)
    ·
      refine ⟨41380093825816857314320489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55173458434422476419093985 41380093825816857314320489)
      ·
        refine ⟨31035070369362642985740367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41380093825816857314320489 31035070369362642985740367)
        ·
          refine ⟨46552605554043964478610551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31035070369362642985740367 46552605554043964478610551)
          ·
            refine ⟨69828908331065946717915827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46552605554043964478610551 69828908331065946717915827)
            ·
              refine ⟨104743362496598920076873741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69828908331065946717915827 104743362496598920076873741)
              ·
                refine ⟨39278760936224595028827653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104743362496598920076873741 39278760936224595028827653)
                ·
                  refine ⟨7364767675542111567905185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39278760936224595028827653 7364767675542111567905185)
                  ·
                    refine ⟨5523575756656583675928889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7364767675542111567905185 5523575756656583675928889)
                    ·
                      refine ⟨4142681817492437756946667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523575756656583675928889 4142681817492437756946667)
                      ·
                        rfl

theorem cell23_8067844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_8067844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067844 prefixEnd_8067844 := by exact prefixLift 8067844
  have htrace : WordTrace (prefixWord ++ tailWord_8067844) baseStart_8067844 baseEnd_8067844 := by
    simpa [prefixWord, tailWord_8067844, baseEnd_8067844] using wordTrace_append hprefix tailTrace_8067844
  have hstable : (prefixWord ++ tailWord_8067844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067844).length < 2 ^ (prefixWord ++ tailWord_8067844).sum := by decide
  have hdescent : baseEnd_8067844 < baseStart_8067844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067890 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_8067890 : Nat := 118140960795 + 8067890 * 2 ^ 59
def prefixEnd_8067890 : Nat := 4983230072969 + 3 ^ 40 * 8067890 * 2
def baseEnd_8067890 : Nat := 4142705437602544576971455

theorem tailTrace_8067890 : CollatzResearch.WordTrace tailWord_8067890 prefixEnd_8067890 4142705437602544576971455 := by
  unfold tailWord_8067890
  simp only [CollatzResearch.WordTrace]
  refine ⟨73565030685354972689502281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196173415160946593838672749 73565030685354972689502281)
  ·
    refine ⟨55173773014016229517126711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73565030685354972689502281 55173773014016229517126711)
    ·
      refine ⟨82760659521024344275690067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55173773014016229517126711 82760659521024344275690067)
      ·
        refine ⟨124140989281536516413535101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82760659521024344275690067 124140989281536516413535101)
        ·
          refine ⟨46552870980576193655075663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124140989281536516413535101 46552870980576193655075663)
          ·
            refine ⟨69829306470864290482613495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46552870980576193655075663 69829306470864290482613495)
            ·
              refine ⟨104743959706296435723920243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69829306470864290482613495 104743959706296435723920243)
              ·
                refine ⟨157115939559444653585880365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104743959706296435723920243 157115939559444653585880365)
                ·
                  refine ⟨58918477334791745094705137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157115939559444653585880365 58918477334791745094705137)
                  ·
                    refine ⟨44188858001093808821028853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58918477334791745094705137 44188858001093808821028853)
                    ·
                      refine ⟨4142705437602544576971455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44188858001093808821028853 4142705437602544576971455)
                      ·
                        rfl

theorem cell23_8067890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_8067890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067890 prefixEnd_8067890 := by exact prefixLift 8067890
  have htrace : WordTrace (prefixWord ++ tailWord_8067890) baseStart_8067890 baseEnd_8067890 := by
    simpa [prefixWord, tailWord_8067890, baseEnd_8067890] using wordTrace_append hprefix tailTrace_8067890
  have hstable : (prefixWord ++ tailWord_8067890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067890).length < 2 ^ (prefixWord ++ tailWord_8067890).sum := by decide
  have hdescent : baseEnd_8067890 < baseStart_8067890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067900 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_8067900 : Nat := 118140960795 + 8067900 * 2 ^ 59
def prefixEnd_8067900 : Nat := 4983230072969 + 3 ^ 40 * 8067900 * 2
def baseEnd_8067900 : Nat := 4142710572409089537846409

theorem tailTrace_8067900 : CollatzResearch.WordTrace tailWord_8067900 prefixEnd_8067900 4142710572409089537846409 := by
  unfold tailWord_8067900
  simp only [CollatzResearch.WordTrace]
  refine ⟨147130243735691831232936577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196173658314255774977248769 147130243735691831232936577)
  ·
    refine ⟨110347682801768873424702433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147130243735691831232936577 110347682801768873424702433)
    ·
      refine ⟨82760762101326655068526825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110347682801768873424702433 82760762101326655068526825)
      ·
        refine ⟨62070571575994991301395119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82760762101326655068526825 62070571575994991301395119)
        ·
          refine ⟨93105857363992486952092679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62070571575994991301395119 93105857363992486952092679)
          ·
            refine ⟨139658786045988730428139019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93105857363992486952092679 139658786045988730428139019)
            ·
              refine ⟨209488179068983095642208529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139658786045988730428139019 209488179068983095642208529)
              ·
                refine ⟨157116134301737321731656397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209488179068983095642208529 157116134301737321731656397)
                ·
                  refine ⟨58918550363151495649371149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157116134301737321731656397 58918550363151495649371149)
                  ·
                    refine ⟨22094456386181810868514181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58918550363151495649371149 22094456386181810868514181)
                    ·
                      refine ⟨4142710572409089537846409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22094456386181810868514181 4142710572409089537846409)
                      ·
                        rfl

theorem cell23_8067900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_8067900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067900 prefixEnd_8067900 := by exact prefixLift 8067900
  have htrace : WordTrace (prefixWord ++ tailWord_8067900) baseStart_8067900 baseEnd_8067900 := by
    simpa [prefixWord, tailWord_8067900, baseEnd_8067900] using wordTrace_append hprefix tailTrace_8067900
  have hstable : (prefixWord ++ tailWord_8067900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067900).length < 2 ^ (prefixWord ++ tailWord_8067900).sum := by decide
  have hdescent : baseEnd_8067900 < baseStart_8067900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067927 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 5, 4]
def baseStart_8067927 : Nat := 118140960795 + 8067927 * 2 ^ 59
def prefixEnd_8067927 : Nat := 4983230072969 + 3 ^ 40 * 8067927 * 2
def baseEnd_8067927 : Nat := 1380908145462253644069595

theorem tailTrace_8067927 : CollatzResearch.WordTrace tailWord_8067927 prefixEnd_8067927 1380908145462253644069595 := by
  unfold tailWord_8067927
  simp only [CollatzResearch.WordTrace]
  refine ⟨294261472242285846077106035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196174314828190564051404023 294261472242285846077106035)
  ·
    refine ⟨441392208363428769115659053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294261472242285846077106035 441392208363428769115659053)
    ·
      refine ⟨165522078136285788418372145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441392208363428769115659053 165522078136285788418372145)
      ·
        refine ⟨124141558602214341313779109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165522078136285788418372145 124141558602214341313779109)
        ·
          refine ⟨23276542237915188996333583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124141558602214341313779109 23276542237915188996333583)
          ·
            refine ⟨34914813356872783494500375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23276542237915188996333583 34914813356872783494500375)
            ·
              refine ⟨52372220035309175241750563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34914813356872783494500375 52372220035309175241750563)
              ·
                refine ⟨78558330052963762862625845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52372220035309175241750563 78558330052963762862625845)
                ·
                  refine ⟨7364843442465352768371173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78558330052963762862625845 7364843442465352768371173)
                  ·
                    refine ⟨1380908145462253644069595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7364843442465352768371173 1380908145462253644069595)
                    ·
                      rfl

theorem cell23_8067927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_8067927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067927 prefixEnd_8067927 := by exact prefixLift 8067927
  have htrace : WordTrace (prefixWord ++ tailWord_8067927) baseStart_8067927 baseEnd_8067927 := by
    simpa [prefixWord, tailWord_8067927, baseEnd_8067927] using wordTrace_append hprefix tailTrace_8067927
  have hstable : (prefixWord ++ tailWord_8067927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067927).length < 2 ^ (prefixWord ++ tailWord_8067927).sum := by decide
  have hdescent : baseEnd_8067927 < baseStart_8067927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067937 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_8067937 : Nat := 118140960795 + 8067937 * 2 ^ 59
def prefixEnd_8067937 : Nat := 4983230072969 + 3 ^ 40 * 8067937 * 2
def baseEnd_8067937 : Nat := 4142729571193305893083739

theorem tailTrace_8067937 : CollatzResearch.WordTrace tailWord_8067937 prefixEnd_8067937 4142729571193305893083739 := by
  unfold tailWord_8067937
  simp only [CollatzResearch.WordTrace]
  refine ⟨294261836972249617784970065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196174557981499745189980043 294261836972249617784970065)
  ·
    refine ⟨220696377729187213338727549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294261836972249617784970065 220696377729187213338727549)
    ·
      refine ⟨82761141648445205002022831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220696377729187213338727549 82761141648445205002022831)
      ·
        refine ⟨124141712472667807503034247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82761141648445205002022831 124141712472667807503034247)
        ·
          refine ⟨186212568709001711254551371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124141712472667807503034247 186212568709001711254551371)
          ·
            refine ⟨279318853063502566881827057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186212568709001711254551371 279318853063502566881827057)
            ·
              refine ⟨209489139797626925161370293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279318853063502566881827057 209489139797626925161370293)
              ·
                refine ⟨19639606856027524233878465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209489139797626925161370293 19639606856027524233878465)
                ·
                  refine ⟨14729705142020643175408849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19639606856027524233878465 14729705142020643175408849)
                  ·
                    refine ⟨11047278856515482381556637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14729705142020643175408849 11047278856515482381556637)
                    ·
                      refine ⟨4142729571193305893083739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047278856515482381556637 4142729571193305893083739)
                      ·
                        rfl

theorem cell23_8067937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_8067937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067937 prefixEnd_8067937 := by exact prefixLift 8067937
  have htrace : WordTrace (prefixWord ++ tailWord_8067937) baseStart_8067937 baseEnd_8067937 := by
    simpa [prefixWord, tailWord_8067937, baseEnd_8067937] using wordTrace_append hprefix tailTrace_8067937
  have hstable : (prefixWord ++ tailWord_8067937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067937).length < 2 ^ (prefixWord ++ tailWord_8067937).sum := by decide
  have hdescent : baseEnd_8067937 < baseStart_8067937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067957 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 8]
def baseStart_8067957 : Nat := 118140960795 + 8067957 * 2 ^ 59
def prefixEnd_8067957 : Nat := 4983230072969 + 3 ^ 40 * 8067957 * 2
def baseEnd_8067957 : Nat := 460304426756266201648183

theorem tailTrace_8067957 : CollatzResearch.WordTrace tailWord_8067957 prefixEnd_8067957 460304426756266201648183 := by
  unfold tailWord_8067957
  simp only [CollatzResearch.WordTrace]
  refine ⟨294262566432177161200698125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196175044288118107467132083 294262566432177161200698125)
  ·
    refine ⟨110348462412066435450261797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294262566432177161200698125 110348462412066435450261797)
    ·
      refine ⟨20690336702262456646924087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110348462412066435450261797 20690336702262456646924087)
      ·
        refine ⟨31035505053393684970386131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20690336702262456646924087 31035505053393684970386131)
        ·
          refine ⟨46553257580090527455579197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31035505053393684970386131 46553257580090527455579197)
          ·
            refine ⟨17457471592533947795842199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46553257580090527455579197 17457471592533947795842199)
            ·
              refine ⟨26186207388800921693763299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17457471592533947795842199 26186207388800921693763299)
              ·
                refine ⟨39279311083201382540644949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26186207388800921693763299 39279311083201382540644949)
                ·
                  refine ⟨460304426756266201648183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39279311083201382540644949 460304426756266201648183)
                  ·
                    rfl

theorem cell23_8067957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_8067957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067957 prefixEnd_8067957 := by exact prefixLift 8067957
  have htrace : WordTrace (prefixWord ++ tailWord_8067957) baseStart_8067957 baseEnd_8067957 := by
    simpa [prefixWord, tailWord_8067957, baseEnd_8067957] using wordTrace_append hprefix tailTrace_8067957
  have hstable : (prefixWord ++ tailWord_8067957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067957).length < 2 ^ (prefixWord ++ tailWord_8067957).sum := by decide
  have hdescent : baseEnd_8067957 < baseStart_8067957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8067980 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_8067980 : Nat := 118140960795 + 8067980 * 2 ^ 59
def prefixEnd_8067980 : Nat := 4983230072969 + 3 ^ 40 * 8067980 * 2
def baseEnd_8067980 : Nat := 4142751650861449224846041

theorem tailTrace_8067980 : CollatzResearch.WordTrace tailWord_8067980 prefixEnd_8067980 4142751650861449224846041 := by
  unfold tailWord_8067980
  simp only [CollatzResearch.WordTrace]
  refine ⟨147131702655546918064392697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196175603540729224085856929 147131702655546918064392697)
  ·
    refine ⟨110348776991660188548294523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147131702655546918064392697 110348776991660188548294523)
    ·
      refine ⟨165523165487490282822441785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110348776991660188548294523 165523165487490282822441785)
      ·
        refine ⟨124142374115617712116831339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165523165487490282822441785 124142374115617712116831339)
        ·
          refine ⟨186213561173426568175247009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124142374115617712116831339 186213561173426568175247009)
          ·
            refine ⟨139660170880069926131435257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186213561173426568175247009 139660170880069926131435257)
            ·
              refine ⟨104745128160052444598576443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139660170880069926131435257 104745128160052444598576443)
              ·
                refine ⟨157117692240078666897864665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104745128160052444598576443 157117692240078666897864665)
                ·
                  refine ⟨117838269180059000173398499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157117692240078666897864665 117838269180059000173398499)
                  ·
                    refine ⟨176757403770088500260097749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117838269180059000173398499 176757403770088500260097749)
                    ·
                      refine ⟨4142751650861449224846041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176757403770088500260097749 4142751650861449224846041)
                      ·
                        rfl

theorem cell23_8067980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_8067980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8067980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8067980 prefixEnd_8067980 := by exact prefixLift 8067980
  have htrace : WordTrace (prefixWord ++ tailWord_8067980) baseStart_8067980 baseEnd_8067980 := by
    simpa [prefixWord, tailWord_8067980, baseEnd_8067980] using wordTrace_append hprefix tailTrace_8067980
  have hstable : (prefixWord ++ tailWord_8067980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8067980).length < 2 ^ (prefixWord ++ tailWord_8067980).sum := by decide
  have hdescent : baseEnd_8067980 < baseStart_8067980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8067980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068044 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_8068044 : Nat := 118140960795 + 8068044 * 2 ^ 59
def prefixEnd_8068044 : Nat := 4983230072969 + 3 ^ 40 * 8068044 * 2
def baseEnd_8068044 : Nat := 4142784513623336974445747

theorem tailTrace_8068044 : CollatzResearch.WordTrace tailWord_8068044 prefixEnd_8068044 4142784513623336974445747 := by
  unfold tailWord_8068044
  simp only [CollatzResearch.WordTrace]
  refine ⟨147132869791430987529557593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196177159721907983372743457 147132869791430987529557593)
  ·
    refine ⟨110349652343573240647168195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147132869791430987529557593 110349652343573240647168195)
    ·
      refine ⟨165524478515359860970752293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110349652343573240647168195 165524478515359860970752293)
      ·
        refine ⟨31035839721629973932016055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165524478515359860970752293 31035839721629973932016055)
        ·
          refine ⟨46553759582444960898024083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31035839721629973932016055 46553759582444960898024083)
          ·
            refine ⟨69830639373667441347036125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46553759582444960898024083 69830639373667441347036125)
            ·
              refine ⟨26186489765125290505138547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69830639373667441347036125 26186489765125290505138547)
              ·
                refine ⟨39279734647687935757707821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26186489765125290505138547 39279734647687935757707821)
                ·
                  refine ⟨14729900492882975909140433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39279734647687935757707821 14729900492882975909140433)
                  ·
                    refine ⟨11047425369662231931855325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14729900492882975909140433 11047425369662231931855325)
                    ·
                      refine ⟨4142784513623336974445747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047425369662231931855325 4142784513623336974445747)
                      ·
                        rfl

theorem cell23_8068044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_8068044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068044 prefixEnd_8068044 := by exact prefixLift 8068044
  have htrace : WordTrace (prefixWord ++ tailWord_8068044) baseStart_8068044 baseEnd_8068044 := by
    simpa [prefixWord, tailWord_8068044, baseEnd_8068044] using wordTrace_append hprefix tailTrace_8068044
  have hstable : (prefixWord ++ tailWord_8068044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068044).length < 2 ^ (prefixWord ++ tailWord_8068044).sum := by decide
  have hdescent : baseEnd_8068044 < baseStart_8068044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068061 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_8068061 : Nat := 118140960795 + 8068061 * 2 ^ 59
def prefixEnd_8068061 : Nat := 4983230072969 + 3 ^ 40 * 8068061 * 2
def baseEnd_8068061 : Nat := 4142793242794463407933169

theorem tailTrace_8068061 : CollatzResearch.WordTrace tailWord_8068061 prefixEnd_8068061 4142793242794463407933169 := by
  unfold tailWord_8068061
  simp only [CollatzResearch.WordTrace]
  refine ⟨294266359623800386962484037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196177573082533591308322691 294266359623800386962484037)
  ·
    refine ⟨55174942429462572555465757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294266359623800386962484037 55174942429462572555465757)
    ·
      refine ⟨20690603411048464708299659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55174942429462572555465757 20690603411048464708299659)
      ·
        refine ⟨31035905116572697062449489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20690603411048464708299659 31035905116572697062449489)
        ·
          refine ⟨23276928837429522796837117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31035905116572697062449489 23276928837429522796837117)
          ·
            refine ⟨8728848314036071048813919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23276928837429522796837117 8728848314036071048813919)
            ·
              refine ⟨13093272471054106573220879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728848314036071048813919 13093272471054106573220879)
              ·
                refine ⟨19639908706581159859831319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13093272471054106573220879 19639908706581159859831319)
                ·
                  refine ⟨29459863059871739789746979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19639908706581159859831319 29459863059871739789746979)
                  ·
                    refine ⟨44189794589807609684620469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29459863059871739789746979 44189794589807609684620469)
                    ·
                      refine ⟨4142793242794463407933169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44189794589807609684620469 4142793242794463407933169)
                      ·
                        rfl

theorem cell23_8068061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_8068061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068061 prefixEnd_8068061 := by exact prefixLift 8068061
  have htrace : WordTrace (prefixWord ++ tailWord_8068061) baseStart_8068061 baseEnd_8068061 := by
    simpa [prefixWord, tailWord_8068061, baseEnd_8068061] using wordTrace_append hprefix tailTrace_8068061
  have hstable : (prefixWord ++ tailWord_8068061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068061).length < 2 ^ (prefixWord ++ tailWord_8068061).sum := by decide
  have hdescent : baseEnd_8068061 < baseStart_8068061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068069 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 1, 1, 3]
def baseStart_8068069 : Nat := 118140960795 + 8068069 * 2 ^ 59
def prefixEnd_8068069 : Nat := 4983230072969 + 3 ^ 40 * 8068069 * 2
def baseEnd_8068069 : Nat := 4142797350639699376633133

theorem tailTrace_8068069 : CollatzResearch.WordTrace tailWord_8068069 prefixEnd_8068069 4142797350639699376633133 := by
  unfold tailWord_8068069
  simp only [CollatzResearch.WordTrace]
  refine ⟨294266651407771404328775261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196177767605180936219183507 294266651407771404328775261)
  ·
    refine ⟨110349994277914276623290723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294266651407771404328775261 110349994277914276623290723)
    ·
      refine ⟨165524991416871414934936085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110349994277914276623290723 165524991416871414934936085)
      ·
        refine ⟨7758983972665847575075129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165524991416871414934936085 7758983972665847575075129)
        ·
          refine ⟨5819237979499385681306347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758983972665847575075129 5819237979499385681306347)
          ·
            refine ⟨8728856969249078521959521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819237979499385681306347 8728856969249078521959521)
            ·
              refine ⟨6546642726936808891469641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8728856969249078521959521 6546642726936808891469641)
              ·
                refine ⟨4909982045202606668602231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546642726936808891469641 4909982045202606668602231)
                ·
                  refine ⟨7364973067803910002903347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909982045202606668602231 7364973067803910002903347)
                  ·
                    refine ⟨11047459601705865004355021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7364973067803910002903347 11047459601705865004355021)
                    ·
                      refine ⟨4142797350639699376633133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047459601705865004355021 4142797350639699376633133)
                      ·
                        rfl

theorem cell23_8068069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_8068069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068069 prefixEnd_8068069 := by exact prefixLift 8068069
  have htrace : WordTrace (prefixWord ++ tailWord_8068069) baseStart_8068069 baseEnd_8068069 := by
    simpa [prefixWord, tailWord_8068069, baseEnd_8068069] using wordTrace_append hprefix tailTrace_8068069
  have hstable : (prefixWord ++ tailWord_8068069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068069).length < 2 ^ (prefixWord ++ tailWord_8068069).sum := by decide
  have hdescent : baseEnd_8068069 < baseStart_8068069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068098 : List Nat := [3, 4, 1, 3, 1, 1, 3, 7]
def baseStart_8068098 : Nat := 118140960795 + 8068098 * 2 ^ 59
def prefixEnd_8068098 : Nat := 4983230072969 + 3 ^ 40 * 8068098 * 2
def baseEnd_8068098 : Nat := 153437490428839991228537

theorem tailTrace_8068098 : CollatzResearch.WordTrace tailWord_8068098 prefixEnd_8068098 153437490428839991228537 := by
  unfold tailWord_8068098
  simp only [CollatzResearch.WordTrace]
  refine ⟨73566927281166585570395237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196178472749777561521053965 73566927281166585570395237)
  ·
    refine ⟨13793798865218734794449107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73566927281166585570395237 13793798865218734794449107)
    ·
      refine ⟨20690698297828102191673661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13793798865218734794449107 20690698297828102191673661)
      ·
        refine ⟨7759011861685538321877623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20690698297828102191673661 7759011861685538321877623)
        ·
          refine ⟨11638517792528307482816435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759011861685538321877623 11638517792528307482816435)
          ·
            refine ⟨17457776688792461224224653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638517792528307482816435 17457776688792461224224653)
            ·
              refine ⟨6546666258297172959084245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17457776688792461224224653 6546666258297172959084245)
              ·
                refine ⟨153437490428839991228537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6546666258297172959084245 153437490428839991228537)
                ·
                  rfl

theorem cell23_8068098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_8068098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068098 prefixEnd_8068098 := by exact prefixLift 8068098
  have htrace : WordTrace (prefixWord ++ tailWord_8068098) baseStart_8068098 baseEnd_8068098 := by
    simpa [prefixWord, tailWord_8068098, baseEnd_8068098] using wordTrace_append hprefix tailTrace_8068098
  have hstable : (prefixWord ++ tailWord_8068098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068098).length < 2 ^ (prefixWord ++ tailWord_8068098).sum := by decide
  have hdescent : baseEnd_8068098 < baseStart_8068098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068101 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 1, 3, 2]
def baseStart_8068101 : Nat := 118140960795 + 8068101 * 2 ^ 59
def prefixEnd_8068101 : Nat := 4983230072969 + 3 ^ 40 * 8068101 * 2
def baseEnd_8068101 : Nat := 4142813782020643251432985

theorem tailTrace_8068101 : CollatzResearch.WordTrace tailWord_8068101 prefixEnd_8068101 4142813782020643251432985 := by
  unfold tailWord_8068101
  simp only [CollatzResearch.WordTrace]
  refine ⟨294267818543655473793940157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196178545695770315862626771 294267818543655473793940157)
  ·
    refine ⟨110350431953870802672727559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294267818543655473793940157 110350431953870802672727559)
    ·
      refine ⟨165525647930806204009091339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110350431953870802672727559 165525647930806204009091339)
      ·
        refine ⟨248288471896209306013637009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165525647930806204009091339 248288471896209306013637009)
        ·
          refine ⟨186216353922156979510227757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248288471896209306013637009 186216353922156979510227757)
          ·
            refine ⟨69831132720808867316335409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186216353922156979510227757 69831132720808867316335409)
            ·
              refine ⟨52373349540606650487251557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69831132720808867316335409 52373349540606650487251557)
              ·
                refine ⟨9820003038863746966359667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52373349540606650487251557 9820003038863746966359667)
                ·
                  refine ⟨14730004558295620449539501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820003038863746966359667 14730004558295620449539501)
                  ·
                    refine ⟨5523751709360857668577313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14730004558295620449539501 5523751709360857668577313)
                    ·
                      refine ⟨4142813782020643251432985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523751709360857668577313 4142813782020643251432985)
                      ·
                        rfl

theorem cell23_8068101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_8068101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068101 prefixEnd_8068101 := by exact prefixLift 8068101
  have htrace : WordTrace (prefixWord ++ tailWord_8068101) baseStart_8068101 baseEnd_8068101 := by
    simpa [prefixWord, tailWord_8068101, baseEnd_8068101] using wordTrace_append hprefix tailTrace_8068101
  have hstable : (prefixWord ++ tailWord_8068101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068101).length < 2 ^ (prefixWord ++ tailWord_8068101).sum := by decide
  have hdescent : baseEnd_8068101 < baseStart_8068101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068125 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_8068125 : Nat := 118140960795 + 8068125 * 2 ^ 59
def prefixEnd_8068125 : Nat := 4983230072969 + 3 ^ 40 * 8068125 * 2
def baseEnd_8068125 : Nat := 4142826105556351157532875

theorem tailTrace_8068125 : CollatzResearch.WordTrace tailWord_8068125 prefixEnd_8068125 4142826105556351157532875 := by
  unfold tailWord_8068125
  simp only [CollatzResearch.WordTrace]
  refine ⟨294268693895568525892813829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196179129263712350595209219 294268693895568525892813829)
  ·
    refine ⟨55175380105419098604902593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294268693895568525892813829 55175380105419098604902593)
    ·
      refine ⟨41381535079064323953676945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55175380105419098604902593 41381535079064323953676945)
      ·
        refine ⟨31036151309298242965257709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41381535079064323953676945 31036151309298242965257709)
        ·
          refine ⟨11638556740986841111971641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31036151309298242965257709 11638556740986841111971641)
          ·
            refine ⟨8728917555740130833978731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11638556740986841111971641 8728917555740130833978731)
            ·
              refine ⟨13093376333610196250968097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728917555740130833978731 13093376333610196250968097)
              ·
                refine ⟨9820032250207647188226073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093376333610196250968097 9820032250207647188226073)
                ·
                  refine ⟨7365024187655735391169555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9820032250207647188226073 7365024187655735391169555)
                  ·
                    refine ⟨11047536281483603086754333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7365024187655735391169555 11047536281483603086754333)
                    ·
                      refine ⟨4142826105556351157532875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047536281483603086754333 4142826105556351157532875)
                      ·
                        rfl

theorem cell23_8068125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_8068125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068125 prefixEnd_8068125 := by exact prefixLift 8068125
  have htrace : WordTrace (prefixWord ++ tailWord_8068125) baseStart_8068125 baseEnd_8068125 := by
    simpa [prefixWord, tailWord_8068125, baseEnd_8068125] using wordTrace_append hprefix tailTrace_8068125
  have hstable : (prefixWord ++ tailWord_8068125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068125).length < 2 ^ (prefixWord ++ tailWord_8068125).sum := by decide
  have hdescent : baseEnd_8068125 < baseStart_8068125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068184 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_8068184 : Nat := 118140960795 + 8068184 * 2 ^ 59
def prefixEnd_8068184 : Nat := 4983230072969 + 3 ^ 40 * 8068184 * 2
def baseEnd_8068184 : Nat := 1380952133638322142231701

theorem tailTrace_8068184 : CollatzResearch.WordTrace tailWord_8068184 prefixEnd_8068184 1380952133638322142231701 := by
  unfold tailWord_8068184
  simp only [CollatzResearch.WordTrace]
  refine ⟨147135422901177389484605803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196180563868236519312807737 147135422901177389484605803)
  ·
    refine ⟨220703134351766084226908705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147135422901177389484605803 220703134351766084226908705)
    ·
      refine ⟨165527350763824563170181529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220703134351766084226908705 165527350763824563170181529)
      ·
        refine ⟨124145513072868422377636147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165527350763824563170181529 124145513072868422377636147)
        ·
          refine ⟨186218269609302633566454221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124145513072868422377636147 186218269609302633566454221)
          ·
            refine ⟨69831851103488487587420333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186218269609302633566454221 69831851103488487587420333)
            ·
              refine ⟨26186944163808182845282625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69831851103488487587420333 26186944163808182845282625)
              ·
                refine ⟨19640208122856137133961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26186944163808182845282625 19640208122856137133961969)
                ·
                  refine ⟨14730156092142102850471477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19640208122856137133961969 14730156092142102850471477)
                  ·
                    refine ⟨1380952133638322142231701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14730156092142102850471477 1380952133638322142231701)
                    ·
                      rfl

theorem cell23_8068184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_8068184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068184 prefixEnd_8068184 := by exact prefixLift 8068184
  have htrace : WordTrace (prefixWord ++ tailWord_8068184) baseStart_8068184 baseEnd_8068184 := by
    simpa [prefixWord, tailWord_8068184, baseEnd_8068184] using wordTrace_append hprefix tailTrace_8068184
  have hstable : (prefixWord ++ tailWord_8068184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068184).length < 2 ^ (prefixWord ++ tailWord_8068184).sum := by decide
  have hdescent : baseEnd_8068184 < baseStart_8068184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068188 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 5]
def baseStart_8068188 : Nat := 118140960795 + 8068188 * 2 ^ 59
def prefixEnd_8068188 : Nat := 4983230072969 + 3 ^ 40 * 8068188 * 2
def baseEnd_8068188 : Nat := 460317606093064934560565

theorem tailTrace_8068188 : CollatzResearch.WordTrace tailWord_8068188 prefixEnd_8068188 460317606093064934560565 := by
  unfold tailWord_8068188
  simp only [CollatzResearch.WordTrace]
  refine ⟨147135495847170143826178609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196180661129560191768238145 147135495847170143826178609)
  ·
    refine ⟨110351621885377607869633957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147135495847170143826178609 110351621885377607869633957)
    ·
      refine ⟨20690929103508301475556367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110351621885377607869633957 20690929103508301475556367)
      ·
        refine ⟨31036393655262452213334551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20690929103508301475556367 31036393655262452213334551)
        ·
          refine ⟨46554590482893678320001827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31036393655262452213334551 46554590482893678320001827)
          ·
            refine ⟨69831885724340517480002741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46554590482893678320001827 69831885724340517480002741)
            ·
              refine ⟨6546739286656923513750257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69831885724340517480002741 6546739286656923513750257)
              ·
                refine ⟨4910054464992692635312693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546739286656923513750257 4910054464992692635312693)
                ·
                  refine ⟨460317606093064934560565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4910054464992692635312693 460317606093064934560565)
                  ·
                    rfl

theorem cell23_8068188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_8068188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068188 prefixEnd_8068188 := by exact prefixLift 8068188
  have htrace : WordTrace (prefixWord ++ tailWord_8068188) baseStart_8068188 baseEnd_8068188 := by
    simpa [prefixWord, tailWord_8068188, baseEnd_8068188] using wordTrace_append hprefix tailTrace_8068188
  have hstable : (prefixWord ++ tailWord_8068188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068188).length < 2 ^ (prefixWord ++ tailWord_8068188).sum := by decide
  have hdescent : baseEnd_8068188 < baseStart_8068188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068204 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_8068204 : Nat := 118140960795 + 8068204 * 2 ^ 59
def prefixEnd_8068204 : Nat := 4983230072969 + 3 ^ 40 * 8068204 * 2
def baseEnd_8068204 : Nat := 4142866670528056348445011

theorem tailTrace_8068204 : CollatzResearch.WordTrace tailWord_8068204 prefixEnd_8068204 4142866670528056348445011 := by
  unfold tailWord_8068204
  simp only [CollatzResearch.WordTrace]
  refine ⟨147135787631141161192469833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196181050174854881589959777 147135787631141161192469833)
  ·
    refine ⟨110351840723355870894352375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147135787631141161192469833 110351840723355870894352375)
    ·
      refine ⟨165527761085033806341528563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110351840723355870894352375 165527761085033806341528563)
      ·
        refine ⟨248291641627550709512292845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165527761085033806341528563 248291641627550709512292845)
        ·
          refine ⟨93109365610331516067109817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248291641627550709512292845 93109365610331516067109817)
          ·
            refine ⟨69832024207748637050332363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93109365610331516067109817 69832024207748637050332363)
            ·
              refine ⟨104748036311622955575498545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69832024207748637050332363 104748036311622955575498545)
              ·
                refine ⟨78561027233717216681623909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104748036311622955575498545 78561027233717216681623909)
                ·
                  refine ⟨14730192606321978127804483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78561027233717216681623909 14730192606321978127804483)
                  ·
                    refine ⟨22095288909482967191706725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14730192606321978127804483 22095288909482967191706725)
                    ·
                      refine ⟨4142866670528056348445011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22095288909482967191706725 4142866670528056348445011)
                      ·
                        rfl

theorem cell23_8068204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_8068204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068204 prefixEnd_8068204 := by exact prefixLift 8068204
  have htrace : WordTrace (prefixWord ++ tailWord_8068204) baseStart_8068204 baseEnd_8068204 := by
    simpa [prefixWord, tailWord_8068204, baseEnd_8068204] using wordTrace_append hprefix tailTrace_8068204
  have hstable : (prefixWord ++ tailWord_8068204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068204).length < 2 ^ (prefixWord ++ tailWord_8068204).sum := by decide
  have hdescent : baseEnd_8068204 < baseStart_8068204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068221 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_8068221 : Nat := 118140960795 + 8068221 * 2 ^ 59
def prefixEnd_8068221 : Nat := 4983230072969 + 3 ^ 40 * 8068221 * 2
def baseEnd_8068221 : Nat := 4142875399699182781932433

theorem tailTrace_8068221 : CollatzResearch.WordTrace tailWord_8068221 prefixEnd_8068221 4142875399699182781932433 := by
  unfold tailWord_8068221
  simp only [CollatzResearch.WordTrace]
  refine ⟨294272195303220734288308517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196181463535480489525539011 294272195303220734288308517)
  ·
    refine ⟨55176036619353887679057847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294272195303220734288308517 55176036619353887679057847)
    ·
      refine ⟨82764054929030831518586771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55176036619353887679057847 82764054929030831518586771)
      ·
        refine ⟨124146082393546247277880157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82764054929030831518586771 124146082393546247277880157)
        ·
          refine ⟨46554780897579842729205059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124146082393546247277880157 46554780897579842729205059)
          ·
            refine ⟨69832171346369764093807589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46554780897579842729205059 69832171346369764093807589)
            ·
              refine ⟨13093532127444330767588923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69832171346369764093807589 13093532127444330767588923)
              ·
                refine ⟨19640298191166496151383385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13093532127444330767588923 19640298191166496151383385)
                ·
                  refine ⟨14730223643374872113537539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19640298191166496151383385 14730223643374872113537539)
                  ·
                    refine ⟨22095335465062308170306309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14730223643374872113537539 22095335465062308170306309)
                    ·
                      refine ⟨4142875399699182781932433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22095335465062308170306309 4142875399699182781932433)
                      ·
                        rfl

theorem cell23_8068221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_8068221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068221 prefixEnd_8068221 := by exact prefixLift 8068221
  have htrace : WordTrace (prefixWord ++ tailWord_8068221) baseStart_8068221 baseEnd_8068221 := by
    simpa [prefixWord, tailWord_8068221, baseEnd_8068221] using wordTrace_append hprefix tailTrace_8068221
  have hstable : (prefixWord ++ tailWord_8068221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068221).length < 2 ^ (prefixWord ++ tailWord_8068221).sum := by decide
  have hdescent : baseEnd_8068221 < baseStart_8068221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068224 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_8068224 : Nat := 118140960795 + 8068224 * 2 ^ 59
def prefixEnd_8068224 : Nat := 4983230072969 + 3 ^ 40 * 8068224 * 2
def baseEnd_8068224 : Nat := 4142876940141146270194919

theorem tailTrace_8068224 : CollatzResearch.WordTrace tailWord_8068224 prefixEnd_8068224 4142876940141146270194919 := by
  unfold tailWord_8068224
  simp only [CollatzResearch.WordTrace]
  refine ⟨147136152361104932900333863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196181536481473243867111817 147136152361104932900333863)
  ·
    refine ⟨220704228541657399350500795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147136152361104932900333863 220704228541657399350500795)
    ·
      refine ⟨331056342812486099025751193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220704228541657399350500795 331056342812486099025751193)
      ·
        refine ⟨248292257109364574269313395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331056342812486099025751193 248292257109364574269313395)
        ·
          refine ⟨372438385664046861403970093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248292257109364574269313395 372438385664046861403970093)
          ·
            refine ⟨139664394624017573026488785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372438385664046861403970093 139664394624017573026488785)
            ·
              refine ⟨104748295968013179769866589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139664394624017573026488785 104748295968013179769866589)
              ·
                refine ⟨39280610988004942413699971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104748295968013179769866589 39280610988004942413699971)
                ·
                  refine ⟨58920916482007413620549957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39280610988004942413699971 58920916482007413620549957)
                  ·
                    refine ⟨11047671840376390053853117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58920916482007413620549957 11047671840376390053853117)
                    ·
                      refine ⟨4142876940141146270194919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047671840376390053853117 4142876940141146270194919)
                      ·
                        rfl

theorem cell23_8068224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_8068224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068224 prefixEnd_8068224 := by exact prefixLift 8068224
  have htrace : WordTrace (prefixWord ++ tailWord_8068224) baseStart_8068224 baseEnd_8068224 := by
    simpa [prefixWord, tailWord_8068224, baseEnd_8068224] using wordTrace_append hprefix tailTrace_8068224
  have hstable : (prefixWord ++ tailWord_8068224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068224).length < 2 ^ (prefixWord ++ tailWord_8068224).sum := by decide
  have hdescent : baseEnd_8068224 < baseStart_8068224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068234 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_8068234 : Nat := 118140960795 + 8068234 * 2 ^ 59
def prefixEnd_8068234 : Nat := 4983230072969 + 3 ^ 40 * 8068234 * 2
def baseEnd_8068234 : Nat := 4142882074947691231069873

theorem tailTrace_8068234 : CollatzResearch.WordTrace tailWord_8068234 prefixEnd_8068234 4142882074947691231069873 := by
  unfold tailWord_8068234
  simp only [CollatzResearch.WordTrace]
  refine ⟨73568167363043409377132939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196181779634782425005687837 73568167363043409377132939)
  ·
    refine ⟨110352251044565114065699409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73568167363043409377132939 110352251044565114065699409)
    ·
      refine ⟨82764188283423835549274557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110352251044565114065699409 82764188283423835549274557)
      ·
        refine ⟨31036570606283938330977959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82764188283423835549274557 31036570606283938330977959)
        ·
          refine ⟨46554855909425907496466939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31036570606283938330977959 46554855909425907496466939)
          ·
            refine ⟨69832283864138861244700409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46554855909425907496466939 69832283864138861244700409)
            ·
              refine ⟨52374212898104145933525307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69832283864138861244700409 52374212898104145933525307)
              ·
                refine ⟨78561319347156218900287961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52374212898104145933525307 78561319347156218900287961)
                ·
                  refine ⟨58920989510367164175215971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78561319347156218900287961 58920989510367164175215971)
                  ·
                    refine ⟨88381484265550746262823957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58920989510367164175215971 88381484265550746262823957)
                    ·
                      refine ⟨4142882074947691231069873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88381484265550746262823957 4142882074947691231069873)
                      ·
                        rfl

theorem cell23_8068234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_8068234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068234 prefixEnd_8068234 := by exact prefixLift 8068234
  have htrace : WordTrace (prefixWord ++ tailWord_8068234) baseStart_8068234 baseEnd_8068234 := by
    simpa [prefixWord, tailWord_8068234, baseEnd_8068234] using wordTrace_append hprefix tailTrace_8068234
  have hstable : (prefixWord ++ tailWord_8068234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068234).length < 2 ^ (prefixWord ++ tailWord_8068234).sum := by decide
  have hdescent : baseEnd_8068234 < baseStart_8068234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068271 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 3]
def baseStart_8068271 : Nat := 118140960795 + 8068271 * 2 ^ 59
def prefixEnd_8068271 : Nat := 4983230072969 + 3 ^ 40 * 8068271 * 2
def baseEnd_8068271 : Nat := 4142901073731907586307203

theorem tailTrace_8068271 : CollatzResearch.WordTrace tailWord_8068271 prefixEnd_8068271 4142901073731907586307203 := by
  unfold tailWord_8068271
  simp only [CollatzResearch.WordTrace]
  refine ⟨294274018953039592827628667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196182679302026395218419111 294274018953039592827628667)
  ·
    refine ⟨441411028429559389241443001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294274018953039592827628667 441411028429559389241443001)
    ·
      refine ⟨331058271322169541931082251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441411028429559389241443001 331058271322169541931082251)
      ·
        refine ⟨496587406983254312896623377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331058271322169541931082251 496587406983254312896623377)
        ·
          refine ⟨372440555237440734672467533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496587406983254312896623377 372440555237440734672467533)
          ·
            refine ⟨139665208214040275502175325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372440555237440734672467533 139665208214040275502175325)
            ·
              refine ⟨52374453080265103313315747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139665208214040275502175325 52374453080265103313315747)
              ·
                refine ⟨78561679620397654969973621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52374453080265103313315747 78561679620397654969973621)
                ·
                  refine ⟨7365157464412280153435027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78561679620397654969973621 7365157464412280153435027)
                  ·
                    refine ⟨11047736196618420230152541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7365157464412280153435027 11047736196618420230152541)
                    ·
                      refine ⟨4142901073731907586307203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047736196618420230152541 4142901073731907586307203)
                      ·
                        rfl

theorem cell23_8068271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_8068271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068271 prefixEnd_8068271 := by exact prefixLift 8068271
  have htrace : WordTrace (prefixWord ++ tailWord_8068271) baseStart_8068271 baseEnd_8068271 := by
    simpa [prefixWord, tailWord_8068271, baseEnd_8068271] using wordTrace_append hprefix tailTrace_8068271
  have hstable : (prefixWord ++ tailWord_8068271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068271).length < 2 ^ (prefixWord ++ tailWord_8068271).sum := by decide
  have hdescent : baseEnd_8068271 < baseStart_8068271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068321 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 1, 6]
def baseStart_8068321 : Nat := 118140960795 + 8068321 * 2 ^ 59
def prefixEnd_8068321 : Nat := 4983230072969 + 3 ^ 40 * 8068321 * 2
def baseEnd_8068321 : Nat := 1380975582588210796893991

theorem tailTrace_8068321 : CollatzResearch.WordTrace tailWord_8068321 prefixEnd_8068321 1380975582588210796893991 := by
  unfold tailWord_8068321
  simp only [CollatzResearch.WordTrace]
  refine ⟨294275842602858451366948817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196183895068572300911299211 294275842602858451366948817)
  ·
    refine ⟨220706881952143838525211613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294275842602858451366948817 220706881952143838525211613)
    ·
      refine ⟨82765080732053939446954355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220706881952143838525211613 82765080732053939446954355)
      ·
        refine ⟨124147621098080909170431533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82765080732053939446954355 124147621098080909170431533)
        ·
          refine ⟨46555357911780340938911825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124147621098080909170431533 46555357911780340938911825)
          ·
            refine ⟨34916518433835255704183869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46555357911780340938911825 34916518433835255704183869)
            ·
              refine ⟨13093694412688220889068951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34916518433835255704183869 13093694412688220889068951)
              ·
                refine ⟨19640541619032331333603427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13093694412688220889068951 19640541619032331333603427)
                ·
                  refine ⟨29460812428548497000405141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19640541619032331333603427 29460812428548497000405141)
                  ·
                    refine ⟨1380975582588210796893991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29460812428548497000405141 1380975582588210796893991)
                    ·
                      rfl

theorem cell23_8068321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_8068321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068321 prefixEnd_8068321 := by exact prefixLift 8068321
  have htrace : WordTrace (prefixWord ++ tailWord_8068321) baseStart_8068321 baseEnd_8068321 := by
    simpa [prefixWord, tailWord_8068321, baseEnd_8068321] using wordTrace_append hprefix tailTrace_8068321
  have hstable : (prefixWord ++ tailWord_8068321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068321).length < 2 ^ (prefixWord ++ tailWord_8068321).sum := by decide
  have hdescent : baseEnd_8068321 < baseStart_8068321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068328 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_8068328 : Nat := 118140960795 + 8068328 * 2 ^ 59
def prefixEnd_8068328 : Nat := 4983230072969 + 3 ^ 40 * 8068328 * 2
def baseEnd_8068328 : Nat := 4142930342129213863294441

theorem tailTrace_8068328 : CollatzResearch.WordTrace tailWord_8068328 prefixEnd_8068328 4142930342129213863294441 := by
  unfold tailWord_8068328
  simp only [CollatzResearch.WordTrace]
  refine ⟨147138048956916545781226819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196184065275888727708302425 147138048956916545781226819)
  ·
    refine ⟨220707073435374818671840229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147138048956916545781226819 220707073435374818671840229)
    ·
      refine ⟨41382576269132778500970043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220707073435374818671840229 41382576269132778500970043)
      ·
        refine ⟨62073864403699167751455065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41382576269132778500970043 62073864403699167751455065)
        ·
          refine ⟨46555398302774375813591299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62073864403699167751455065 46555398302774375813591299)
          ·
            refine ⟨69833097454161563720386949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46555398302774375813591299 69833097454161563720386949)
            ·
              refine ⟨13093705772655293197572553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69833097454161563720386949 13093705772655293197572553)
              ·
                refine ⟨9820279329491469898179415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093705772655293197572553 9820279329491469898179415)
                ·
                  refine ⟨14730418994237204847269123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820279329491469898179415 14730418994237204847269123)
                  ·
                    refine ⟨22095628491355807270903685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14730418994237204847269123 22095628491355807270903685)
                    ·
                      refine ⟨4142930342129213863294441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22095628491355807270903685 4142930342129213863294441)
                      ·
                        rfl

theorem cell23_8068328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_8068328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068328 prefixEnd_8068328 := by exact prefixLift 8068328
  have htrace : WordTrace (prefixWord ++ tailWord_8068328) baseStart_8068328 baseEnd_8068328 := by
    simpa [prefixWord, tailWord_8068328, baseEnd_8068328] using wordTrace_append hprefix tailTrace_8068328
  have hstable : (prefixWord ++ tailWord_8068328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068328).length < 2 ^ (prefixWord ++ tailWord_8068328).sum := by decide
  have hdescent : baseEnd_8068328 < baseStart_8068328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068348 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_8068348 : Nat := 118140960795 + 8068348 * 2 ^ 59
def prefixEnd_8068348 : Nat := 4983230072969 + 3 ^ 40 * 8068348 * 2
def baseEnd_8068348 : Nat := 4142940611742303785044349

theorem tailTrace_8068348 : CollatzResearch.WordTrace tailWord_8068348 prefixEnd_8068348 4142940611742303785044349 := by
  unfold tailWord_8068348
  simp only [CollatzResearch.WordTrace]
  refine ⟨147138413686880317489090849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196184551582507089985454465 147138413686880317489090849)
  ·
    refine ⟨110353810265160238116818137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147138413686880317489090849 110353810265160238116818137)
    ·
      refine ⟨82765357698870178587613603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110353810265160238116818137 82765357698870178587613603)
      ·
        refine ⟨124148036548305267881420405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82765357698870178587613603 124148036548305267881420405)
        ·
          refine ⟨11638878426403618863883163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124148036548305267881420405 11638878426403618863883163)
          ·
            refine ⟨17458317639605428295824745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638878426403618863883163 17458317639605428295824745)
            ·
              refine ⟨13093738229704071221868559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17458317639605428295824745 13093738229704071221868559)
              ·
                refine ⟨19640607344556106832802839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13093738229704071221868559 19640607344556106832802839)
                ·
                  refine ⟨29460911016834160249204259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19640607344556106832802839 29460911016834160249204259)
                  ·
                    refine ⟨44191366525251240373806389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29460911016834160249204259 44191366525251240373806389)
                    ·
                      refine ⟨4142940611742303785044349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44191366525251240373806389 4142940611742303785044349)
                      ·
                        rfl

theorem cell23_8068348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_8068348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068348 prefixEnd_8068348 := by exact prefixLift 8068348
  have htrace : WordTrace (prefixWord ++ tailWord_8068348) baseStart_8068348 baseEnd_8068348 := by
    simpa [prefixWord, tailWord_8068348, baseEnd_8068348] using wordTrace_append hprefix tailTrace_8068348
  have hstable : (prefixWord ++ tailWord_8068348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068348).length < 2 ^ (prefixWord ++ tailWord_8068348).sum := by decide
  have hdescent : baseEnd_8068348 < baseStart_8068348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068371 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 9, 2]
def baseStart_8068371 : Nat := 118140960795 + 8068371 * 2 ^ 59
def prefixEnd_8068371 : Nat := 4983230072969 + 3 ^ 40 * 8068371 * 2
def baseEnd_8068371 : Nat := 4142952421797357195056743

theorem tailTrace_8068371 : CollatzResearch.WordTrace tailWord_8068371 prefixEnd_8068371 4142952421797357195056743 := by
  unfold tailWord_8068371
  simp only [CollatzResearch.WordTrace]
  refine ⟨294277666252677309906268967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196185110835118206604179311 294277666252677309906268967)
  ·
    refine ⟨441416499379015964859403451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294277666252677309906268967 441416499379015964859403451)
    ·
      refine ⟨662124749068523947289105177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441416499379015964859403451 662124749068523947289105177)
      ·
        refine ⟨496593561801392960466828883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662124749068523947289105177 496593561801392960466828883)
        ·
          refine ⟨744890342702089440700243325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496593561801392960466828883 744890342702089440700243325)
          ·
            refine ⟨279333878513283540262591247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744890342702089440700243325 279333878513283540262591247)
            ·
              refine ⟨419000817769925310393886871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279333878513283540262591247 419000817769925310393886871)
              ·
                refine ⟨628501226654887965590830307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419000817769925310393886871 628501226654887965590830307)
                ·
                  refine ⟨942751839982331948386245461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628501226654887965590830307 942751839982331948386245461)
                  ·
                    refine ⟨5523936562396476260075657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 942751839982331948386245461 5523936562396476260075657)
                    ·
                      refine ⟨4142952421797357195056743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523936562396476260075657 4142952421797357195056743)
                      ·
                        rfl

theorem cell23_8068371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9, 2].length) (baseStart_8068371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068371 prefixEnd_8068371 := by exact prefixLift 8068371
  have htrace : WordTrace (prefixWord ++ tailWord_8068371) baseStart_8068371 baseEnd_8068371 := by
    simpa [prefixWord, tailWord_8068371, baseEnd_8068371] using wordTrace_append hprefix tailTrace_8068371
  have hstable : (prefixWord ++ tailWord_8068371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068371).length < 2 ^ (prefixWord ++ tailWord_8068371).sum := by decide
  have hdescent : baseEnd_8068371 < baseStart_8068371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068382 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_8068382 : Nat := 118140960795 + 8068382 * 2 ^ 59
def prefixEnd_8068382 : Nat := 4983230072969 + 3 ^ 40 * 8068382 * 2
def baseEnd_8068382 : Nat := 4142958070084556652019193

theorem tailTrace_8068382 : CollatzResearch.WordTrace tailWord_8068382 prefixEnd_8068382 4142958070084556652019193 := by
  unfold tailWord_8068382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36784758431954682348114925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196185378303758305856612933 36784758431954682348114925)
  ·
    refine ⟨13794284411983005880543097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36784758431954682348114925 13794284411983005880543097)
    ·
      refine ⟨10345713308987254410407323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13794284411983005880543097 10345713308987254410407323)
      ·
        refine ⟨15518569963480881615610985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10345713308987254410407323 15518569963480881615610985)
        ·
          refine ⟨11638927472610661211708239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15518569963480881615610985 11638927472610661211708239)
          ·
            refine ⟨17458391208915991817562359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638927472610661211708239 17458391208915991817562359)
            ·
              refine ⟨26187586813373987726343539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458391208915991817562359 26187586813373987726343539)
              ·
                refine ⟨39281380220060981589515309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26187586813373987726343539 39281380220060981589515309)
                ·
                  refine ⟨14730517582522868096068241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39281380220060981589515309 14730517582522868096068241)
                  ·
                    refine ⟨11047888186892151072051181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14730517582522868096068241 11047888186892151072051181)
                    ·
                      refine ⟨4142958070084556652019193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11047888186892151072051181 4142958070084556652019193)
                      ·
                        rfl

theorem cell23_8068382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_8068382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068382 prefixEnd_8068382 := by exact prefixLift 8068382
  have htrace : WordTrace (prefixWord ++ tailWord_8068382) baseStart_8068382 baseEnd_8068382 := by
    simpa [prefixWord, tailWord_8068382, baseEnd_8068382] using wordTrace_append hprefix tailTrace_8068382
  have hstable : (prefixWord ++ tailWord_8068382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068382).length < 2 ^ (prefixWord ++ tailWord_8068382).sum := by decide
  have hdescent : baseEnd_8068382 < baseStart_8068382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068413 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8068413 : Nat := 118140960795 + 8068413 * 2 ^ 59
def prefixEnd_8068413 : Nat := 4983230072969 + 3 ^ 40 * 8068413 * 2
def baseEnd_8068413 : Nat := 4142973987984846030731551

theorem tailTrace_8068413 : CollatzResearch.WordTrace tailWord_8068413 prefixEnd_8068413 4142973987984846030731551 := by
  unfold tailWord_8068413
  simp only [CollatzResearch.WordTrace]
  refine ⟨294279198118525151079297893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196186132079016767386198595 294279198118525151079297893)
  ·
    refine ⟨55177349647223465827368355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294279198118525151079297893 55177349647223465827368355)
    ·
      refine ⟨82766024470835198741052533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55177349647223465827368355 82766024470835198741052533)
      ·
        refine ⟨7759314794140799881973675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82766024470835198741052533 7759314794140799881973675)
        ·
          refine ⟨11638972191211199822960513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759314794140799881973675 11638972191211199822960513)
          ·
            refine ⟨8729229143408399867220385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11638972191211199822960513 8729229143408399867220385)
            ·
              refine ⟨6546921857556299900415289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8729229143408399867220385 6546921857556299900415289)
              ·
                refine ⟨4910191393167224925311467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546921857556299900415289 4910191393167224925311467)
                ·
                  refine ⟨7365287089750837387967201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910191393167224925311467 7365287089750837387967201)
                  ·
                    refine ⟨5523965317313128040975401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365287089750837387967201 5523965317313128040975401)
                    ·
                      refine ⟨4142973987984846030731551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523965317313128040975401 4142973987984846030731551)
                      ·
                        rfl

theorem cell23_8068413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8068413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068413 prefixEnd_8068413 := by exact prefixLift 8068413
  have htrace : WordTrace (prefixWord ++ tailWord_8068413) baseStart_8068413 baseEnd_8068413 := by
    simpa [prefixWord, tailWord_8068413, baseEnd_8068413] using wordTrace_append hprefix tailTrace_8068413
  have hstable : (prefixWord ++ tailWord_8068413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068413).length < 2 ^ (prefixWord ++ tailWord_8068413).sum := by decide
  have hdescent : baseEnd_8068413 < baseStart_8068413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068435 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 2, 2, 2]
def baseStart_8068435 : Nat := 118140960795 + 8068435 * 2 ^ 59
def prefixEnd_8068435 : Nat := 4983230072969 + 3 ^ 40 * 8068435 * 2
def baseEnd_8068435 : Nat := 4142985284559244944656449

theorem tailTrace_8068435 : CollatzResearch.WordTrace tailWord_8068435 prefixEnd_8068435 4142985284559244944656449 := by
  unfold tailWord_8068435
  simp only [CollatzResearch.WordTrace]
  refine ⟨294280000524445448836598759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196186667016296965891065839 294280000524445448836598759)
  ·
    refine ⟨441420000786668173254898139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294280000524445448836598759 441420000786668173254898139)
    ·
      refine ⟨662130001180002259882347209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441420000786668173254898139 662130001180002259882347209)
      ·
        refine ⟨496597500885001694911760407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662130001180002259882347209 496597500885001694911760407)
        ·
          refine ⟨744896251327502542367640611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496597500885001694911760407 744896251327502542367640611)
          ·
            refine ⟨1117344376991253813551460917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744896251327502542367640611 1117344376991253813551460917)
            ·
              refine ⟨104751035342930045020449461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1117344376991253813551460917 104751035342930045020449461)
              ·
                refine ⟨9820409563399691720667137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104751035342930045020449461 9820409563399691720667137)
                ·
                  refine ⟨7365307172549768790500353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9820409563399691720667137 7365307172549768790500353)
                  ·
                    refine ⟨5523980379412326592875265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365307172549768790500353 5523980379412326592875265)
                    ·
                      refine ⟨4142985284559244944656449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523980379412326592875265 4142985284559244944656449)
                      ·
                        rfl

theorem cell23_8068435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 2, 2].length) (baseStart_8068435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068435 prefixEnd_8068435 := by exact prefixLift 8068435
  have htrace : WordTrace (prefixWord ++ tailWord_8068435) baseStart_8068435 baseEnd_8068435 := by
    simpa [prefixWord, tailWord_8068435, baseEnd_8068435] using wordTrace_append hprefix tailTrace_8068435
  have hstable : (prefixWord ++ tailWord_8068435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068435).length < 2 ^ (prefixWord ++ tailWord_8068435).sum := by decide
  have hdescent : baseEnd_8068435 < baseStart_8068435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068456 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_8068456 : Nat := 118140960795 + 8068456 * 2 ^ 59
def prefixEnd_8068456 : Nat := 4983230072969 + 3 ^ 40 * 8068456 * 2
def baseEnd_8068456 : Nat := 4142996067652989362493853

theorem tailTrace_8068456 : CollatzResearch.WordTrace tailWord_8068456 prefixEnd_8068456 4142996067652989362493853 := by
  unfold tailWord_8068456
  simp only [CollatzResearch.WordTrace]
  refine ⟨147140383228684684711556611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196187177638246246282075481 147140383228684684711556611)
  ·
    refine ⟨220710574843027027067334917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147140383228684684711556611 220710574843027027067334917)
    ·
      refine ⟨41383232783067567575125297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220710574843027027067334917 41383232783067567575125297)
      ·
        refine ⟨31037424587300675681343973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41383232783067567575125297 31037424587300675681343973)
        ·
          refine ⟨5819517110118876690251995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31037424587300675681343973 5819517110118876690251995)
          ·
            refine ⟨8729275665178315035377993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819517110118876690251995 8729275665178315035377993)
            ·
              refine ⟨6546956748883736276533495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8729275665178315035377993 6546956748883736276533495)
              ·
                refine ⟨9820435123325604414800243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546956748883736276533495 9820435123325604414800243)
                ·
                  refine ⟨14730652684988406622200365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820435123325604414800243 14730652684988406622200365)
                  ·
                    refine ⟨5523994756870652483325137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14730652684988406622200365 5523994756870652483325137)
                    ·
                      refine ⟨4142996067652989362493853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5523994756870652483325137 4142996067652989362493853)
                      ·
                        rfl

theorem cell23_8068456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_8068456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068456 prefixEnd_8068456 := by exact prefixLift 8068456
  have htrace : WordTrace (prefixWord ++ tailWord_8068456) baseStart_8068456 baseEnd_8068456 := by
    simpa [prefixWord, tailWord_8068456, baseEnd_8068456] using wordTrace_append hprefix tailTrace_8068456
  have hstable : (prefixWord ++ tailWord_8068456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068456).length < 2 ^ (prefixWord ++ tailWord_8068456).sum := by decide
  have hdescent : baseEnd_8068456 < baseStart_8068456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068471 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 4, 5]
def baseStart_8068471 : Nat := 118140960795 + 8068471 * 2 ^ 59
def prefixEnd_8068471 : Nat := 4983230072969 + 3 ^ 40 * 8068471 * 2
def baseEnd_8068471 : Nat := 1381001256620935601268761

theorem tailTrace_8068471 : CollatzResearch.WordTrace tailWord_8068471 prefixEnd_8068471 1381001256620935601268761 := by
  unfold tailWord_8068471
  simp only [CollatzResearch.WordTrace]
  refine ⟨294281313552315026984909267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196187542368210017989939511 294281313552315026984909267)
  ·
    refine ⟨441421970328472540477363901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294281313552315026984909267 441421970328472540477363901)
    ·
      refine ⟨165533238873177202679011463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441421970328472540477363901 165533238873177202679011463)
      ·
        refine ⟨248299858309765804018517195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165533238873177202679011463 248299858309765804018517195)
        ·
          refine ⟨372449787464648706027775793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248299858309765804018517195 372449787464648706027775793)
          ·
            refine ⟨279337340598486529520831845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372449787464648706027775793 279337340598486529520831845)
            ·
              refine ⟨52375751362216224285155971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279337340598486529520831845 52375751362216224285155971)
              ·
                refine ⟨78563627043324336427733957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52375751362216224285155971 78563627043324336427733957)
                ·
                  refine ⟨14730680070623313080200117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78563627043324336427733957 14730680070623313080200117)
                  ·
                    refine ⟨1381001256620935601268761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14730680070623313080200117 1381001256620935601268761)
                    ·
                      rfl

theorem cell23_8068471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_8068471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068471 prefixEnd_8068471 := by exact prefixLift 8068471
  have htrace : WordTrace (prefixWord ++ tailWord_8068471) baseStart_8068471 baseEnd_8068471 := by
    simpa [prefixWord, tailWord_8068471, baseEnd_8068471] using wordTrace_append hprefix tailTrace_8068471
  have hstable : (prefixWord ++ tailWord_8068471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068471).length < 2 ^ (prefixWord ++ tailWord_8068471).sum := by decide
  have hdescent : baseEnd_8068471 < baseStart_8068471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068491 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4]
def baseStart_8068491 : Nat := 118140960795 + 8068491 * 2 ^ 59
def prefixEnd_8068491 : Nat := 4983230072969 + 3 ^ 40 * 8068491 * 2
def baseEnd_8068491 : Nat := 4143014039475896725556191

theorem tailTrace_8068491 : CollatzResearch.WordTrace tailWord_8068491 prefixEnd_8068491 4143014039475896725556191 := by
  unfold tailWord_8068491
  simp only [CollatzResearch.WordTrace]
  refine ⟨294282043012242570400637327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196188028674828380267091551 294282043012242570400637327)
  ·
    refine ⟨441423064518363855600955991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294282043012242570400637327 441423064518363855600955991)
    ·
      refine ⟨662134596777545783401433987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441423064518363855600955991 662134596777545783401433987)
      ·
        refine ⟨993201895166318675102150981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662134596777545783401433987 993201895166318675102150981)
        ·
          refine ⟨186225355343684751581653309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 993201895166318675102150981 186225355343684751581653309)
          ·
            refine ⟨69834508253881781843119991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186225355343684751581653309 69834508253881781843119991)
            ·
              refine ⟨104751762380822672764679987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69834508253881781843119991 104751762380822672764679987)
              ·
                refine ⟨157127643571234009147019981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104751762380822672764679987 157127643571234009147019981)
                ·
                  refine ⟨58922866339212753430132493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157127643571234009147019981 58922866339212753430132493)
                  ·
                    refine ⟨22096074877204782536299685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58922866339212753430132493 22096074877204782536299685)
                    ·
                      refine ⟨4143014039475896725556191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22096074877204782536299685 4143014039475896725556191)
                      ·
                        rfl

theorem cell23_8068491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_8068491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068491 prefixEnd_8068491 := by exact prefixLift 8068491
  have htrace : WordTrace (prefixWord ++ tailWord_8068491) baseStart_8068491 baseEnd_8068491 := by
    simpa [prefixWord, tailWord_8068491, baseEnd_8068491] using wordTrace_append hprefix tailTrace_8068491
  have hstable : (prefixWord ++ tailWord_8068491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068491).length < 2 ^ (prefixWord ++ tailWord_8068491).sum := by decide
  have hdescent : baseEnd_8068491 < baseStart_8068491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068525 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_8068525 : Nat := 118140960795 + 8068525 * 2 ^ 59
def prefixEnd_8068525 : Nat := 4983230072969 + 3 ^ 40 * 8068525 * 2
def baseEnd_8068525 : Nat := 4143031497818149592531035

theorem tailTrace_8068525 : CollatzResearch.WordTrace tailWord_8068525 prefixEnd_8068525 4143031497818149592531035 := by
  unfold tailWord_8068525
  simp only [CollatzResearch.WordTrace]
  refine ⟨294283283094119394207375029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196188855396079596138250019 294283283094119394207375029)
  ·
    refine ⟨27589057790073693206941409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294283283094119394207375029 27589057790073693206941409)
    ·
      refine ⟨20691793342555269905206057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27589057790073693206941409 20691793342555269905206057)
      ·
        refine ⟨15518845006916452428904543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20691793342555269905206057 15518845006916452428904543)
        ·
          refine ⟨23278267510374678643356815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15518845006916452428904543 23278267510374678643356815)
          ·
            refine ⟨34917401265562017965035223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23278267510374678643356815 34917401265562017965035223)
            ·
              refine ⟨52376101898343026947552835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34917401265562017965035223 52376101898343026947552835)
              ·
                refine ⟨78564152847514540421329253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52376101898343026947552835 78564152847514540421329253)
                ·
                  refine ⟨14730778658908976328999235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78564152847514540421329253 14730778658908976328999235)
                  ·
                    refine ⟨22096167988363464493498853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14730778658908976328999235 22096167988363464493498853)
                    ·
                      refine ⟨4143031497818149592531035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22096167988363464493498853 4143031497818149592531035)
                      ·
                        rfl

theorem cell23_8068525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_8068525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068525 prefixEnd_8068525 := by exact prefixLift 8068525
  have htrace : WordTrace (prefixWord ++ tailWord_8068525) baseStart_8068525 baseEnd_8068525 := by
    simpa [prefixWord, tailWord_8068525, baseEnd_8068525] using wordTrace_append hprefix tailTrace_8068525
  have hstable : (prefixWord ++ tailWord_8068525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068525).length < 2 ^ (prefixWord ++ tailWord_8068525).sum := by decide
  have hdescent : baseEnd_8068525 < baseStart_8068525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068558 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_8068558 : Nat := 118140960795 + 8068558 * 2 ^ 59
def prefixEnd_8068558 : Nat := 4983230072969 + 3 ^ 40 * 8068558 * 2
def baseEnd_8068558 : Nat := 4143048442679747963418383

theorem tailTrace_8068558 : CollatzResearch.WordTrace tailWord_8068558 prefixEnd_8068558 4143048442679747963418383 := by
  unfold tailWord_8068558
  simp only [CollatzResearch.WordTrace]
  refine ⟨36785560837874980105415791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196189657801999893895550885 36785560837874980105415791)
  ·
    refine ⟨55178341256812470158123687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36785560837874980105415791 55178341256812470158123687)
    ·
      refine ⟨82767511885218705237185531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55178341256812470158123687 82767511885218705237185531)
      ·
        refine ⟨124151267827828057855778297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82767511885218705237185531 124151267827828057855778297)
        ·
          refine ⟨93113450870871043391833723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124151267827828057855778297 93113450870871043391833723)
          ·
            refine ⟨139670176306306565087750585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93113450870871043391833723 139670176306306565087750585)
            ·
              refine ⟨104752632229729923815812939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139670176306306565087750585 104752632229729923815812939)
              ·
                refine ⟨157128948344594885723719409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104752632229729923815812939 157128948344594885723719409)
                ·
                  refine ⟨117846711258446164292789557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157128948344594885723719409 117846711258446164292789557)
                  ·
                    refine ⟨11048129180479327902449021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117846711258446164292789557 11048129180479327902449021)
                    ·
                      refine ⟨4143048442679747963418383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11048129180479327902449021 4143048442679747963418383)
                      ·
                        rfl

theorem cell23_8068558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_8068558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068558 prefixEnd_8068558 := by exact prefixLift 8068558
  have htrace : WordTrace (prefixWord ++ tailWord_8068558) baseStart_8068558 baseEnd_8068558 := by
    simpa [prefixWord, tailWord_8068558, baseEnd_8068558] using wordTrace_append hprefix tailTrace_8068558
  have hstable : (prefixWord ++ tailWord_8068558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068558).length < 2 ^ (prefixWord ++ tailWord_8068558).sum := by decide
  have hdescent : baseEnd_8068558 < baseStart_8068558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068586 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_8068586 : Nat := 118140960795 + 8068586 * 2 ^ 59
def prefixEnd_8068586 : Nat := 4983230072969 + 3 ^ 40 * 8068586 * 2
def baseEnd_8068586 : Nat := 1381020940046024617956085

theorem tailTrace_8068586 : CollatzResearch.WordTrace tailWord_8068586 prefixEnd_8068586 1381020940046024617956085 := by
  unfold tailWord_8068586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73571376986724600406336403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196190338631265601083563741 73571376986724600406336403)
  ·
    refine ⟨110357065480086900609504605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73571376986724600406336403 110357065480086900609504605)
    ·
      refine ⟨41383899555032587728564227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110357065480086900609504605 41383899555032587728564227)
      ·
        refine ⟨62075849332548881592846341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41383899555032587728564227 62075849332548881592846341)
        ·
          refine ⟨11639221749852915298658689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62075849332548881592846341 11639221749852915298658689)
          ·
            refine ⟨8729416312389686473994017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11639221749852915298658689 8729416312389686473994017)
            ·
              refine ⟨6547062234292264855495513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8729416312389686473994017 6547062234292264855495513)
              ·
                refine ⟨4910296675719198641621635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6547062234292264855495513 4910296675719198641621635)
                ·
                  refine ⟨7365445013578797962432453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910296675719198641621635 7365445013578797962432453)
                  ·
                    refine ⟨1381020940046024617956085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7365445013578797962432453 1381020940046024617956085)
                    ·
                      rfl

theorem cell23_8068586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_8068586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068586 prefixEnd_8068586 := by exact prefixLift 8068586
  have htrace : WordTrace (prefixWord ++ tailWord_8068586) baseStart_8068586 baseEnd_8068586 := by
    simpa [prefixWord, tailWord_8068586, baseEnd_8068586] using wordTrace_append hprefix tailTrace_8068586
  have hstable : (prefixWord ++ tailWord_8068586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068586).length < 2 ^ (prefixWord ++ tailWord_8068586).sum := by decide
  have hdescent : baseEnd_8068586 < baseStart_8068586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068615 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_8068615 : Nat := 118140960795 + 8068615 * 2 ^ 59
def prefixEnd_8068615 : Nat := 4983230072969 + 3 ^ 40 * 8068615 * 2
def baseEnd_8068615 : Nat := 4143077711077054240405621

theorem tailTrace_8068615 : CollatzResearch.WordTrace tailWord_8068615 prefixEnd_8068615 4143077711077054240405621 := by
  unfold tailWord_8068615
  simp only [CollatzResearch.WordTrace]
  refine ⟨294286565663793339578151299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196191043775862226385434199 294286565663793339578151299)
  ·
    refine ⟨441429848495690009367226949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294286565663793339578151299 441429848495690009367226949)
    ·
      refine ⟨82768096592941876756355053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441429848495690009367226949 82768096592941876756355053)
      ·
        refine ⟨31038036222353203783633145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82768096592941876756355053 31038036222353203783633145)
        ·
          refine ⟨23278527166764902837724859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31038036222353203783633145 23278527166764902837724859)
          ·
            refine ⟨34917790750147354256587289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23278527166764902837724859 34917790750147354256587289)
            ·
              refine ⟨26188343062610515692440467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34917790750147354256587289 26188343062610515692440467)
              ·
                refine ⟨39282514593915773538660701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26188343062610515692440467 39282514593915773538660701)
                ·
                  refine ⟨14730942972718415076997763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39282514593915773538660701 14730942972718415076997763)
                  ·
                    refine ⟨22096414459077622615496645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14730942972718415076997763 22096414459077622615496645)
                    ·
                      refine ⟨4143077711077054240405621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22096414459077622615496645 4143077711077054240405621)
                      ·
                        rfl

theorem cell23_8068615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_8068615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068615 prefixEnd_8068615 := by exact prefixLift 8068615
  have htrace : WordTrace (prefixWord ++ tailWord_8068615) baseStart_8068615 baseEnd_8068615 := by
    simpa [prefixWord, tailWord_8068615, baseEnd_8068615] using wordTrace_append hprefix tailTrace_8068615
  have hstable : (prefixWord ++ tailWord_8068615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068615).length < 2 ^ (prefixWord ++ tailWord_8068615).sum := by decide
  have hdescent : baseEnd_8068615 < baseStart_8068615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068619 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 2, 3, 2]
def baseStart_8068619 : Nat := 118140960795 + 8068619 * 2 ^ 59
def prefixEnd_8068619 : Nat := 4983230072969 + 3 ^ 40 * 8068619 * 2
def baseEnd_8068619 : Nat := 4143079764999672224755603

theorem tailTrace_8068619 : CollatzResearch.WordTrace tailWord_8068619 prefixEnd_8068619 4143079764999672224755603 := by
  unfold tailWord_8068619
  simp only [CollatzResearch.WordTrace]
  refine ⟨294286711555778848261296911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196191141037185898840864607 294286711555778848261296911)
  ·
    refine ⟨441430067333668272391945367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294286711555778848261296911 441430067333668272391945367)
    ·
      refine ⟨662145101000502408587918051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441430067333668272391945367 662145101000502408587918051)
      ·
        refine ⟨993217651500753612881877077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662145101000502408587918051 993217651500753612881877077)
        ·
          refine ⟨11639269353524456400959497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 993217651500753612881877077 11639269353524456400959497)
          ·
            refine ⟨8729452015143342300719623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11639269353524456400959497 8729452015143342300719623)
            ·
              refine ⟨13094178022715013451079435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729452015143342300719623 13094178022715013451079435)
              ·
                refine ⟨19641267034072520176619153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13094178022715013451079435 19641267034072520176619153)
                ·
                  refine ⟨14730950275554390132464365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19641267034072520176619153 14730950275554390132464365)
                  ·
                    refine ⟨5524106353332896299674137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14730950275554390132464365 5524106353332896299674137)
                    ·
                      refine ⟨4143079764999672224755603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524106353332896299674137 4143079764999672224755603)
                      ·
                        rfl

theorem cell23_8068619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 3, 2].length) (baseStart_8068619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068619 prefixEnd_8068619 := by exact prefixLift 8068619
  have htrace : WordTrace (prefixWord ++ tailWord_8068619) baseStart_8068619 baseEnd_8068619 := by
    simpa [prefixWord, tailWord_8068619, baseEnd_8068619] using wordTrace_append hprefix tailTrace_8068619
  have hstable : (prefixWord ++ tailWord_8068619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068619).length < 2 ^ (prefixWord ++ tailWord_8068619).sum := by decide
  have hdescent : baseEnd_8068619 < baseStart_8068619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068632 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_8068632 : Nat := 118140960795 + 8068632 * 2 ^ 59
def prefixEnd_8068632 : Nat := 4983230072969 + 3 ^ 40 * 8068632 * 2
def baseEnd_8068632 : Nat := 4143086440248180673893043

theorem tailTrace_8068632 : CollatzResearch.WordTrace tailWord_8068632 prefixEnd_8068632 4143086440248180673893043 := by
  unfold tailWord_8068632
  simp only [CollatzResearch.WordTrace]
  refine ⟨147143592852365875740760075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196191457136487834321013433 147143592852365875740760075)
  ·
    refine ⟨220715389278548813611140113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147143592852365875740760075 220715389278548813611140113)
    ·
      refine ⟨165536541958911610208355085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220715389278548813611140113 165536541958911610208355085)
      ·
        refine ⟨62076203234591853828133157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165536541958911610208355085 62076203234591853828133157)
        ·
          refine ⟨11639288106485972592774967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62076203234591853828133157 11639288106485972592774967)
          ·
            refine ⟨17458932159728958889162451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639288106485972592774967 17458932159728958889162451)
            ·
              refine ⟨26188398239593438333743677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458932159728958889162451 26188398239593438333743677)
              ·
                refine ⟨9820649339847539375153879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26188398239593438333743677 9820649339847539375153879)
                ·
                  refine ⟨14730974009771309062730819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820649339847539375153879 14730974009771309062730819)
                  ·
                    refine ⟨22096461014656963594096229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14730974009771309062730819 22096461014656963594096229)
                    ·
                      refine ⟨4143086440248180673893043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22096461014656963594096229 4143086440248180673893043)
                      ·
                        rfl

theorem cell23_8068632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_8068632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068632 prefixEnd_8068632 := by exact prefixLift 8068632
  have htrace : WordTrace (prefixWord ++ tailWord_8068632) baseStart_8068632 baseEnd_8068632 := by
    simpa [prefixWord, tailWord_8068632, baseEnd_8068632] using wordTrace_append hprefix tailTrace_8068632
  have hstable : (prefixWord ++ tailWord_8068632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068632).length < 2 ^ (prefixWord ++ tailWord_8068632).sum := by decide
  have hdescent : baseEnd_8068632 < baseStart_8068632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068642 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_8068642 : Nat := 118140960795 + 8068642 * 2 ^ 59
def prefixEnd_8068642 : Nat := 4983230072969 + 3 ^ 40 * 8068642 * 2
def baseEnd_8068642 : Nat := 1381030525018241878255999

theorem tailTrace_8068642 : CollatzResearch.WordTrace tailWord_8068642 prefixEnd_8068642 1381030525018241878255999 := by
  unfold tailWord_8068642
  simp only [CollatzResearch.WordTrace]
  refine ⟨73571887608673880797346045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196191700289797015459589453 73571887608673880797346045)
  ·
    refine ⟨27589457853252705299004767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73571887608673880797346045 27589457853252705299004767)
    ·
      refine ⟨41384186779879057948507151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27589457853252705299004767 41384186779879057948507151)
      ·
        refine ⟨62076280169818586922760727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41384186779879057948507151 62076280169818586922760727)
        ·
          refine ⟨93114420254727880384141091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62076280169818586922760727 93114420254727880384141091)
          ·
            refine ⟨139671630382091820576211637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93114420254727880384141091 139671630382091820576211637)
            ·
              refine ⟨13094215348321108179019841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139671630382091820576211637 13094215348321108179019841)
              ·
                refine ⟨9820661511240831134264881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094215348321108179019841 9820661511240831134264881)
                ·
                  refine ⟨7365496133430623350698661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9820661511240831134264881 7365496133430623350698661)
                  ·
                    refine ⟨1381030525018241878255999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7365496133430623350698661 1381030525018241878255999)
                    ·
                      rfl

theorem cell23_8068642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_8068642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068642 prefixEnd_8068642 := by exact prefixLift 8068642
  have htrace : WordTrace (prefixWord ++ tailWord_8068642) baseStart_8068642 baseEnd_8068642 := by
    simpa [prefixWord, tailWord_8068642, baseEnd_8068642] using wordTrace_append hprefix tailTrace_8068642
  have hstable : (prefixWord ++ tailWord_8068642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068642).length < 2 ^ (prefixWord ++ tailWord_8068642).sum := by decide
  have hdescent : baseEnd_8068642 < baseStart_8068642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068662 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_8068662 : Nat := 118140960795 + 8068662 * 2 ^ 59
def prefixEnd_8068662 : Nat := 4983230072969 + 3 ^ 40 * 8068662 * 2
def baseEnd_8068662 : Nat := 4143101844667815556517905

theorem tailTrace_8068662 : CollatzResearch.WordTrace tailWord_8068662 prefixEnd_8068662 4143101844667815556517905 := by
  unfold tailWord_8068662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393017493413941662819515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196192186596415377736741493 18393017493413941662819515)
  ·
    refine ⟨27589526240120912494229273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18393017493413941662819515 27589526240120912494229273)
    ·
      refine ⟨20692144680090684370671955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27589526240120912494229273 20692144680090684370671955)
      ·
        refine ⟨31038217020136026556007933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20692144680090684370671955 31038217020136026556007933)
        ·
          refine ⟨11639331382551009958502975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31038217020136026556007933 11639331382551009958502975)
          ·
            refine ⟨17458997073826514937754463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639331382551009958502975 17458997073826514937754463)
            ·
              refine ⟨26188495610739772406631695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458997073826514937754463 26188495610739772406631695)
              ·
                refine ⟨39282743416109658609947543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26188495610739772406631695 39282743416109658609947543)
                ·
                  refine ⟨58924115124164487914921315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39282743416109658609947543 58924115124164487914921315)
                  ·
                    refine ⟨88386172686246731872381973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58924115124164487914921315 88386172686246731872381973)
                    ·
                      refine ⟨4143101844667815556517905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88386172686246731872381973 4143101844667815556517905)
                      ·
                        rfl

theorem cell23_8068662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_8068662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068662 prefixEnd_8068662 := by exact prefixLift 8068662
  have htrace : WordTrace (prefixWord ++ tailWord_8068662) baseStart_8068662 baseEnd_8068662 := by
    simpa [prefixWord, tailWord_8068662, baseEnd_8068662] using wordTrace_append hprefix tailTrace_8068662
  have hstable : (prefixWord ++ tailWord_8068662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068662).length < 2 ^ (prefixWord ++ tailWord_8068662).sum := by decide
  have hdescent : baseEnd_8068662 < baseStart_8068662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068669 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_8068669 : Nat := 118140960795 + 8068669 * 2 ^ 59
def prefixEnd_8068669 : Nat := 4983230072969 + 3 ^ 40 * 8068669 * 2
def baseEnd_8068669 : Nat := 4143105439032397029130373

theorem tailTrace_8068669 : CollatzResearch.WordTrace tailWord_8068669 prefixEnd_8068669 4143105439032397029130373 := by
  unfold tailWord_8068669
  simp only [CollatzResearch.WordTrace]
  refine ⟨294288535205597706800617061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196192356803731804533744707 294288535205597706800617061)
  ·
    refine ⟨55179100351049570025115699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294288535205597706800617061 55179100351049570025115699)
    ·
      refine ⟨82768650526574355037673549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55179100351049570025115699 82768650526574355037673549)
      ·
        refine ⟨31038243947465383139127581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82768650526574355037673549 31038243947465383139127581)
        ·
          refine ⟨11639341480299518677172843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31038243947465383139127581 11639341480299518677172843)
          ·
            refine ⟨17459012220449278015759265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639341480299518677172843 17459012220449278015759265)
            ·
              refine ⟨13094259165336958511819449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17459012220449278015759265 13094259165336958511819449)
              ·
                refine ⟨9820694374002718883864587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094259165336958511819449 9820694374002718883864587)
                ·
                  refine ⟨14731041561004078325796881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820694374002718883864587 14731041561004078325796881)
                  ·
                    refine ⟨11048281170753058744347661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14731041561004078325796881 11048281170753058744347661)
                    ·
                      refine ⟨4143105439032397029130373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11048281170753058744347661 4143105439032397029130373)
                      ·
                        rfl

theorem cell23_8068669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_8068669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068669 prefixEnd_8068669 := by exact prefixLift 8068669
  have htrace : WordTrace (prefixWord ++ tailWord_8068669) baseStart_8068669 baseEnd_8068669 := by
    simpa [prefixWord, tailWord_8068669, baseEnd_8068669] using wordTrace_append hprefix tailTrace_8068669
  have hstable : (prefixWord ++ tailWord_8068669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068669).length < 2 ^ (prefixWord ++ tailWord_8068669).sum := by decide
  have hdescent : baseEnd_8068669 < baseStart_8068669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068698 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_8068698 : Nat := 118140960795 + 8068698 * 2 ^ 59
def prefixEnd_8068698 : Nat := 4983230072969 + 3 ^ 40 * 8068698 * 2
def baseEnd_8068698 : Nat := 1381040109990459138555913

theorem tailTrace_8068698 : CollatzResearch.WordTrace tailWord_8068698 prefixEnd_8068698 1381040109990459138555913 := by
  unfold tailWord_8068698
  simp only [CollatzResearch.WordTrace]
  refine ⟨73572398230623161188355687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196193061948328429835615165 73572398230623161188355687)
  ·
    refine ⟨110358597345934741782533531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73572398230623161188355687 110358597345934741782533531)
    ·
      refine ⟨165537896018902112673800297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110358597345934741782533531 165537896018902112673800297)
      ·
        refine ⟨124153422014176584505350223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165537896018902112673800297 124153422014176584505350223)
        ·
          refine ⟨186230133021264876758025335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124153422014176584505350223 186230133021264876758025335)
          ·
            refine ⟨279345199531897315137038003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186230133021264876758025335 279345199531897315137038003)
            ·
              refine ⟨419017799297845972705557005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279345199531897315137038003 419017799297845972705557005)
              ·
                refine ⟨157131674736692239764583877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419017799297845972705557005 157131674736692239764583877)
                ·
                  refine ⟨29462189013129794955859477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157131674736692239764583877 29462189013129794955859477)
                  ·
                    refine ⟨1381040109990459138555913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29462189013129794955859477 1381040109990459138555913)
                    ·
                      rfl

theorem cell23_8068698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_8068698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068698 prefixEnd_8068698 := by exact prefixLift 8068698
  have htrace : WordTrace (prefixWord ++ tailWord_8068698) baseStart_8068698 baseEnd_8068698 := by
    simpa [prefixWord, tailWord_8068698, baseEnd_8068698] using wordTrace_append hprefix tailTrace_8068698
  have hstable : (prefixWord ++ tailWord_8068698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068698).length < 2 ^ (prefixWord ++ tailWord_8068698).sum := by decide
  have hdescent : baseEnd_8068698 < baseStart_8068698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068726 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_8068726 : Nat := 118140960795 + 8068726 * 2 ^ 59
def prefixEnd_8068726 : Nat := 4983230072969 + 3 ^ 40 * 8068726 * 2
def baseEnd_8068726 : Nat := 4143134707429703306117611

theorem tailTrace_8068726 : CollatzResearch.WordTrace tailWord_8068726 prefixEnd_8068726 4143134707429703306117611 := by
  unfold tailWord_8068726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393163385399450345965127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196193742777594137023628021 18393163385399450345965127)
  ·
    refine ⟨27589745078099175518947691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18393163385399450345965127 27589745078099175518947691)
    ·
      refine ⟨41384617617148763278421537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27589745078099175518947691 41384617617148763278421537)
      ·
        refine ⟨31038463212861572458816153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41384617617148763278421537 31038463212861572458816153)
        ·
          refine ⟨23278847409646179344112115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31038463212861572458816153 23278847409646179344112115)
          ·
            refine ⟨34918271114469269016168173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23278847409646179344112115 34918271114469269016168173)
            ·
              refine ⟨13094351667925975881063065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34918271114469269016168173 13094351667925975881063065)
              ·
                refine ⟨9820763750944481910797299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094351667925975881063065 9820763750944481910797299)
                ·
                  refine ⟨14731145626416722866195949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820763750944481910797299 14731145626416722866195949)
                  ·
                    refine ⟨5524179609906271074823481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14731145626416722866195949 5524179609906271074823481)
                    ·
                      refine ⟨4143134707429703306117611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524179609906271074823481 4143134707429703306117611)
                      ·
                        rfl

theorem cell23_8068726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_8068726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068726 prefixEnd_8068726 := by exact prefixLift 8068726
  have htrace : WordTrace (prefixWord ++ tailWord_8068726) baseStart_8068726 baseEnd_8068726 := by
    simpa [prefixWord, tailWord_8068726, baseEnd_8068726] using wordTrace_append hprefix tailTrace_8068726
  have hstable : (prefixWord ++ tailWord_8068726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068726).length < 2 ^ (prefixWord ++ tailWord_8068726).sum := by decide
  have hdescent : baseEnd_8068726 < baseStart_8068726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068772 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_8068772 : Nat := 118140960795 + 8068772 * 2 ^ 59
def prefixEnd_8068772 : Nat := 4983230072969 + 3 ^ 40 * 8068772 * 2
def baseEnd_8068772 : Nat := 4143158327539810126142399

theorem tailTrace_8068772 : CollatzResearch.WordTrace tailWord_8068772 prefixEnd_8068772 4143158327539810126142399 := by
  unfold tailWord_8068772
  simp only [CollatzResearch.WordTrace]
  refine ⟨147146145962112277695808285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196194861282816370261077713 147146145962112277695808285)
  ·
    refine ⟨55179804735792104135928107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147146145962112277695808285 55179804735792104135928107)
    ·
      refine ⟨82769707103688156203892161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55179804735792104135928107 82769707103688156203892161)
      ·
        refine ⟨62077280327766117152919121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82769707103688156203892161 62077280327766117152919121)
        ·
          refine ⟨46557960245824587864689341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62077280327766117152919121 46557960245824587864689341)
          ·
            refine ⟨17459235092184220449258503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46557960245824587864689341 17459235092184220449258503)
            ·
              refine ⟨26188852638276330673887755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17459235092184220449258503 26188852638276330673887755)
              ·
                refine ⟨39283278957414496010831633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26188852638276330673887755 39283278957414496010831633)
                ·
                  refine ⟨29462459218060872008123725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39283278957414496010831633 29462459218060872008123725)
                  ·
                    refine ⟨11048422206772827003046397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29462459218060872008123725 11048422206772827003046397)
                    ·
                      refine ⟨4143158327539810126142399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11048422206772827003046397 4143158327539810126142399)
                      ·
                        rfl

theorem cell23_8068772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_8068772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068772 prefixEnd_8068772 := by exact prefixLift 8068772
  have htrace : WordTrace (prefixWord ++ tailWord_8068772) baseStart_8068772 baseEnd_8068772 := by
    simpa [prefixWord, tailWord_8068772, baseEnd_8068772] using wordTrace_append hprefix tailTrace_8068772
  have hstable : (prefixWord ++ tailWord_8068772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068772).length < 2 ^ (prefixWord ++ tailWord_8068772).sum := by decide
  have hdescent : baseEnd_8068772 < baseStart_8068772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068806 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_8068806 : Nat := 118140960795 + 8068806 * 2 ^ 59
def prefixEnd_8068806 : Nat := 4983230072969 + 3 ^ 40 * 8068806 * 2
def baseEnd_8068806 : Nat := 4143175785882062993117243

theorem tailTrace_8068806 : CollatzResearch.WordTrace tailWord_8068806 prefixEnd_8068806 4143175785882062993117243 := by
  unfold tailWord_8068806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196672875190668099948571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196195688004067586132236181 9196672875190668099948571)
  ·
    refine ⟨13795009312786002149922857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9196672875190668099948571 13795009312786002149922857)
    ·
      refine ⟨10346256984589501612442143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13795009312786002149922857 10346256984589501612442143)
      ·
        refine ⟨15519385476884252418663215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10346256984589501612442143 15519385476884252418663215)
        ·
          refine ⟨23279078215326378627994823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15519385476884252418663215 23279078215326378627994823)
          ·
            refine ⟨34918617322989567941992235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23279078215326378627994823 34918617322989567941992235)
            ·
              refine ⟨52377925984484351912988353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34918617322989567941992235 52377925984484351912988353)
              ·
                refine ⟨39283444488363263934741265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52377925984484351912988353 39283444488363263934741265)
                ·
                  refine ⟨29462583366272447951055949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39283444488363263934741265 29462583366272447951055949)
                  ·
                    refine ⟨11048468762352167981645981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29462583366272447951055949 11048468762352167981645981)
                    ·
                      refine ⟨4143175785882062993117243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11048468762352167981645981 4143175785882062993117243)
                      ·
                        rfl

theorem cell23_8068806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_8068806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068806 prefixEnd_8068806 := by exact prefixLift 8068806
  have htrace : WordTrace (prefixWord ++ tailWord_8068806) baseStart_8068806 baseEnd_8068806 := by
    simpa [prefixWord, tailWord_8068806, baseEnd_8068806] using wordTrace_append hprefix tailTrace_8068806
  have hstable : (prefixWord ++ tailWord_8068806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068806).length < 2 ^ (prefixWord ++ tailWord_8068806).sum := by decide
  have hdescent : baseEnd_8068806 < baseStart_8068806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068870 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8068870 : Nat := 118140960795 + 8068870 * 2 ^ 59
def prefixEnd_8068870 : Nat := 4983230072969 + 3 ^ 40 * 8068870 * 2
def baseEnd_8068870 : Nat := 4143208648643950742716949

theorem tailTrace_8068870 : CollatzResearch.WordTrace tailWord_8068870 prefixEnd_8068870 4143208648643950742716949 := by
  unfold tailWord_8068870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196745821183422441521377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196197244185246345419122709 9196745821183422441521377)
  ·
    refine ⟨6897559365887566831141033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9196745821183422441521377 6897559365887566831141033)
    ·
      refine ⟨5173169524415675123355775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6897559365887566831141033 5173169524415675123355775)
      ·
        refine ⟨7759754286623512685033663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173169524415675123355775 7759754286623512685033663)
        ·
          refine ⟨11639631429935269027550495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759754286623512685033663 11639631429935269027550495)
          ·
            refine ⟨17459447144902903541325743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639631429935269027550495 17459447144902903541325743)
            ·
              refine ⟨26189170717354355311988615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17459447144902903541325743 26189170717354355311988615)
              ·
                refine ⟨39283756076031532967982923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26189170717354355311988615 39283756076031532967982923)
                ·
                  refine ⟨58925634114047299451974385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39283756076031532967982923 58925634114047299451974385)
                  ·
                    refine ⟨44194225585535474588980789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58925634114047299451974385 44194225585535474588980789)
                    ·
                      refine ⟨4143208648643950742716949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44194225585535474588980789 4143208648643950742716949)
                      ·
                        rfl

theorem cell23_8068870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8068870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068870 prefixEnd_8068870 := by exact prefixLift 8068870
  have htrace : WordTrace (prefixWord ++ tailWord_8068870) baseStart_8068870 baseEnd_8068870 := by
    simpa [prefixWord, tailWord_8068870, baseEnd_8068870] using wordTrace_append hprefix tailTrace_8068870
  have hstable : (prefixWord ++ tailWord_8068870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068870).length < 2 ^ (prefixWord ++ tailWord_8068870).sum := by decide
  have hdescent : baseEnd_8068870 < baseStart_8068870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068919 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 7, 2, 2]
def baseStart_8068919 : Nat := 118140960795 + 8068919 * 2 ^ 59
def prefixEnd_8068919 : Nat := 4983230072969 + 3 ^ 40 * 8068919 * 2
def baseEnd_8068919 : Nat := 4143233809196021051004223

theorem tailTrace_8068919 : CollatzResearch.WordTrace tailWord_8068919 prefixEnd_8068919 4143233809196021051004223 := by
  unfold tailWord_8068919
  simp only [CollatzResearch.WordTrace]
  refine ⟨294297653454691999497217811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196198435636461332998145207 294297653454691999497217811)
  ·
    refine ⟨441446480182037999245826717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294297653454691999497217811 441446480182037999245826717)
    ·
      refine ⟨165542430068264249717185019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441446480182037999245826717 165542430068264249717185019)
      ·
        refine ⟨248313645102396374575777529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165542430068264249717185019 248313645102396374575777529)
        ·
          refine ⟨186235233826797280931833147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248313645102396374575777529 186235233826797280931833147)
          ·
            refine ⟨279352850740195921397749721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186235233826797280931833147 279352850740195921397749721)
            ·
              refine ⟨209514638055146941048312291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279352850740195921397749721 209514638055146941048312291)
              ·
                refine ⟨314271957082720411572468437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209514638055146941048312291 314271957082720411572468437)
                ·
                  refine ⟨7365748994126259646229729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 314271957082720411572468437 7365748994126259646229729)
                  ·
                    refine ⟨5524311745594694734672297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365748994126259646229729 5524311745594694734672297)
                    ·
                      refine ⟨4143233809196021051004223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524311745594694734672297 4143233809196021051004223)
                      ·
                        rfl

theorem cell23_8068919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_8068919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068919 prefixEnd_8068919 := by exact prefixLift 8068919
  have htrace : WordTrace (prefixWord ++ tailWord_8068919) baseStart_8068919 baseEnd_8068919 := by
    simpa [prefixWord, tailWord_8068919, baseEnd_8068919] using wordTrace_append hprefix tailTrace_8068919
  have hstable : (prefixWord ++ tailWord_8068919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068919).length < 2 ^ (prefixWord ++ tailWord_8068919).sum := by decide
  have hdescent : baseEnd_8068919 < baseStart_8068919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068949 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_8068949 : Nat := 118140960795 + 8068949 * 2 ^ 59
def prefixEnd_8068949 : Nat := 4983230072969 + 3 ^ 40 * 8068949 * 2
def baseEnd_8068949 : Nat := 4143249213615655933629085

theorem tailTrace_8068949 : CollatzResearch.WordTrace tailWord_8068949 prefixEnd_8068949 4143249213615655933629085 := by
  unfold tailWord_8068949
  simp only [CollatzResearch.WordTrace]
  refine ⟨294298747644583314620809901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196199165096388876413873267 294298747644583314620809901)
  ·
    refine ⟨110362030366718742982803713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294298747644583314620809901 110362030366718742982803713)
    ·
      refine ⟨82771522775039057237102785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110362030366718742982803713 82771522775039057237102785)
      ·
        refine ⟨62078642081279292927827089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82771522775039057237102785 62078642081279292927827089)
        ·
          refine ⟨46558981560959469695870317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62078642081279292927827089 46558981560959469695870317)
          ·
            refine ⟨17459618085359801135951369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46558981560959469695870317 17459618085359801135951369)
            ·
              refine ⟨13094713564019850851963527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17459618085359801135951369 13094713564019850851963527)
              ·
                refine ⟨19642070346029776277945291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13094713564019850851963527 19642070346029776277945291)
                ·
                  refine ⟨29463105519044664416917937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19642070346029776277945291 29463105519044664416917937)
                  ·
                    refine ⟨22097329139283498312688453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29463105519044664416917937 22097329139283498312688453)
                    ·
                      refine ⟨4143249213615655933629085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22097329139283498312688453 4143249213615655933629085)
                      ·
                        rfl

theorem cell23_8068949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_8068949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068949 prefixEnd_8068949 := by exact prefixLift 8068949
  have htrace : WordTrace (prefixWord ++ tailWord_8068949) baseStart_8068949 baseEnd_8068949 := by
    simpa [prefixWord, tailWord_8068949, baseEnd_8068949] using wordTrace_append hprefix tailTrace_8068949
  have hstable : (prefixWord ++ tailWord_8068949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068949).length < 2 ^ (prefixWord ++ tailWord_8068949).sum := by decide
  have hdescent : baseEnd_8068949 < baseStart_8068949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068970 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_8068970 : Nat := 118140960795 + 8068970 * 2 ^ 59
def prefixEnd_8068970 : Nat := 4983230072969 + 3 ^ 40 * 8068970 * 2
def baseEnd_8068970 : Nat := 4143259996709400351466489

theorem tailTrace_8068970 : CollatzResearch.WordTrace tailWord_8068970 prefixEnd_8068970 4143259996709400351466489 := by
  unfold tailWord_8068970
  simp only [CollatzResearch.WordTrace]
  refine ⟨73574878394376808801831091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196199675718338156804882909 73574878394376808801831091)
  ·
    refine ⟨110362317591565213202746637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73574878394376808801831091 110362317591565213202746637)
    ·
      refine ⟨41385869096836954951029989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110362317591565213202746637 41385869096836954951029989)
      ·
        refine ⟨7759850455656929053318123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41385869096836954951029989 7759850455656929053318123)
        ·
          refine ⟨11639775683485393579977185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759850455656929053318123 11639775683485393579977185)
          ·
            refine ⟨8729831762614045184982889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11639775683485393579977185 8729831762614045184982889)
            ·
              refine ⟨6547373821960533888737167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8729831762614045184982889 6547373821960533888737167)
              ·
                refine ⟨9821060732940800833105751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547373821960533888737167 9821060732940800833105751)
                ·
                  refine ⟨14731591099411201249658627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9821060732940800833105751 14731591099411201249658627)
                  ·
                    refine ⟨22097386649116801874487941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14731591099411201249658627 22097386649116801874487941)
                    ·
                      refine ⟨4143259996709400351466489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22097386649116801874487941 4143259996709400351466489)
                      ·
                        rfl

theorem cell23_8068970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_8068970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068970 prefixEnd_8068970 := by exact prefixLift 8068970
  have htrace : WordTrace (prefixWord ++ tailWord_8068970) baseStart_8068970 baseEnd_8068970 := by
    simpa [prefixWord, tailWord_8068970, baseEnd_8068970] using wordTrace_append hprefix tailTrace_8068970
  have hstable : (prefixWord ++ tailWord_8068970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068970).length < 2 ^ (prefixWord ++ tailWord_8068970).sum := by decide
  have hdescent : baseEnd_8068970 < baseStart_8068970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068986 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_8068986 : Nat := 118140960795 + 8068986 * 2 ^ 59
def prefixEnd_8068986 : Nat := 4983230072969 + 3 ^ 40 * 8068986 * 2
def baseEnd_8068986 : Nat := 4143268212399872288866415

theorem tailTrace_8068986 : CollatzResearch.WordTrace tailWord_8068986 prefixEnd_8068986 4143268212399872288866415 := by
  unfold tailWord_8068986
  simp only [CollatzResearch.WordTrace]
  refine ⟨73575024286362317484976703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196200064763632846626604541 73575024286362317484976703)
  ·
    refine ⟨110362536429543476227465055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73575024286362317484976703 110362536429543476227465055)
    ·
      refine ⟨165543804644315214341197583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110362536429543476227465055 165543804644315214341197583)
      ·
        refine ⟨248315706966472821511796375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165543804644315214341197583 248315706966472821511796375)
        ·
          refine ⟨372473560449709232267694563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248315706966472821511796375 372473560449709232267694563)
          ·
            refine ⟨558710340674563848401541845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372473560449709232267694563 558710340674563848401541845)
            ·
              refine ⟨13094773609560090196911137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 558710340674563848401541845 13094773609560090196911137)
              ·
                refine ⟨9821080207170067647683353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094773609560090196911137 9821080207170067647683353)
                ·
                  refine ⟨7365810155377550735762515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9821080207170067647683353 7365810155377550735762515)
                  ·
                    refine ⟨11048715233066326103643773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7365810155377550735762515 11048715233066326103643773)
                    ·
                      refine ⟨4143268212399872288866415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11048715233066326103643773 4143268212399872288866415)
                      ·
                        rfl

theorem cell23_8068986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_8068986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8068986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8068986 prefixEnd_8068986 := by exact prefixLift 8068986
  have htrace : WordTrace (prefixWord ++ tailWord_8068986) baseStart_8068986 baseEnd_8068986 := by
    simpa [prefixWord, tailWord_8068986, baseEnd_8068986] using wordTrace_append hprefix tailTrace_8068986
  have hstable : (prefixWord ++ tailWord_8068986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068986).length < 2 ^ (prefixWord ++ tailWord_8068986).sum := by decide
  have hdescent : baseEnd_8068986 < baseStart_8068986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069079 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 2, 5]
def baseStart_8069079 : Nat := 118140960795 + 8069079 * 2 ^ 59
def prefixEnd_8069079 : Nat := 4983230072969 + 3 ^ 40 * 8069079 * 2
def baseEnd_8069079 : Nat := 1381105322033580141667829

theorem tailTrace_8069079 : CollatzResearch.WordTrace tailWord_8069079 prefixEnd_8069079 1381105322033580141667829 := by
  unfold tailWord_8069079
  simp only [CollatzResearch.WordTrace]
  refine ⟨294303489134112346823042291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196202326089408231215361527 294303489134112346823042291)
  ·
    refine ⟨441455233701168520234563437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294303489134112346823042291 441455233701168520234563437)
    ·
      refine ⟨165545712637938195087961289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441455233701168520234563437 165545712637938195087961289)
      ·
        refine ⟨124159284478453646315970967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165545712637938195087961289 124159284478453646315970967)
        ·
          refine ⟨186238926717680469473956451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124159284478453646315970967 186238926717680469473956451)
          ·
            refine ⟨279358390076520704210934677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186238926717680469473956451 279358390076520704210934677)
            ·
              refine ⟨13094924534836908009887563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279358390076520704210934677 13094924534836908009887563)
              ·
                refine ⟨19642386802255362014831345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13094924534836908009887563 19642386802255362014831345)
                ·
                  refine ⟨14731790101691521511123509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19642386802255362014831345 14731790101691521511123509)
                  ·
                    refine ⟨1381105322033580141667829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14731790101691521511123509 1381105322033580141667829)
                    ·
                      rfl

theorem cell23_8069079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_8069079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069079 prefixEnd_8069079 := by exact prefixLift 8069079
  have htrace : WordTrace (prefixWord ++ tailWord_8069079) baseStart_8069079 baseEnd_8069079 := by
    simpa [prefixWord, tailWord_8069079, baseEnd_8069079] using wordTrace_append hprefix tailTrace_8069079
  have hstable : (prefixWord ++ tailWord_8069079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069079).length < 2 ^ (prefixWord ++ tailWord_8069079).sum := by decide
  have hdescent : baseEnd_8069079 < baseStart_8069079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069099 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 6, 2]
def baseStart_8069099 : Nat := 118140960795 + 8069099 * 2 ^ 59
def prefixEnd_8069099 : Nat := 4983230072969 + 3 ^ 40 * 8069099 * 2
def baseEnd_8069099 : Nat := 4143326235713830346753395

theorem tailTrace_8069099 : CollatzResearch.WordTrace tailWord_8069099 prefixEnd_8069099 4143326235713830346753395 := by
  unfold tailWord_8069099
  simp only [CollatzResearch.WordTrace]
  refine ⟨294304218594039890238770351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196202812396026593492513567 294304218594039890238770351)
  ·
    refine ⟨441456327891059835358155527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294304218594039890238770351 441456327891059835358155527)
    ·
      refine ⟨662184491836589753037233291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441456327891059835358155527 662184491836589753037233291)
      ·
        refine ⟨993276737754884629555849937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662184491836589753037233291 993276737754884629555849937)
        ·
          refine ⟨744957553316163472166887453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993276737754884629555849937 744957553316163472166887453)
          ·
            refine ⟨279359082493561302062582795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744957553316163472166887453 279359082493561302062582795)
            ·
              refine ⟨419038623740341953093874193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279359082493561302062582795 419038623740341953093874193)
              ·
                refine ⟨314278967805256464820405645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419038623740341953093874193 314278967805256464820405645)
                ·
                  refine ⟨117854612926971174307652117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314278967805256464820405645 117854612926971174307652117)
                  ·
                    refine ⟨5524434980951773795671193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117854612926971174307652117 5524434980951773795671193)
                    ·
                      refine ⟨4143326235713830346753395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524434980951773795671193 4143326235713830346753395)
                      ·
                        rfl

theorem cell23_8069099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6, 2].length) (baseStart_8069099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069099 prefixEnd_8069099 := by exact prefixLift 8069099
  have htrace : WordTrace (prefixWord ++ tailWord_8069099) baseStart_8069099 baseEnd_8069099 := by
    simpa [prefixWord, tailWord_8069099, baseEnd_8069099] using wordTrace_append hprefix tailTrace_8069099
  have hstable : (prefixWord ++ tailWord_8069099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069099).length < 2 ^ (prefixWord ++ tailWord_8069099).sum := by decide
  have hdescent : baseEnd_8069099 < baseStart_8069099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069116 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_8069116 : Nat := 118140960795 + 8069116 * 2 ^ 59
def prefixEnd_8069116 : Nat := 4983230072969 + 3 ^ 40 * 8069116 * 2
def baseEnd_8069116 : Nat := 4143334964884956780240817

theorem tailTrace_8069116 : CollatzResearch.WordTrace tailWord_8069116 prefixEnd_8069116 4143334964884956780240817 := by
  unfold tailWord_8069116
  simp only [CollatzResearch.WordTrace]
  refine ⟨147152419317489151071069601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196203225756652201428092801 147152419317489151071069601)
  ·
    refine ⟨110364314488116863303302201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147152419317489151071069601 110364314488116863303302201)
    ·
      refine ⟨82773235866087647477476651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110364314488116863303302201 82773235866087647477476651)
      ·
        refine ⟨124159853799131471216214977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82773235866087647477476651 124159853799131471216214977)
        ·
          refine ⟨93119890349348603412161233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124159853799131471216214977 93119890349348603412161233)
          ·
            refine ⟨69839917762011452559120925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93119890349348603412161233 69839917762011452559120925)
            ·
              refine ⟨26189969160754294709670347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69839917762011452559120925 26189969160754294709670347)
              ·
                refine ⟨39284953741131442064505521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26189969160754294709670347 39284953741131442064505521)
                ·
                  refine ⟨29463715305848581548379141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39284953741131442064505521 29463715305848581548379141)
                  ·
                    refine ⟨5524446619846609040321089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29463715305848581548379141 5524446619846609040321089)
                    ·
                      refine ⟨4143334964884956780240817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524446619846609040321089 4143334964884956780240817)
                      ·
                        rfl

theorem cell23_8069116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_8069116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069116 prefixEnd_8069116 := by exact prefixLift 8069116
  have htrace : WordTrace (prefixWord ++ tailWord_8069116) baseStart_8069116 baseEnd_8069116 := by
    simpa [prefixWord, tailWord_8069116, baseEnd_8069116] using wordTrace_append hprefix tailTrace_8069116
  have hstable : (prefixWord ++ tailWord_8069116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069116).length < 2 ^ (prefixWord ++ tailWord_8069116).sum := by decide
  have hdescent : baseEnd_8069116 < baseStart_8069116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069119 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_8069119 : Nat := 118140960795 + 8069119 * 2 ^ 59
def prefixEnd_8069119 : Nat := 4983230072969 + 3 ^ 40 * 8069119 * 2
def baseEnd_8069119 : Nat := 4143336505326920268503303

theorem tailTrace_8069119 : CollatzResearch.WordTrace tailWord_8069119 prefixEnd_8069119 4143336505326920268503303 := by
  unfold tailWord_8069119
  simp only [CollatzResearch.WordTrace]
  refine ⟨294304948053967433654498411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196203298702644955769665607 294304948053967433654498411)
  ·
    refine ⟨441457422080951150481747617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294304948053967433654498411 441457422080951150481747617)
    ·
      refine ⟨331093066560713362861310713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441457422080951150481747617 331093066560713362861310713)
      ·
        refine ⟨248319799920535022145983035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331093066560713362861310713 248319799920535022145983035)
        ·
          refine ⟨372479699880802533218974553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248319799920535022145983035 372479699880802533218974553)
          ·
            refine ⟨279359774910601899914230915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372479699880802533218974553 279359774910601899914230915)
            ·
              refine ⟨419039662365902849871346373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279359774910601899914230915 419039662365902849871346373)
              ·
                refine ⟨78569936693606784350877445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419039662365902849871346373 78569936693606784350877445)
                ·
                  refine ⟨14731863130051272065789521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78569936693606784350877445 14731863130051272065789521)
                  ·
                    refine ⟨11048897347538454049342141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14731863130051272065789521 11048897347538454049342141)
                    ·
                      refine ⟨4143336505326920268503303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11048897347538454049342141 4143336505326920268503303)
                      ·
                        rfl

theorem cell23_8069119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_8069119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069119 prefixEnd_8069119 := by exact prefixLift 8069119
  have htrace : WordTrace (prefixWord ++ tailWord_8069119) baseStart_8069119 baseEnd_8069119 := by
    simpa [prefixWord, tailWord_8069119, baseEnd_8069119] using wordTrace_append hprefix tailTrace_8069119
  have hstable : (prefixWord ++ tailWord_8069119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069119).length < 2 ^ (prefixWord ++ tailWord_8069119).sum := by decide
  have hdescent : baseEnd_8069119 < baseStart_8069119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069156 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 8]
def baseStart_8069156 : Nat := 118140960795 + 8069156 * 2 ^ 59
def prefixEnd_8069156 : Nat := 4983230072969 + 3 ^ 40 * 8069156 * 2
def baseEnd_8069156 : Nat := 460372833790126291526737

theorem tailTrace_8069156 : CollatzResearch.WordTrace tailWord_8069156 prefixEnd_8069156 460372833790126291526737 := by
  unfold tailWord_8069156
  simp only [CollatzResearch.WordTrace]
  refine ⟨147153148777416694486797661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196204198369888925982396881 147153148777416694486797661)
  ·
    refine ⟨55182430791531260432549123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147153148777416694486797661 55182430791531260432549123)
    ·
      refine ⟨82773646187296890648823685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55182430791531260432549123 82773646187296890648823685)
      ·
        refine ⟨15520058660118166996654441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82773646187296890648823685 15520058660118166996654441)
        ·
          refine ⟨11640043995088625247490831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15520058660118166996654441 11640043995088625247490831)
          ·
            refine ⟨17460065992632937871236247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640043995088625247490831 17460065992632937871236247)
            ·
              refine ⟨26190098988949406806854371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17460065992632937871236247 26190098988949406806854371)
              ·
                refine ⟨39285148483424110210281557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26190098988949406806854371 39285148483424110210281557)
                ·
                  refine ⟨460372833790126291526737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39285148483424110210281557 460372833790126291526737)
                  ·
                    rfl

theorem cell23_8069156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_8069156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069156 prefixEnd_8069156 := by exact prefixLift 8069156
  have htrace : WordTrace (prefixWord ++ tailWord_8069156) baseStart_8069156 baseEnd_8069156 := by
    simpa [prefixWord, tailWord_8069156, baseEnd_8069156] using wordTrace_append hprefix tailTrace_8069156
  have hstable : (prefixWord ++ tailWord_8069156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069156).length < 2 ^ (prefixWord ++ tailWord_8069156).sum := by decide
  have hdescent : baseEnd_8069156 < baseStart_8069156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069160 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 3, 4]
def baseStart_8069160 : Nat := 118140960795 + 8069160 * 2 ^ 59
def prefixEnd_8069160 : Nat := 4983230072969 + 3 ^ 40 * 8069160 * 2
def baseEnd_8069160 : Nat := 1381119186011251536030205

theorem tailTrace_8069160 : CollatzResearch.WordTrace tailWord_8069160 prefixEnd_8069160 1381119186011251536030205 := by
  unfold tailWord_8069160
  simp only [CollatzResearch.WordTrace]
  refine ⟨147153221723409448828370467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196204295631212598437827289 147153221723409448828370467)
  ·
    refine ⟨220729832585114173242555701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147153221723409448828370467 220729832585114173242555701)
    ·
      refine ⟨20693421804854453741489597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220729832585114173242555701 20693421804854453741489597)
      ·
        refine ⟨7760033176820420153058599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20693421804854453741489597 7760033176820420153058599)
        ·
          refine ⟨11640049765230630229587899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760033176820420153058599 11640049765230630229587899)
          ·
            refine ⟨17460074647845945344381849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640049765230630229587899 17460074647845945344381849)
            ·
              refine ⟨13095055985884459008286387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17460074647845945344381849 13095055985884459008286387)
              ·
                refine ⟨19642583978826688512429581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13095055985884459008286387 19642583978826688512429581)
                ·
                  refine ⟨7365968992060008192161093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19642583978826688512429581 7365968992060008192161093)
                  ·
                    refine ⟨1381119186011251536030205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7365968992060008192161093 1381119186011251536030205)
                    ·
                      rfl

theorem cell23_8069160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_8069160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069160 prefixEnd_8069160 := by exact prefixLift 8069160
  have htrace : WordTrace (prefixWord ++ tailWord_8069160) baseStart_8069160 baseEnd_8069160 := by
    simpa [prefixWord, tailWord_8069160, baseEnd_8069160] using wordTrace_append hprefix tailTrace_8069160
  have hstable : (prefixWord ++ tailWord_8069160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069160).length < 2 ^ (prefixWord ++ tailWord_8069160).sum := by decide
  have hdescent : baseEnd_8069160 < baseStart_8069160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069216 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 4, 4]
def baseStart_8069216 : Nat := 118140960795 + 8069216 * 2 ^ 59
def prefixEnd_8069216 : Nat := 4983230072969 + 3 ^ 40 * 8069216 * 2
def baseEnd_8069216 : Nat := 1381128770983468796330119

theorem tailTrace_8069216 : CollatzResearch.WordTrace tailWord_8069216 prefixEnd_8069216 1381128770983468796330119 := by
  unfold tailWord_8069216
  simp only [CollatzResearch.WordTrace]
  refine ⟨147154242967308009610389751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196205657289744012813853001 147154242967308009610389751)
  ·
    refine ⟨220731364450962014415584627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147154242967308009610389751 220731364450962014415584627)
    ·
      refine ⟨331097046676443021623376941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220731364450962014415584627 331097046676443021623376941)
      ·
        refine ⟨124161392503666133108766353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331097046676443021623376941 124161392503666133108766353)
        ·
          refine ⟨93121044377749599831574765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124161392503666133108766353 93121044377749599831574765)
          ·
            refine ⟨34920391641656099936840537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93121044377749599831574765 34920391641656099936840537)
            ·
              refine ⟨26190293731242074952630403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34920391641656099936840537 26190293731242074952630403)
              ·
                refine ⟨39285440596863112428945605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26190293731242074952630403 39285440596863112428945605)
                ·
                  refine ⟨7366020111911833580427301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39285440596863112428945605 7366020111911833580427301)
                  ·
                    refine ⟨1381128770983468796330119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7366020111911833580427301 1381128770983468796330119)
                    ·
                      rfl

theorem cell23_8069216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_8069216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069216 prefixEnd_8069216 := by exact prefixLift 8069216
  have htrace : WordTrace (prefixWord ++ tailWord_8069216) baseStart_8069216 baseEnd_8069216 := by
    simpa [prefixWord, tailWord_8069216, baseEnd_8069216] using wordTrace_append hprefix tailTrace_8069216
  have hstable : (prefixWord ++ tailWord_8069216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069216).length < 2 ^ (prefixWord ++ tailWord_8069216).sum := by decide
  have hdescent : baseEnd_8069216 < baseStart_8069216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069219 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6]
def baseStart_8069219 : Nat := 118140960795 + 8069219 * 2 ^ 59
def prefixEnd_8069219 : Nat := 4983230072969 + 3 ^ 40 * 8069219 * 2
def baseEnd_8069219 : Nat := 4143387853392369877252843

theorem tailTrace_8069219 : CollatzResearch.WordTrace tailWord_8069219 prefixEnd_8069219 4143387853392369877252843 := by
  unfold tailWord_8069219
  simp only [CollatzResearch.WordTrace]
  refine ⟨294308595353605150733138711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196205730235736767155425807 294308595353605150733138711)
  ·
    refine ⟨441462893030407726099708067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294308595353605150733138711 441462893030407726099708067)
    ·
      refine ⟨662194339545611589149562101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441462893030407726099708067 662194339545611589149562101)
      ·
        refine ⟨62080719332401086482771447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 662194339545611589149562101 62080719332401086482771447)
        ·
          refine ⟨93121078998601629724157171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62080719332401086482771447 93121078998601629724157171)
          ·
            refine ⟨139681618497902444586235757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93121078998601629724157171 139681618497902444586235757)
            ·
              refine ⟨52380606936713416719838409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139681618497902444586235757 52380606936713416719838409)
              ·
                refine ⟨39285455202535062539878807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52380606936713416719838409 39285455202535062539878807)
                ·
                  refine ⟨58928182803802593809818211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39285455202535062539878807 58928182803802593809818211)
                  ·
                    refine ⟨88392274205703890714727317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58928182803802593809818211 88392274205703890714727317)
                    ·
                      refine ⟨4143387853392369877252843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88392274205703890714727317 4143387853392369877252843)
                      ·
                        rfl

theorem cell23_8069219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_8069219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069219 prefixEnd_8069219 := by exact prefixLift 8069219
  have htrace : WordTrace (prefixWord ++ tailWord_8069219) baseStart_8069219 baseEnd_8069219 := by
    simpa [prefixWord, tailWord_8069219, baseEnd_8069219] using wordTrace_append hprefix tailTrace_8069219
  have hstable : (prefixWord ++ tailWord_8069219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069219).length < 2 ^ (prefixWord ++ tailWord_8069219).sum := by decide
  have hdescent : baseEnd_8069219 < baseStart_8069219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069268 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_8069268 : Nat := 118140960795 + 8069268 * 2 ^ 59
def prefixEnd_8069268 : Nat := 4983230072969 + 3 ^ 40 * 8069268 * 2
def baseEnd_8069268 : Nat := 4143413013944440185540119

theorem tailTrace_8069268 : CollatzResearch.WordTrace tailWord_8069268 prefixEnd_8069268 4143413013944440185540119 := by
  unfold tailWord_8069268
  simp only [CollatzResearch.WordTrace]
  refine ⟨147155191265213816050836229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196206921686951754734448305 147155191265213816050836229)
  ·
    refine ⟨27591598362227590509531793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147155191265213816050836229 27591598362227590509531793)
    ·
      refine ⟨20693698771670692882148845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27591598362227590509531793 20693698771670692882148845)
      ·
        refine ⟨7760137039376509830805817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20693698771670692882148845 7760137039376509830805817)
        ·
          refine ⟨5820102779532382373104363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760137039376509830805817 5820102779532382373104363)
          ·
            refine ⟨8730154169298573559656545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820102779532382373104363 8730154169298573559656545)
            ·
              refine ⟨6547615626973930169742409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8730154169298573559656545 6547615626973930169742409)
              ·
                refine ⟨4910711720230447627306807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6547615626973930169742409 4910711720230447627306807)
                ·
                  refine ⟨7366067580345671440960211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910711720230447627306807 7366067580345671440960211)
                  ·
                    refine ⟨11049101370518507161440317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7366067580345671440960211 11049101370518507161440317)
                    ·
                      refine ⟨4143413013944440185540119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11049101370518507161440317 4143413013944440185540119)
                      ·
                        rfl

theorem cell23_8069268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_8069268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069268 prefixEnd_8069268 := by exact prefixLift 8069268
  have htrace : WordTrace (prefixWord ++ tailWord_8069268) baseStart_8069268 baseEnd_8069268 := by
    simpa [prefixWord, tailWord_8069268, baseEnd_8069268] using wordTrace_append hprefix tailTrace_8069268
  have hstable : (prefixWord ++ tailWord_8069268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069268).length < 2 ^ (prefixWord ++ tailWord_8069268).sum := by decide
  have hdescent : baseEnd_8069268 < baseStart_8069268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069274 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2]
def baseStart_8069274 : Nat := 118140960795 + 8069274 * 2 ^ 59
def prefixEnd_8069274 : Nat := 4983230072969 + 3 ^ 40 * 8069274 * 2
def baseEnd_8069274 : Nat := 4143416094828367162065091

theorem tailTrace_8069274 : CollatzResearch.WordTrace tailWord_8069274 prefixEnd_8069274 4143416094828367162065091 := by
  unfold tailWord_8069274
  simp only [CollatzResearch.WordTrace]
  refine ⟨73577650342101473781597719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196207067578937263417593917 73577650342101473781597719)
  ·
    refine ⟨110366475513152210672396579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73577650342101473781597719 110366475513152210672396579)
    ·
      refine ⟨165549713269728316008594869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110366475513152210672396579 165549713269728316008594869)
      ·
        refine ⟨15520285619037029625805769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165549713269728316008594869 15520285619037029625805769)
        ·
          refine ⟨11640214214277772219354327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15520285619037029625805769 11640214214277772219354327)
          ·
            refine ⟨17460321321416658329031491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640214214277772219354327 17460321321416658329031491)
            ·
              refine ⟨26190481982124987493547237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17460321321416658329031491 26190481982124987493547237)
              ·
                refine ⟨4910715371648435155040107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26190481982124987493547237 4910715371648435155040107)
                ·
                  refine ⟨7366073057472652732560161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910715371648435155040107 7366073057472652732560161)
                  ·
                    refine ⟨5524554793104489549420121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7366073057472652732560161 5524554793104489549420121)
                    ·
                      refine ⟨4143416094828367162065091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524554793104489549420121 4143416094828367162065091)
                      ·
                        rfl

theorem cell23_8069274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_8069274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069274 prefixEnd_8069274 := by exact prefixLift 8069274
  have htrace : WordTrace (prefixWord ++ tailWord_8069274) baseStart_8069274 baseEnd_8069274 := by
    simpa [prefixWord, tailWord_8069274, baseEnd_8069274] using wordTrace_append hprefix tailTrace_8069274
  have hstable : (prefixWord ++ tailWord_8069274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069274).length < 2 ^ (prefixWord ++ tailWord_8069274).sum := by decide
  have hdescent : baseEnd_8069274 < baseStart_8069274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069324 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_8069324 : Nat := 118140960795 + 8069324 * 2 ^ 59
def prefixEnd_8069324 : Nat := 4983230072969 + 3 ^ 40 * 8069324 * 2
def baseEnd_8069324 : Nat := 4143441768861091966439861

theorem tailTrace_8069324 : CollatzResearch.WordTrace tailWord_8069324 prefixEnd_8069324 4143441768861091966439861 := by
  unfold tailWord_8069324
  simp only [CollatzResearch.WordTrace]
  refine ⟨147156212509112376832855513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196208283345483169110474017 147156212509112376832855513)
  ·
    refine ⟨110367159381834282624641635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147156212509112376832855513 110367159381834282624641635)
    ·
      refine ⟨165550739072751423936962453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110367159381834282624641635 165550739072751423936962453)
      ·
        refine ⟨7760190894035222997045115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165550739072751423936962453 7760190894035222997045115)
        ·
          refine ⟨11640286341052834495567673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760190894035222997045115 11640286341052834495567673)
          ·
            refine ⟨8730214755789625871675755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11640286341052834495567673 8730214755789625871675755)
            ·
              refine ⟨13095322133684438807513633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8730214755789625871675755 13095322133684438807513633)
              ·
                refine ⟨9821491600263329105635225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13095322133684438807513633 9821491600263329105635225)
                ·
                  refine ⟨7366118700197496829226419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9821491600263329105635225 7366118700197496829226419)
                  ·
                    refine ⟨11049178050296245243839629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7366118700197496829226419 11049178050296245243839629)
                    ·
                      refine ⟨4143441768861091966439861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11049178050296245243839629 4143441768861091966439861)
                      ·
                        rfl

theorem cell23_8069324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_8069324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069324 prefixEnd_8069324 := by exact prefixLift 8069324
  have htrace : WordTrace (prefixWord ++ tailWord_8069324) baseStart_8069324 baseEnd_8069324 := by
    simpa [prefixWord, tailWord_8069324, baseEnd_8069324] using wordTrace_append hprefix tailTrace_8069324
  have hstable : (prefixWord ++ tailWord_8069324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069324).length < 2 ^ (prefixWord ++ tailWord_8069324).sum := by decide
  have hdescent : baseEnd_8069324 < baseStart_8069324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069336 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 7]
def baseStart_8069336 : Nat := 118140960795 + 8069336 * 2 ^ 59
def prefixEnd_8069336 : Nat := 4983230072969 + 3 ^ 40 * 8069336 * 2
def baseEnd_8069336 : Nat := 460383103403216213276645

theorem tailTrace_8069336 : CollatzResearch.WordTrace tailWord_8069336 prefixEnd_8069336 460383103403216213276645 := by
  unfold tailWord_8069336
  simp only [CollatzResearch.WordTrace]
  refine ⟨147156431347090639857573931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196208575129454186476765241 147156431347090639857573931)
  ·
    refine ⟨220734647020635959786360897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147156431347090639857573931 220734647020635959786360897)
    ·
      refine ⟨165550985265476969839770673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220734647020635959786360897 165550985265476969839770673)
      ·
        refine ⟨124163238949107727379828005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165550985265476969839770673 124163238949107727379828005)
        ·
          refine ⟨23280607302957698883717751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124163238949107727379828005 23280607302957698883717751)
          ·
            refine ⟨34920910954436548325576627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23280607302957698883717751 34920910954436548325576627)
            ·
              refine ⟨52381366431654822488364941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34920910954436548325576627 52381366431654822488364941)
              ·
                refine ⟨19643012411870558433136853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52381366431654822488364941 19643012411870558433136853)
                ·
                  refine ⟨460383103403216213276645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19643012411870558433136853 460383103403216213276645)
                  ·
                    rfl

theorem cell23_8069336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_8069336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069336 prefixEnd_8069336 := by exact prefixLift 8069336
  have htrace : WordTrace (prefixWord ++ tailWord_8069336) baseStart_8069336 baseEnd_8069336 := by
    simpa [prefixWord, tailWord_8069336, baseEnd_8069336] using wordTrace_append hprefix tailTrace_8069336
  have hstable : (prefixWord ++ tailWord_8069336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069336).length < 2 ^ (prefixWord ++ tailWord_8069336).sum := by decide
  have hdescent : baseEnd_8069336 < baseStart_8069336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069339 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_8069339 : Nat := 118140960795 + 8069339 * 2 ^ 59
def prefixEnd_8069339 : Nat := 4983230072969 + 3 ^ 40 * 8069339 * 2
def baseEnd_8069339 : Nat := 4143449471070909407752291

theorem tailTrace_8069339 : CollatzResearch.WordTrace tailWord_8069339 prefixEnd_8069339 4143449471070909407752291 := by
  unfold tailWord_8069339
  simp only [CollatzResearch.WordTrace]
  refine ⟨294312972113170411227507071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196208648075446940818338047 294312972113170411227507071)
  ·
    refine ⟨441469458169755616841260607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294312972113170411227507071 441469458169755616841260607)
    ·
      refine ⟨662204187254633425261890911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441469458169755616841260607 662204187254633425261890911)
      ·
        refine ⟨993306280881950137892836367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662204187254633425261890911 993306280881950137892836367)
        ·
          refine ⟨1489959421322925206839254551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993306280881950137892836367 1489959421322925206839254551)
          ·
            refine ⟨2234939131984387810258881827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489959421322925206839254551 2234939131984387810258881827)
            ·
              refine ⟨3352408697976581715388322741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234939131984387810258881827 3352408697976581715388322741)
              ·
                refine ⟨314288315435304535817655257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3352408697976581715388322741 314288315435304535817655257)
                ·
                  refine ⟨235716236576478401863241443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314288315435304535817655257 235716236576478401863241443)
                  ·
                    refine ⟨353574354864717602794862165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235716236576478401863241443 353574354864717602794862165)
                    ·
                      refine ⟨4143449471070909407752291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 353574354864717602794862165 4143449471070909407752291)
                      ·
                        rfl

theorem cell23_8069339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_8069339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069339 prefixEnd_8069339 := by exact prefixLift 8069339
  have htrace : WordTrace (prefixWord ++ tailWord_8069339) baseStart_8069339 baseEnd_8069339 := by
    simpa [prefixWord, tailWord_8069339, baseEnd_8069339] using wordTrace_append hprefix tailTrace_8069339
  have hstable : (prefixWord ++ tailWord_8069339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069339).length < 2 ^ (prefixWord ++ tailWord_8069339).sum := by decide
  have hdescent : baseEnd_8069339 < baseStart_8069339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069370 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 5]
def baseStart_8069370 : Nat := 118140960795 + 8069370 * 2 ^ 59
def prefixEnd_8069370 : Nat := 4983230072969 + 3 ^ 40 * 8069370 * 2
def baseEnd_8069370 : Nat := 460385043219022087384961

theorem tailTrace_8069370 : CollatzResearch.WordTrace tailWord_8069370 prefixEnd_8069370 460385043219022087384961 := by
  unfold tailWord_8069370
  simp only [CollatzResearch.WordTrace]
  refine ⟨73578525694014525880471391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196209401850705402347923709 73578525694014525880471391)
  ·
    refine ⟨110367788541021788820707087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73578525694014525880471391 110367788541021788820707087)
    ·
      refine ⟨165551682811532683231060631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110367788541021788820707087 165551682811532683231060631)
      ·
        refine ⟨248327524217299024846590947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165551682811532683231060631 248327524217299024846590947)
        ·
          refine ⟨372491286325948537269886421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248327524217299024846590947 372491286325948537269886421)
          ·
            refine ⟨8730264523264418842262963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 372491286325948537269886421 8730264523264418842262963)
            ·
              refine ⟨13095396784896628263394445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8730264523264418842262963 13095396784896628263394445)
              ·
                refine ⟨4910773794336235598772917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13095396784896628263394445 4910773794336235598772917)
                ·
                  refine ⟨460385043219022087384961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4910773794336235598772917 460385043219022087384961)
                  ·
                    rfl

theorem cell23_8069370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_8069370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069370 prefixEnd_8069370 := by exact prefixLift 8069370
  have htrace : WordTrace (prefixWord ++ tailWord_8069370) baseStart_8069370 baseEnd_8069370 := by
    simpa [prefixWord, tailWord_8069370, baseEnd_8069370] using wordTrace_append hprefix tailTrace_8069370
  have hstable : (prefixWord ++ tailWord_8069370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069370).length < 2 ^ (prefixWord ++ tailWord_8069370).sum := by decide
  have hdescent : baseEnd_8069370 < baseStart_8069370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069403 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 2, 4, 2]
def baseStart_8069403 : Nat := 118140960795 + 8069403 * 2 ^ 59
def prefixEnd_8069403 : Nat := 4983230072969 + 3 ^ 40 * 8069403 * 2
def baseEnd_8069403 : Nat := 4143482333832797157351997

theorem tailTrace_8069403 : CollatzResearch.WordTrace tailWord_8069403 prefixEnd_8069403 4143482333832797157351997 := by
  unfold tailWord_8069403
  simp only [CollatzResearch.WordTrace]
  refine ⟨294315306384938550157836863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196210204256625700105224575 294315306384938550157836863)
  ·
    refine ⟨441472959577407825236755295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294315306384938550157836863 441472959577407825236755295)
    ·
      refine ⟨662209439366111737855132943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441472959577407825236755295 662209439366111737855132943)
      ·
        refine ⟨993314159049167606782699415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662209439366111737855132943 993314159049167606782699415)
        ·
          refine ⟨1489971238573751410174049123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993314159049167606782699415 1489971238573751410174049123)
          ·
            refine ⟨2234956857860627115261073685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489971238573751410174049123 2234956857860627115261073685)
            ·
              refine ⟨104763602712216896027862829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2234956857860627115261073685 104763602712216896027862829)
              ·
                refine ⟨39286351017081336010448561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104763602712216896027862829 39286351017081336010448561)
                ·
                  refine ⟨29464763262811002007836421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39286351017081336010448561 29464763262811002007836421)
                  ·
                    refine ⟨5524643111777062876469329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29464763262811002007836421 5524643111777062876469329)
                    ·
                      refine ⟨4143482333832797157351997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524643111777062876469329 4143482333832797157351997)
                      ·
                        rfl

theorem cell23_8069403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4, 2].length) (baseStart_8069403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069403 prefixEnd_8069403 := by exact prefixLift 8069403
  have htrace : WordTrace (prefixWord ++ tailWord_8069403) baseStart_8069403 baseEnd_8069403 := by
    simpa [prefixWord, tailWord_8069403, baseEnd_8069403] using wordTrace_append hprefix tailTrace_8069403
  have hstable : (prefixWord ++ tailWord_8069403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069403).length < 2 ^ (prefixWord ++ tailWord_8069403).sum := by decide
  have hdescent : baseEnd_8069403 < baseStart_8069403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069423 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_8069423 : Nat := 118140960795 + 8069423 * 2 ^ 59
def prefixEnd_8069423 : Nat := 4983230072969 + 3 ^ 40 * 8069423 * 2
def baseEnd_8069423 : Nat := 4143492603445887079101905

theorem tailTrace_8069423 : CollatzResearch.WordTrace tailWord_8069423 prefixEnd_8069423 4143492603445887079101905 := by
  unfold tailWord_8069423
  simp only [CollatzResearch.WordTrace]
  refine ⟨294316035844866093573564923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196210690563244062382376615 294316035844866093573564923)
  ·
    refine ⟨441474053767299140360347385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294316035844866093573564923 441474053767299140360347385)
    ·
      refine ⟨331105540325474355270260539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441474053767299140360347385 331105540325474355270260539)
      ·
        refine ⟨496658310488211532905390809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331105540325474355270260539 496658310488211532905390809)
        ·
          refine ⟨372493732866158649679043107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496658310488211532905390809 372493732866158649679043107)
          ·
            refine ⟨558740599299237974518564661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372493732866158649679043107 558740599299237974518564661)
            ·
              refine ⟨52381931184303560111115437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558740599299237974518564661 52381931184303560111115437)
              ·
                refine ⟨19643224194113835041668289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52381931184303560111115437 19643224194113835041668289)
                ·
                  refine ⟨14732418145585376281251217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19643224194113835041668289 14732418145585376281251217)
                  ·
                    refine ⟨11049313609189032210938413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14732418145585376281251217 11049313609189032210938413)
                    ·
                      refine ⟨4143492603445887079101905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11049313609189032210938413 4143492603445887079101905)
                      ·
                        rfl

theorem cell23_8069423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_8069423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069423 prefixEnd_8069423 := by exact prefixLift 8069423
  have htrace : WordTrace (prefixWord ++ tailWord_8069423) baseStart_8069423 baseEnd_8069423 := by
    simpa [prefixWord, tailWord_8069423, baseEnd_8069423] using wordTrace_append hprefix tailTrace_8069423
  have hstable : (prefixWord ++ tailWord_8069423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069423).length < 2 ^ (prefixWord ++ tailWord_8069423).sum := by decide
  have hdescent : baseEnd_8069423 < baseStart_8069423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069466 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_8069466 : Nat := 118140960795 + 8069466 * 2 ^ 59
def prefixEnd_8069466 : Nat := 4983230072969 + 3 ^ 40 * 8069466 * 2
def baseEnd_8069466 : Nat := 4143514683114030410864207

theorem tailTrace_8069466 : CollatzResearch.WordTrace tailWord_8069466 prefixEnd_8069466 4143514683114030410864207 := by
  unfold tailWord_8069466
  simp only [CollatzResearch.WordTrace]
  refine ⟨73579401045927577979345063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196211736122473541278253501 73579401045927577979345063)
  ·
    refine ⟨110369101568891366969017595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73579401045927577979345063 110369101568891366969017595)
    ·
      refine ⟨165553652353337050453526393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110369101568891366969017595 165553652353337050453526393)
      ·
        refine ⟨124165239265002787840144795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165553652353337050453526393 124165239265002787840144795)
        ·
          refine ⟨186247858897504181760217193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124165239265002787840144795 186247858897504181760217193)
          ·
            refine ⟨139685894173128136320162895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186247858897504181760217193 139685894173128136320162895)
            ·
              refine ⟨209528841259692204480244343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139685894173128136320162895 209528841259692204480244343)
              ·
                refine ⟨314293261889538306720366515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209528841259692204480244343 314293261889538306720366515)
                ·
                  refine ⟨471439892834307460080549773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314293261889538306720366515 471439892834307460080549773)
                  ·
                    refine ⟨176789959812865297530206165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471439892834307460080549773 176789959812865297530206165)
                    ·
                      refine ⟨4143514683114030410864207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176789959812865297530206165 4143514683114030410864207)
                      ·
                        rfl

theorem cell23_8069466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_8069466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069466 prefixEnd_8069466 := by exact prefixLift 8069466
  have htrace : WordTrace (prefixWord ++ tailWord_8069466) baseStart_8069466 baseEnd_8069466 := by
    simpa [prefixWord, tailWord_8069466, baseEnd_8069466] using wordTrace_append hprefix tailTrace_8069466
  have hstable : (prefixWord ++ tailWord_8069466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069466).length < 2 ^ (prefixWord ++ tailWord_8069466).sum := by decide
  have hdescent : baseEnd_8069466 < baseStart_8069466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069490 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_8069490 : Nat := 118140960795 + 8069490 * 2 ^ 59
def prefixEnd_8069490 : Nat := 4983230072969 + 3 ^ 40 * 8069490 * 2
def baseEnd_8069490 : Nat := 1381175668883246105654699

theorem tailTrace_8069490 : CollatzResearch.WordTrace tailWord_8069490 prefixEnd_8069490 1381175668883246105654699 := by
  unfold tailWord_8069490
  simp only [CollatzResearch.WordTrace]
  refine ⟨73579619883905841004063481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196212319690415576010835949 73579619883905841004063481)
  ·
    refine ⟨55184714912929380753047611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73579619883905841004063481 55184714912929380753047611)
    ·
      refine ⟨82777072369394071129571417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55184714912929380753047611 82777072369394071129571417)
      ·
        refine ⟨62082804277045553347178563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82777072369394071129571417 62082804277045553347178563)
        ·
          refine ⟨93124206415568330020767845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62082804277045553347178563 93124206415568330020767845)
          ·
            refine ⟨17460788702919061878893971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93124206415568330020767845 17460788702919061878893971)
            ·
              refine ⟨26191183054378592818340957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17460788702919061878893971 26191183054378592818340957)
              ·
                refine ⟨9821693645391972306877859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26191183054378592818340957 9821693645391972306877859)
                ·
                  refine ⟨14732540468087958460316789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9821693645391972306877859 14732540468087958460316789)
                  ·
                    refine ⟨1381175668883246105654699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14732540468087958460316789 1381175668883246105654699)
                    ·
                      rfl

theorem cell23_8069490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_8069490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069490 prefixEnd_8069490 := by exact prefixLift 8069490
  have htrace : WordTrace (prefixWord ++ tailWord_8069490) baseStart_8069490 baseEnd_8069490 := by
    simpa [prefixWord, tailWord_8069490, baseEnd_8069490] using wordTrace_append hprefix tailTrace_8069490
  have hstable : (prefixWord ++ tailWord_8069490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069490).length < 2 ^ (prefixWord ++ tailWord_8069490).sum := by decide
  have hdescent : baseEnd_8069490 < baseStart_8069490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069494 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_8069494 : Nat := 118140960795 + 8069494 * 2 ^ 59
def prefixEnd_8069494 : Nat := 4983230072969 + 3 ^ 40 * 8069494 * 2
def baseEnd_8069494 : Nat := 460392117841372922368231

theorem tailTrace_8069494 : CollatzResearch.WordTrace tailWord_8069494 prefixEnd_8069494 460392117841372922368231 := by
  unfold tailWord_8069494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394914089225554543712471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196212416951739248466266357 18394914089225554543712471)
  ·
    refine ⟨27592371133838331815568707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18394914089225554543712471 27592371133838331815568707)
    ·
      refine ⟨41388556700757497723353061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27592371133838331815568707 41388556700757497723353061)
      ·
        refine ⟨7760354381392030823128699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41388556700757497723353061 7760354381392030823128699)
        ·
          refine ⟨11640531572088046234693049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760354381392030823128699 11640531572088046234693049)
          ·
            refine ⟨8730398679066034676019787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11640531572088046234693049 8730398679066034676019787)
            ·
              refine ⟨13095598018599052014029681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8730398679066034676019787 13095598018599052014029681)
              ·
                refine ⟨9821698513949289010522261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13095598018599052014029681 9821698513949289010522261)
                ·
                  refine ⟨460392117841372922368231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9821698513949289010522261 460392117841372922368231)
                  ·
                    rfl

theorem cell23_8069494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_8069494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069494 prefixEnd_8069494 := by exact prefixLift 8069494
  have htrace : WordTrace (prefixWord ++ tailWord_8069494) baseStart_8069494 baseEnd_8069494 := by
    simpa [prefixWord, tailWord_8069494, baseEnd_8069494] using wordTrace_append hprefix tailTrace_8069494
  have hstable : (prefixWord ++ tailWord_8069494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069494).length < 2 ^ (prefixWord ++ tailWord_8069494).sum := by decide
  have hdescent : baseEnd_8069494 < baseStart_8069494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069503 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 4, 4]
def baseStart_8069503 : Nat := 118140960795 + 8069503 * 2 ^ 59
def prefixEnd_8069503 : Nat := 4983230072969 + 3 ^ 40 * 8069503 * 2
def baseEnd_8069503 : Nat := 1381177893966082255367179

theorem tailTrace_8069503 : CollatzResearch.WordTrace tailWord_8069503 prefixEnd_8069503 1381177893966082255367179 := by
  unfold tailWord_8069503
  simp only [CollatzResearch.WordTrace]
  refine ⟨294318953684576267236477163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196212635789717511490984775 294318953684576267236477163)
  ·
    refine ⟨441478430526864400854715745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294318953684576267236477163 441478430526864400854715745)
    ·
      refine ⟨331108822895148300641036809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441478430526864400854715745 331108822895148300641036809)
      ·
        refine ⟨248331617171361225480777607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331108822895148300641036809 248331617171361225480777607)
        ·
          refine ⟨372497425757041838221166411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248331617171361225480777607 372497425757041838221166411)
          ·
            refine ⟨558746138635562757331749617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372497425757041838221166411 558746138635562757331749617)
            ·
              refine ⟨419059603976672067998812213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558746138635562757331749617 419059603976672067998812213)
              ·
                refine ⟨39286837872813006374888645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 419059603976672067998812213 39286837872813006374888645)
                ·
                  refine ⟨7366282101152438695291621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39286837872813006374888645 7366282101152438695291621)
                  ·
                    refine ⟨1381177893966082255367179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7366282101152438695291621 1381177893966082255367179)
                    ·
                      rfl

theorem cell23_8069503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_8069503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069503 prefixEnd_8069503 := by exact prefixLift 8069503
  have htrace : WordTrace (prefixWord ++ tailWord_8069503) baseStart_8069503 baseEnd_8069503 := by
    simpa [prefixWord, tailWord_8069503, baseEnd_8069503] using wordTrace_append hprefix tailTrace_8069503
  have hstable : (prefixWord ++ tailWord_8069503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069503).length < 2 ^ (prefixWord ++ tailWord_8069503).sum := by decide
  have hdescent : baseEnd_8069503 < baseStart_8069503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069513 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_8069513 : Nat := 118140960795 + 8069513 * 2 ^ 59
def prefixEnd_8069513 : Nat := 4983230072969 + 3 ^ 40 * 8069513 * 2
def baseEnd_8069513 : Nat := 4143538816704791726976491

theorem tailTrace_8069513 : CollatzResearch.WordTrace tailWord_8069513 prefixEnd_8069513 4143538816704791726976491 := by
  unfold tailWord_8069513
  simp only [CollatzResearch.WordTrace]
  refine ⟨294319318414540038944341193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196212878943026692629560795 294319318414540038944341193)
  ·
    refine ⟨220739488810905029208255895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294319318414540038944341193 220739488810905029208255895)
    ·
      refine ⟨331109233216357543812383843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220739488810905029208255895 331109233216357543812383843)
      ·
        refine ⟨496663849824536315718575765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331109233216357543812383843 496663849824536315718575765)
        ·
          refine ⟨23281117960525139799308239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 496663849824536315718575765 23281117960525139799308239)
          ·
            refine ⟨34921676940787709698962359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23281117960525139799308239 34921676940787709698962359)
            ·
              refine ⟨52382515411181564548443539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34921676940787709698962359 52382515411181564548443539)
              ·
                refine ⟨78573773116772346822665309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52382515411181564548443539 78573773116772346822665309)
                ·
                  refine ⟨29465164918789630058499491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78573773116772346822665309 29465164918789630058499491)
                  ·
                    refine ⟨44197747378184445087749237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29465164918789630058499491 44197747378184445087749237)
                    ·
                      refine ⟨4143538816704791726976491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44197747378184445087749237 4143538816704791726976491)
                      ·
                        rfl

theorem cell23_8069513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_8069513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069513 prefixEnd_8069513 := by exact prefixLift 8069513
  have htrace : WordTrace (prefixWord ++ tailWord_8069513) baseStart_8069513 baseEnd_8069513 := by
    simpa [prefixWord, tailWord_8069513, baseEnd_8069513] using wordTrace_append hprefix tailTrace_8069513
  have hstable : (prefixWord ++ tailWord_8069513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069513).length < 2 ^ (prefixWord ++ tailWord_8069513).sum := by decide
  have hdescent : baseEnd_8069513 < baseStart_8069513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069527 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 3, 2, 2]
def baseStart_8069527 : Nat := 118140960795 + 8069527 * 2 ^ 59
def prefixEnd_8069527 : Nat := 4983230072969 + 3 ^ 40 * 8069527 * 2
def baseEnd_8069527 : Nat := 4143546005433954672201427

theorem tailTrace_8069527 : CollatzResearch.WordTrace tailWord_8069527 prefixEnd_8069527 4143546005433954672201427 := by
  unfold tailWord_8069527
  simp only [CollatzResearch.WordTrace]
  refine ⟨294319829036489319335350835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196213219357659546223567223 294319829036489319335350835)
  ·
    refine ⟨441479743554733979003026253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294319829036489319335350835 441479743554733979003026253)
    ·
      refine ⟨165554903833025242126134845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441479743554733979003026253 165554903833025242126134845)
      ·
        refine ⟨62083088937384465797300567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165554903833025242126134845 62083088937384465797300567)
        ·
          refine ⟨93124633406076698695950851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62083088937384465797300567 93124633406076698695950851)
          ·
            refine ⟨139686950109115048043926277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93124633406076698695950851 139686950109115048043926277)
            ·
              refine ⟨26191303145459071508236177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139686950109115048043926277 26191303145459071508236177)
              ·
                refine ⟨19643477359094303631177133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26191303145459071508236177 19643477359094303631177133)
                ·
                  refine ⟨7366304009660363861691425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19643477359094303631177133 7366304009660363861691425)
                  ·
                    refine ⟨5524728007245272896268569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7366304009660363861691425 5524728007245272896268569)
                    ·
                      refine ⟨4143546005433954672201427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524728007245272896268569 4143546005433954672201427)
                      ·
                        rfl

theorem cell23_8069527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_8069527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069527 prefixEnd_8069527 := by exact prefixLift 8069527
  have htrace : WordTrace (prefixWord ++ tailWord_8069527) baseStart_8069527 baseEnd_8069527 := by
    simpa [prefixWord, tailWord_8069527, baseEnd_8069527] using wordTrace_append hprefix tailTrace_8069527
  have hstable : (prefixWord ++ tailWord_8069527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069527).length < 2 ^ (prefixWord ++ tailWord_8069527).sum := by decide
  have hdescent : baseEnd_8069527 < baseStart_8069527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069638 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_8069638 : Nat := 118140960795 + 8069638 * 2 ^ 59
def prefixEnd_8069638 : Nat := 4983230072969 + 3 ^ 40 * 8069638 * 2
def baseEnd_8069638 : Nat := 4143603001786603737913417

theorem tailTrace_8069638 : CollatzResearch.WordTrace tailWord_8069638 prefixEnd_8069638 4143603001786603737913417 := by
  unfold tailWord_8069638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197621173096474540395049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196215918359391456861761045 9197621173096474540395049)
  ·
    refine ⟨6898215879822355905296287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9197621173096474540395049 6898215879822355905296287)
    ·
      refine ⟨10347323819733533857944431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898215879822355905296287 10347323819733533857944431)
      ·
        refine ⟨15520985729600300786916647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10347323819733533857944431 15520985729600300786916647)
        ·
          refine ⟨23281478594400451180374971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15520985729600300786916647 23281478594400451180374971)
          ·
            refine ⟨34922217891600676770562457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23281478594400451180374971 34922217891600676770562457)
            ·
              refine ⟨26191663418700507577921843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34922217891600676770562457 26191663418700507577921843)
              ·
                refine ⟨39287495128050761366882765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26191663418700507577921843 39287495128050761366882765)
                ·
                  refine ⟨14732810673019035512581037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39287495128050761366882765 14732810673019035512581037)
                  ·
                    refine ⟨5524804002382138317217889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14732810673019035512581037 5524804002382138317217889)
                    ·
                      refine ⟨4143603001786603737913417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524804002382138317217889 4143603001786603737913417)
                      ·
                        rfl

theorem cell23_8069638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_8069638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069638 prefixEnd_8069638 := by exact prefixLift 8069638
  have htrace : WordTrace (prefixWord ++ tailWord_8069638) baseStart_8069638 baseEnd_8069638 := by
    simpa [prefixWord, tailWord_8069638, baseEnd_8069638] using wordTrace_append hprefix tailTrace_8069638
  have hstable : (prefixWord ++ tailWord_8069638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069638).length < 2 ^ (prefixWord ++ tailWord_8069638).sum := by decide
  have hdescent : baseEnd_8069638 < baseStart_8069638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069655 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 1, 3, 2]
def baseStart_8069655 : Nat := 118140960795 + 8069655 * 2 ^ 59
def prefixEnd_8069655 : Nat := 4983230072969 + 3 ^ 40 * 8069655 * 2
def baseEnd_8069655 : Nat := 4143611730957730171400839

theorem tailTrace_8069655 : CollatzResearch.WordTrace tailWord_8069655 prefixEnd_8069655 4143611730957730171400839 := by
  unfold tailWord_8069655
  simp only [CollatzResearch.WordTrace]
  refine ⟨294324497580025597196010419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196216331720017064797340279 294324497580025597196010419)
  ·
    refine ⟨441486746370038395794015629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294324497580025597196010419 441486746370038395794015629)
    ·
      refine ⟨165557529888764398422755861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441486746370038395794015629 165557529888764398422755861)
      ·
        refine ⟨7760509213535831176066681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165557529888764398422755861 7760509213535831176066681)
        ·
          refine ⟨5820381910151873382050011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760509213535831176066681 5820381910151873382050011)
          ·
            refine ⟨8730572865227810073075017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820381910151873382050011 8730572865227810073075017)
            ·
              refine ⟨6547929648920857554806263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8730572865227810073075017 6547929648920857554806263)
              ·
                refine ⟨9821894473381286332209395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547929648920857554806263 9821894473381286332209395)
                ·
                  refine ⟨14732841710071929498314093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9821894473381286332209395 14732841710071929498314093)
                  ·
                    refine ⟨5524815641276973561867785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14732841710071929498314093 5524815641276973561867785)
                    ·
                      refine ⟨4143611730957730171400839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524815641276973561867785 4143611730957730171400839)
                      ·
                        rfl

theorem cell23_8069655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_8069655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069655 prefixEnd_8069655 := by exact prefixLift 8069655
  have htrace : WordTrace (prefixWord ++ tailWord_8069655) baseStart_8069655 baseEnd_8069655 := by
    simpa [prefixWord, tailWord_8069655, baseEnd_8069655] using wordTrace_append hprefix tailTrace_8069655
  have hstable : (prefixWord ++ tailWord_8069655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069655).length < 2 ^ (prefixWord ++ tailWord_8069655).sum := by decide
  have hdescent : baseEnd_8069655 < baseStart_8069655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069690 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_8069690 : Nat := 118140960795 + 8069690 * 2 ^ 59
def prefixEnd_8069690 : Nat := 4983230072969 + 3 ^ 40 * 8069690 * 2
def baseEnd_8069690 : Nat := 4143629702780637534463177

theorem tailTrace_8069690 : CollatzResearch.WordTrace tailWord_8069690 prefixEnd_8069690 4143629702780637534463177 := by
  unfold tailWord_8069690
  simp only [CollatzResearch.WordTrace]
  refine ⟨73581443533724699543383631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196217182756599198782356349 73581443533724699543383631)
  ·
    refine ⟨110372165300587049315075447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73581443533724699543383631 110372165300587049315075447)
    ·
      refine ⟨165558247950880573972613171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110372165300587049315075447 165558247950880573972613171)
      ·
        refine ⟨248337371926320860958919757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165558247950880573972613171 248337371926320860958919757)
        ·
          refine ⟨93126514472370322859594909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248337371926320860958919757 93126514472370322859594909)
          ·
            refine ⟨34922442927138871072348091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93126514472370322859594909 34922442927138871072348091)
            ·
              refine ⟨52383664390708306608522137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34922442927138871072348091 52383664390708306608522137)
              ·
                refine ⟨39287748293031229956391603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52383664390708306608522137 39287748293031229956391603)
                ·
                  refine ⟨58931622439546844934587405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39287748293031229956391603 58931622439546844934587405)
                  ·
                    refine ⟨22099358414830066850470277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58931622439546844934587405 22099358414830066850470277)
                    ·
                      refine ⟨4143629702780637534463177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22099358414830066850470277 4143629702780637534463177)
                      ·
                        rfl

theorem cell23_8069690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_8069690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069690 prefixEnd_8069690 := by exact prefixLift 8069690
  have htrace : WordTrace (prefixWord ++ tailWord_8069690) baseStart_8069690 baseEnd_8069690 := by
    simpa [prefixWord, tailWord_8069690, baseEnd_8069690] using wordTrace_append hprefix tailTrace_8069690
  have hstable : (prefixWord ++ tailWord_8069690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069690).length < 2 ^ (prefixWord ++ tailWord_8069690).sum := by decide
  have hdescent : baseEnd_8069690 < baseStart_8069690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069724 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_8069724 : Nat := 118140960795 + 8069724 * 2 ^ 59
def prefixEnd_8069724 : Nat := 4983230072969 + 3 ^ 40 * 8069724 * 2
def baseEnd_8069724 : Nat := 4143647161122890401438021

theorem tailTrace_8069724 : CollatzResearch.WordTrace tailWord_8069724 prefixEnd_8069724 4143647161122890401438021 := by
  unfold tailWord_8069724
  simp only [CollatzResearch.WordTrace]
  refine ⟨147163507108387810990136113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196218009477850414653514817 147163507108387810990136113)
  ·
    refine ⟨110372630331290858242602085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147163507108387810990136113 110372630331290858242602085)
    ·
      refine ⟨20694868187117035920487891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110372630331290858242602085 20694868187117035920487891)
      ·
        refine ⟨31042302280675553880731837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20694868187117035920487891 31042302280675553880731837)
        ·
          refine ⟨11640863355253332705274439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31042302280675553880731837 11640863355253332705274439)
          ·
            refine ⟨17461295032879999057911659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640863355253332705274439 17461295032879999057911659)
            ·
              refine ⟨26191942549319998586867489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17461295032879999057911659 26191942549319998586867489)
              ·
                refine ⟨19643956911989998940150617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26191942549319998586867489 19643956911989998940150617)
                ·
                  refine ⟨14732967683992499205112963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19643956911989998940150617 14732967683992499205112963)
                  ·
                    refine ⟨22099451525988748807669445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14732967683992499205112963 22099451525988748807669445)
                    ·
                      refine ⟨4143647161122890401438021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22099451525988748807669445 4143647161122890401438021)
                      ·
                        rfl

theorem cell23_8069724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_8069724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069724 prefixEnd_8069724 := by exact prefixLift 8069724
  have htrace : WordTrace (prefixWord ++ tailWord_8069724) baseStart_8069724 baseEnd_8069724 := by
    simpa [prefixWord, tailWord_8069724, baseEnd_8069724] using wordTrace_append hprefix tailTrace_8069724
  have hstable : (prefixWord ++ tailWord_8069724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069724).length < 2 ^ (prefixWord ++ tailWord_8069724).sum := by decide
  have hdescent : baseEnd_8069724 < baseStart_8069724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069784 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 2, 3, 2]
def baseStart_8069784 : Nat := 118140960795 + 8069784 * 2 ^ 59
def prefixEnd_8069784 : Nat := 4983230072969 + 3 ^ 40 * 8069784 * 2
def baseEnd_8069784 : Nat := 4143677969962160166687745

theorem tailTrace_8069784 : CollatzResearch.WordTrace tailWord_8069784 prefixEnd_8069784 4143677969962160166687745 := by
  unfold tailWord_8069784
  simp only [CollatzResearch.WordTrace]
  refine ⟨147164601298279126113728203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196219468397705501484970937 147164601298279126113728203)
  ·
    refine ⟨220746901947418689170592305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147164601298279126113728203 220746901947418689170592305)
    ·
      refine ⟨165560176460564016877944229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220746901947418689170592305 165560176460564016877944229)
      ·
        refine ⟨31042533086355753164614543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165560176460564016877944229 31042533086355753164614543)
        ·
          refine ⟨46563799629533629746921815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31042533086355753164614543 46563799629533629746921815)
          ·
            refine ⟨69845699444300444620382723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46563799629533629746921815 69845699444300444620382723)
            ·
              refine ⟨104768549166450666930574085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69845699444300444620382723 104768549166450666930574085)
              ·
                refine ⟨19644102968709500049482641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104768549166450666930574085 19644102968709500049482641)
                ·
                  refine ⟨14733077226532125037111981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19644102968709500049482641 14733077226532125037111981)
                  ·
                    refine ⟨5524903959949546888916993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14733077226532125037111981 5524903959949546888916993)
                    ·
                      refine ⟨4143677969962160166687745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524903959949546888916993 4143677969962160166687745)
                      ·
                        rfl

theorem cell23_8069784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_8069784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069784 prefixEnd_8069784 := by exact prefixLift 8069784
  have htrace : WordTrace (prefixWord ++ tailWord_8069784) baseStart_8069784 baseEnd_8069784 := by
    simpa [prefixWord, tailWord_8069784, baseEnd_8069784] using wordTrace_append hprefix tailTrace_8069784
  have hstable : (prefixWord ++ tailWord_8069784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069784).length < 2 ^ (prefixWord ++ tailWord_8069784).sum := by decide
  have hdescent : baseEnd_8069784 < baseStart_8069784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069797 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 6, 2]
def baseStart_8069797 : Nat := 118140960795 + 8069797 * 2 ^ 59
def prefixEnd_8069797 : Nat := 4983230072969 + 3 ^ 40 * 8069797 * 2
def baseEnd_8069797 : Nat := 4143684645210668615825185

theorem tailTrace_8069797 : CollatzResearch.WordTrace tailWord_8069797 prefixEnd_8069797 4143684645210668615825185 := by
  unfold tailWord_8069797
  simp only [CollatzResearch.WordTrace]
  refine ⟨294329676745511155447679645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196219784497007436965119763 294329676745511155447679645)
  ·
    refine ⟨110373628779566683292879867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294329676745511155447679645 110373628779566683292879867)
    ·
      refine ⟨165560443169350024939319801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110373628779566683292879867 165560443169350024939319801)
      ·
        refine ⟨124170332377012518704489851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165560443169350024939319801 124170332377012518704489851)
        ·
          refine ⟨186255498565518778056734777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124170332377012518704489851 186255498565518778056734777)
          ·
            refine ⟨139691623924139083542551083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186255498565518778056734777 139691623924139083542551083)
            ·
              refine ⟨209537435886208625313826625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139691623924139083542551083 209537435886208625313826625)
              ·
                refine ⟨157153076914656468985369969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209537435886208625313826625 157153076914656468985369969)
                ·
                  refine ⟨117864807685992351739027477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157153076914656468985369969 117864807685992351739027477)
                  ·
                    refine ⟨5524912860280891487766913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117864807685992351739027477 5524912860280891487766913)
                    ·
                      refine ⟨4143684645210668615825185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524912860280891487766913 4143684645210668615825185)
                      ·
                        rfl

theorem cell23_8069797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_8069797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069797 prefixEnd_8069797 := by exact prefixLift 8069797
  have htrace : WordTrace (prefixWord ++ tailWord_8069797) baseStart_8069797 baseEnd_8069797 := by
    simpa [prefixWord, tailWord_8069797, baseEnd_8069797] using wordTrace_append hprefix tailTrace_8069797
  have hstable : (prefixWord ++ tailWord_8069797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069797).length < 2 ^ (prefixWord ++ tailWord_8069797).sum := by decide
  have hdescent : baseEnd_8069797 < baseStart_8069797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069807 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 1, 6]
def baseStart_8069807 : Nat := 118140960795 + 8069807 * 2 ^ 59
def prefixEnd_8069807 : Nat := 4983230072969 + 3 ^ 40 * 8069807 * 2
def baseEnd_8069807 : Nat := 1381229926672404525566713

theorem tailTrace_8069807 : CollatzResearch.WordTrace tailWord_8069807 prefixEnd_8069807 1381229926672404525566713 := by
  unfold tailWord_8069807
  simp only [CollatzResearch.WordTrace]
  refine ⟨294330041475474927155543675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196220027650316618103695783 294330041475474927155543675)
  ·
    refine ⟨441495062213212390733315513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294330041475474927155543675 441495062213212390733315513)
    ·
      refine ⟨331121296659909293049986635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441495062213212390733315513 331121296659909293049986635)
      ·
        refine ⟨496681944989863939574979953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331121296659909293049986635 496681944989863939574979953)
        ·
          refine ⟨372511458742397954681234965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496681944989863939574979953 372511458742397954681234965)
          ·
            refine ⟨17461474628549904125682889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 372511458742397954681234965 17461474628549904125682889)
            ·
              refine ⟨13096105971412428094262167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17461474628549904125682889 13096105971412428094262167)
              ·
                refine ⟨19644158957118642141393251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13096105971412428094262167 19644158957118642141393251)
                ·
                  refine ⟨29466238435677963212089877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19644158957118642141393251 29466238435677963212089877)
                  ·
                    refine ⟨1381229926672404525566713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29466238435677963212089877 1381229926672404525566713)
                    ·
                      rfl

theorem cell23_8069807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_8069807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069807 prefixEnd_8069807 := by exact prefixLift 8069807
  have htrace : WordTrace (prefixWord ++ tailWord_8069807) baseStart_8069807 baseEnd_8069807 := by
    simpa [prefixWord, tailWord_8069807, baseEnd_8069807] using wordTrace_append hprefix tailTrace_8069807
  have hstable : (prefixWord ++ tailWord_8069807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069807).length < 2 ^ (prefixWord ++ tailWord_8069807).sum := by decide
  have hdescent : baseEnd_8069807 < baseStart_8069807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069848 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 1, 2, 2]
def baseStart_8069848 : Nat := 118140960795 + 8069848 * 2 ^ 59
def prefixEnd_8069848 : Nat := 4983230072969 + 3 ^ 40 * 8069848 * 2
def baseEnd_8069848 : Nat := 4143710832724047916287451

theorem tailTrace_8069848 : CollatzResearch.WordTrace tailWord_8069848 prefixEnd_8069848 4143710832724047916287451 := by
  unfold tailWord_8069848
  simp only [CollatzResearch.WordTrace]
  refine ⟨147165768434163195578893099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196221024578884260771857465 147165768434163195578893099)
  ·
    refine ⟨220748652651244793368339649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147165768434163195578893099 220748652651244793368339649)
    ·
      refine ⟨165561489488433595026254737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220748652651244793368339649 165561489488433595026254737)
      ·
        refine ⟨124171117116325196269691053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165561489488433595026254737 124171117116325196269691053)
        ·
          refine ⟨46564168918621948601134145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124171117116325196269691053 46564168918621948601134145)
          ·
            refine ⟨34923126688966461450850609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46564168918621948601134145 34923126688966461450850609)
            ·
              refine ⟨26192345016724846088137957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34923126688966461450850609 26192345016724846088137957)
              ·
                refine ⟨4911064690635908641525867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26192345016724846088137957 4911064690635908641525867)
                ·
                  refine ⟨7366597035953862962288801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911064690635908641525867 7366597035953862962288801)
                  ·
                    refine ⟨5524947776965397221716601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7366597035953862962288801 5524947776965397221716601)
                    ·
                      refine ⟨4143710832724047916287451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5524947776965397221716601 4143710832724047916287451)
                      ·
                        rfl

theorem cell23_8069848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_8069848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069848 prefixEnd_8069848 := by exact prefixLift 8069848
  have htrace : WordTrace (prefixWord ++ tailWord_8069848) baseStart_8069848 baseEnd_8069848 := by
    simpa [prefixWord, tailWord_8069848, baseEnd_8069848] using wordTrace_append hprefix tailTrace_8069848
  have hstable : (prefixWord ++ tailWord_8069848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069848).length < 2 ^ (prefixWord ++ tailWord_8069848).sum := by decide
  have hdescent : baseEnd_8069848 < baseStart_8069848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069907 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 3]
def baseStart_8069907 : Nat := 118140960795 + 8069907 * 2 ^ 59
def prefixEnd_8069907 : Nat := 4983230072969 + 3 ^ 40 * 8069907 * 2
def baseEnd_8069907 : Nat := 4143741128082663185449679

theorem tailTrace_8069907 : CollatzResearch.WordTrace tailWord_8069907 prefixEnd_8069907 4143741128082663185449679 := by
  unfold tailWord_8069907
  simp only [CollatzResearch.WordTrace]
  refine ⟨294333688775112644234183975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196222459183408429489455983 294333688775112644234183975)
  ·
    refine ⟨441500533162668966351275963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294333688775112644234183975 441500533162668966351275963)
    ·
      refine ⟨662250799744003449526913945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441500533162668966351275963 662250799744003449526913945)
      ·
        refine ⟨496688099808002587145185459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662250799744003449526913945 496688099808002587145185459)
        ·
          refine ⟨745032149712003880717778189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496688099808002587145185459 745032149712003880717778189)
          ·
            refine ⟨279387056142001455269166821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745032149712003880717778189 279387056142001455269166821)
            ·
              refine ⟨52385073026625272862968779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279387056142001455269166821 52385073026625272862968779)
              ·
                refine ⟨78577609539937909294453169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52385073026625272862968779 78577609539937909294453169)
                ·
                  refine ⟨58933207154953431970839877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78577609539937909294453169 58933207154953431970839877)
                  ·
                    refine ⟨11049976341553768494532477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58933207154953431970839877 11049976341553768494532477)
                    ·
                      refine ⟨4143741128082663185449679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11049976341553768494532477 4143741128082663185449679)
                      ·
                        rfl

theorem cell23_8069907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_8069907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069907 prefixEnd_8069907 := by exact prefixLift 8069907
  have htrace : WordTrace (prefixWord ++ tailWord_8069907) baseStart_8069907 baseEnd_8069907 := by
    simpa [prefixWord, tailWord_8069907, baseEnd_8069907] using wordTrace_append hprefix tailTrace_8069907
  have hstable : (prefixWord ++ tailWord_8069907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069907).length < 2 ^ (prefixWord ++ tailWord_8069907).sum := by decide
  have hdescent : baseEnd_8069907 < baseStart_8069907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069942 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_8069942 : Nat := 118140960795 + 8069942 * 2 ^ 59
def prefixEnd_8069942 : Nat := 4983230072969 + 3 ^ 40 * 8069942 * 2
def baseEnd_8069942 : Nat := 4143759099905570548512019

theorem tailTrace_8069942 : CollatzResearch.WordTrace tailWord_8069942 prefixEnd_8069942 4143759099905570548512019 := by
  unfold tailWord_8069942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18395935333124115325731755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196223310219990563474472053 18395935333124115325731755)
  ·
    refine ⟨27593902999686172988597633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18395935333124115325731755 27593902999686172988597633)
    ·
      refine ⟨20695427249764629741448225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27593902999686172988597633 20695427249764629741448225)
      ·
        refine ⟨15521570437323472306086169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20695427249764629741448225 15521570437323472306086169)
        ·
          refine ⟨11641177827992604229564627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15521570437323472306086169 11641177827992604229564627)
          ·
            refine ⟨17461766741988906344346941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11641177827992604229564627 17461766741988906344346941)
            ·
              refine ⟨6548162528245839879130103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17461766741988906344346941 6548162528245839879130103)
              ·
                refine ⟨9822243792368759818695155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548162528245839879130103 9822243792368759818695155)
                ·
                  refine ⟨14733365688553139728042733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9822243792368759818695155 14733365688553139728042733)
                  ·
                    refine ⟨5525012133207427398016025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14733365688553139728042733 5525012133207427398016025)
                    ·
                      refine ⟨4143759099905570548512019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525012133207427398016025 4143759099905570548512019)
                      ·
                        rfl

theorem cell23_8069942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_8069942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069942 prefixEnd_8069942 := by exact prefixLift 8069942
  have htrace : WordTrace (prefixWord ++ tailWord_8069942) baseStart_8069942 baseEnd_8069942 := by
    simpa [prefixWord, tailWord_8069942, baseEnd_8069942] using wordTrace_append hprefix tailTrace_8069942
  have hstable : (prefixWord ++ tailWord_8069942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069942).length < 2 ^ (prefixWord ++ tailWord_8069942).sum := by decide
  have hdescent : baseEnd_8069942 < baseStart_8069942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069944 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 5]
def baseStart_8069944 : Nat := 118140960795 + 8069944 * 2 ^ 59
def prefixEnd_8069944 : Nat := 4983230072969 + 3 ^ 40 * 8069944 * 2
def baseEnd_8069944 : Nat := 460417791874097726743001

theorem tailTrace_8069944 : CollatzResearch.WordTrace tailWord_8069944 prefixEnd_8069944 460417791874097726743001 := by
  unfold tailWord_8069944
  simp only [CollatzResearch.WordTrace]
  refine ⟨147167519137989299776640443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196223358850652399702187257 147167519137989299776640443)
  ·
    refine ⟨220751278706983949664960665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147167519137989299776640443 220751278706983949664960665)
    ·
      refine ⟨165563459030237962248720499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220751278706983949664960665 165563459030237962248720499)
      ·
        refine ⟨248345188545356943373080749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165563459030237962248720499 248345188545356943373080749)
        ·
          refine ⟨93129445704508853764905281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248345188545356943373080749 93129445704508853764905281)
          ·
            refine ⟨69847084278381640323678961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93129445704508853764905281 69847084278381640323678961)
            ·
              refine ⟨52385313208786230242759221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69847084278381640323678961 52385313208786230242759221)
              ·
                refine ⟨4911123113323709085258677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52385313208786230242759221 4911123113323709085258677)
                ·
                  refine ⟨460417791874097726743001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4911123113323709085258677 460417791874097726743001)
                  ·
                    rfl

theorem cell23_8069944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 5].length) (baseStart_8069944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069944 prefixEnd_8069944 := by exact prefixLift 8069944
  have htrace : WordTrace (prefixWord ++ tailWord_8069944) baseStart_8069944 baseEnd_8069944 := by
    simpa [prefixWord, tailWord_8069944, baseEnd_8069944] using wordTrace_append hprefix tailTrace_8069944
  have hstable : (prefixWord ++ tailWord_8069944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069944).length < 2 ^ (prefixWord ++ tailWord_8069944).sum := by decide
  have hdescent : baseEnd_8069944 < baseStart_8069944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069957 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_8069957 : Nat := 118140960795 + 8069957 * 2 ^ 59
def prefixEnd_8069957 : Nat := 4983230072969 + 3 ^ 40 * 8069957 * 2
def baseEnd_8069957 : Nat := 1381255600705129329941483

theorem tailTrace_8069957 : CollatzResearch.WordTrace tailWord_8069957 prefixEnd_8069957 1381255600705129329941483 := by
  unfold tailWord_8069957
  simp only [CollatzResearch.WordTrace]
  refine ⟨294335512424931502773504125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196223674949954335182336083 294335512424931502773504125)
  ·
    refine ⟨110375817159349313540064047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294335512424931502773504125 110375817159349313540064047)
    ·
      refine ⟨165563725739023970310096071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110375817159349313540064047 165563725739023970310096071)
      ·
        refine ⟨248345588608535955465144107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165563725739023970310096071 248345588608535955465144107)
        ·
          refine ⟨372518382912803933197716161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248345588608535955465144107 372518382912803933197716161)
          ·
            refine ⟨279388787184602949898287121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372518382912803933197716161 279388787184602949898287121)
            ·
              refine ⟨209541590388452212423715341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279388787184602949898287121 209541590388452212423715341)
              ·
                refine ⟨78578096395669579658893253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209541590388452212423715341 78578096395669579658893253)
                ·
                  refine ⟨14733393074188046186042485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78578096395669579658893253 14733393074188046186042485)
                  ·
                    refine ⟨1381255600705129329941483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14733393074188046186042485 1381255600705129329941483)
                    ·
                      rfl

theorem cell23_8069957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_8069957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069957 prefixEnd_8069957 := by exact prefixLift 8069957
  have htrace : WordTrace (prefixWord ++ tailWord_8069957) baseStart_8069957 baseEnd_8069957 := by
    simpa [prefixWord, tailWord_8069957, baseEnd_8069957] using wordTrace_append hprefix tailTrace_8069957
  have hstable : (prefixWord ++ tailWord_8069957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069957).length < 2 ^ (prefixWord ++ tailWord_8069957).sum := by decide
  have hdescent : baseEnd_8069957 < baseStart_8069957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069961 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 5]
def baseStart_8069961 : Nat := 118140960795 + 8069961 * 2 ^ 59
def prefixEnd_8069961 : Nat := 4983230072969 + 3 ^ 40 * 8069961 * 2
def baseEnd_8069961 : Nat := 460418761782000663797159

theorem tailTrace_8069961 : CollatzResearch.WordTrace tailWord_8069961 prefixEnd_8069961 460418761782000663797159 := by
  unfold tailWord_8069961
  simp only [CollatzResearch.WordTrace]
  refine ⟨294335658316917011456649737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196223772211278007637766491 294335658316917011456649737)
  ·
    refine ⟨220751743737687758592487303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294335658316917011456649737 220751743737687758592487303)
    ·
      refine ⟨331127615606531637888730955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220751743737687758592487303 331127615606531637888730955)
      ·
        refine ⟨496691423409797456833096433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331127615606531637888730955 496691423409797456833096433)
        ·
          refine ⟨372518567557348092624822325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496691423409797456833096433 372518567557348092624822325)
          ·
            refine ⟨34923615708501383683577093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 372518567557348092624822325 34923615708501383683577093)
            ·
              refine ⟨6548177945344009440670705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34923615708501383683577093 6548177945344009440670705)
              ·
                refine ⟨4911133459008007080503029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6548177945344009440670705 4911133459008007080503029)
                ·
                  refine ⟨460418761782000663797159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4911133459008007080503029 460418761782000663797159)
                  ·
                    rfl

theorem cell23_8069961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 5].length) (baseStart_8069961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069961 prefixEnd_8069961 := by exact prefixLift 8069961
  have htrace : WordTrace (prefixWord ++ tailWord_8069961) baseStart_8069961 baseEnd_8069961 := by
    simpa [prefixWord, tailWord_8069961, baseEnd_8069961] using wordTrace_append hprefix tailTrace_8069961
  have hstable : (prefixWord ++ tailWord_8069961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069961).length < 2 ^ (prefixWord ++ tailWord_8069961).sum := by decide
  have hdescent : baseEnd_8069961 < baseStart_8069961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8069991 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 2, 5]
def baseStart_8069991 : Nat := 118140960795 + 8069991 * 2 ^ 59
def prefixEnd_8069991 : Nat := 4983230072969 + 3 ^ 40 * 8069991 * 2
def baseEnd_8069991 : Nat := 1381261420152546952266431

theorem tailTrace_8069991 : CollatzResearch.WordTrace tailWord_8069991 prefixEnd_8069991 1381261420152546952266431 := by
  unfold tailWord_8069991
  simp only [CollatzResearch.WordTrace]
  refine ⟨294336752506808326580241827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196224501671205551053494551 294336752506808326580241827)
  ·
    refine ⟨441505128760212489870362741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294336752506808326580241827 441505128760212489870362741)
    ·
      refine ⟨41391105821269920925346507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441505128760212489870362741 41391105821269920925346507)
      ·
        refine ⟨62086658731904881388019761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41391105821269920925346507 62086658731904881388019761)
        ·
          refine ⟨46564994048928661041014821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62086658731904881388019761 46564994048928661041014821)
          ·
            refine ⟨8730936384174123945190279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46564994048928661041014821 8730936384174123945190279)
            ·
              refine ⟨13096404576261185917785419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8730936384174123945190279 13096404576261185917785419)
              ·
                refine ⟨19644606864391778876678129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13096404576261185917785419 19644606864391778876678129)
                ·
                  refine ⟨14733455148293834157508597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19644606864391778876678129 14733455148293834157508597)
                  ·
                    refine ⟨1381261420152546952266431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14733455148293834157508597 1381261420152546952266431)
                    ·
                      rfl

theorem cell23_8069991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_8069991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8069991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8069991 prefixEnd_8069991 := by exact prefixLift 8069991
  have htrace : WordTrace (prefixWord ++ tailWord_8069991) baseStart_8069991 baseEnd_8069991 := by
    simpa [prefixWord, tailWord_8069991, baseEnd_8069991] using wordTrace_append hprefix tailTrace_8069991
  have hstable : (prefixWord ++ tailWord_8069991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8069991).length < 2 ^ (prefixWord ++ tailWord_8069991).sum := by decide
  have hdescent : baseEnd_8069991 < baseStart_8069991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8069991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070007 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_8070007 : Nat := 118140960795 + 8070007 * 2 ^ 59
def prefixEnd_8070007 : Nat := 4983230072969 + 3 ^ 40 * 8070007 * 2
def baseEnd_8070007 : Nat := 4143792476148112794199219

theorem tailTrace_8070007 : CollatzResearch.WordTrace tailWord_8070007 prefixEnd_8070007 4143792476148112794199219 := by
  unfold tailWord_8070007
  simp only [CollatzResearch.WordTrace]
  refine ⟨294337336074750361312824275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196224890716500240875216183 294337336074750361312824275)
  ·
    refine ⟨441506004112125541969236413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294337336074750361312824275 441506004112125541969236413)
    ·
      refine ⟨165564751542047078238463655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441506004112125541969236413 165564751542047078238463655)
      ·
        refine ⟨248347127313070617357695483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165564751542047078238463655 248347127313070617357695483)
        ·
          refine ⟨372520690969605926036543225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248347127313070617357695483 372520690969605926036543225)
          ·
            refine ⟨279390518227204444527407419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372520690969605926036543225 279390518227204444527407419)
            ·
              refine ⟨419085777340806666791111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279390518227204444527407419 419085777340806666791111129)
              ·
                refine ⟨314314333005605000093333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419085777340806666791111129 314314333005605000093333347)
                ·
                  refine ⟨471471499508407500140000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314314333005605000093333347 471471499508407500140000021)
                  ·
                    refine ⟨22100226539456601569062501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 471471499508407500140000021 22100226539456601569062501)
                    ·
                      refine ⟨4143792476148112794199219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22100226539456601569062501 4143792476148112794199219)
                      ·
                        rfl

theorem cell23_8070007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_8070007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070007 prefixEnd_8070007 := by exact prefixLift 8070007
  have htrace : WordTrace (prefixWord ++ tailWord_8070007) baseStart_8070007 baseEnd_8070007 := by
    simpa [prefixWord, tailWord_8070007, baseEnd_8070007] using wordTrace_append hprefix tailTrace_8070007
  have hstable : (prefixWord ++ tailWord_8070007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070007).length < 2 ^ (prefixWord ++ tailWord_8070007).sum := by decide
  have hdescent : baseEnd_8070007 < baseStart_8070007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070021 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_8070021 : Nat := 118140960795 + 8070021 * 2 ^ 59
def prefixEnd_8070021 : Nat := 4983230072969 + 3 ^ 40 * 8070021 * 2
def baseEnd_8070021 : Nat := 1381266554959091913141385

theorem tailTrace_8070021 : CollatzResearch.WordTrace tailWord_8070021 prefixEnd_8070021 1381266554959091913141385 := by
  unfold tailWord_8070021
  simp only [CollatzResearch.WordTrace]
  refine ⟨294337846696699641703833917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196225231131133094469222611 294337846696699641703833917)
  ·
    refine ⟨110376692511262365638937719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294337846696699641703833917 110376692511262365638937719)
    ·
      refine ⟨165565038766893548458406579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110376692511262365638937719 165565038766893548458406579)
      ·
        refine ⟨248347558150340322687609869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165565038766893548458406579 248347558150340322687609869)
        ·
          refine ⟨93130334306377621007853701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248347558150340322687609869 93130334306377621007853701)
          ·
            refine ⟨17461937682445803938972569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93130334306377621007853701 17461937682445803938972569)
            ·
              refine ⟨13096453261834352954229427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17461937682445803938972569 13096453261834352954229427)
              ·
                refine ⟨19644679892751529431344141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13096453261834352954229427 19644679892751529431344141)
                ·
                  refine ⟨7366754959781823536754053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19644679892751529431344141 7366754959781823536754053)
                  ·
                    refine ⟨1381266554959091913141385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7366754959781823536754053 1381266554959091913141385)
                    ·
                      rfl

theorem cell23_8070021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_8070021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070021 prefixEnd_8070021 := by exact prefixLift 8070021
  have htrace : WordTrace (prefixWord ++ tailWord_8070021) baseStart_8070021 baseEnd_8070021 := by
    simpa [prefixWord, tailWord_8070021, baseEnd_8070021] using wordTrace_append hprefix tailTrace_8070021
  have hstable : (prefixWord ++ tailWord_8070021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070021).length < 2 ^ (prefixWord ++ tailWord_8070021).sum := by decide
  have hdescent : baseEnd_8070021 < baseStart_8070021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070071 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 4, 3, 2]
def baseStart_8070071 : Nat := 118140960795 + 8070071 * 2 ^ 59
def prefixEnd_8070071 : Nat := 4983230072969 + 3 ^ 40 * 8070071 * 2
def baseEnd_8070071 : Nat := 4143825338910000543798925

theorem tailTrace_8070071 : CollatzResearch.WordTrace tailWord_8070071 prefixEnd_8070071 4143825338910000543798925 := by
  unfold tailWord_8070071
  simp only [CollatzResearch.WordTrace]
  refine ⟨294339670346518500243154067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196226446897679000162102711 294339670346518500243154067)
  ·
    refine ⟨441509505519777750364731101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294339670346518500243154067 441509505519777750364731101)
    ·
      refine ⟨165566064569916656386774163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441509505519777750364731101 165566064569916656386774163)
      ·
        refine ⟨248349096854874984580161245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165566064569916656386774163 248349096854874984580161245)
        ·
          refine ⟨93130911320578119217560467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248349096854874984580161245 93130911320578119217560467)
          ·
            refine ⟨139696366980867178826340701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93130911320578119217560467 139696366980867178826340701)
            ·
              refine ⟨52386137617825192059877763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139696366980867178826340701 52386137617825192059877763)
              ·
                refine ⟨78579206426737788089816645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52386137617825192059877763 78579206426737788089816645)
                ·
                  refine ⟨14733601205013335266840621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78579206426737788089816645 14733601205013335266840621)
                  ·
                    refine ⟨5525100451880000725065233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14733601205013335266840621 5525100451880000725065233)
                    ·
                      refine ⟨4143825338910000543798925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525100451880000725065233 4143825338910000543798925)
                      ·
                        rfl

theorem cell23_8070071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_8070071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070071 prefixEnd_8070071 := by exact prefixLift 8070071
  have htrace : WordTrace (prefixWord ++ tailWord_8070071) baseStart_8070071 baseEnd_8070071 := by
    simpa [prefixWord, tailWord_8070071, baseEnd_8070071] using wordTrace_append hprefix tailTrace_8070071
  have hstable : (prefixWord ++ tailWord_8070071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070071).length < 2 ^ (prefixWord ++ tailWord_8070071).sum := by decide
  have hdescent : baseEnd_8070071 < baseStart_8070071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070098 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_8070098 : Nat := 118140960795 + 8070098 * 2 ^ 59
def prefixEnd_8070098 : Nat := 4983230072969 + 3 ^ 40 * 8070098 * 2
def baseEnd_8070098 : Nat := 1381279734295890646053767

theorem tailTrace_8070098 : CollatzResearch.WordTrace tailWord_8070098 prefixEnd_8070098 1381279734295890646053767 := by
  unfold tailWord_8070098
  simp only [CollatzResearch.WordTrace]
  refine ⟨73585163779355170963596737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196227103411613789236257965 73585163779355170963596737)
  ·
    refine ⟨55188872834516378222697553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73585163779355170963596737 55188872834516378222697553)
    ·
      refine ⟨41391654625887283667023165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55188872834516378222697553 41391654625887283667023165)
      ·
        refine ⟨15521870484707731375133687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41391654625887283667023165 15521870484707731375133687)
        ·
          refine ⟨23282805727061597062700531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15521870484707731375133687 23282805727061597062700531)
          ·
            refine ⟨34924208590592395594050797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23282805727061597062700531 34924208590592395594050797)
            ·
              refine ⟨13096578221472148347769049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34924208590592395594050797 13096578221472148347769049)
              ·
                refine ⟨9822433666104111260826787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13096578221472148347769049 9822433666104111260826787)
                ·
                  refine ⟨14733650499156166891240181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9822433666104111260826787 14733650499156166891240181)
                  ·
                    refine ⟨1381279734295890646053767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14733650499156166891240181 1381279734295890646053767)
                    ·
                      rfl

theorem cell23_8070098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_8070098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070098 prefixEnd_8070098 := by exact prefixLift 8070098
  have htrace : WordTrace (prefixWord ++ tailWord_8070098) baseStart_8070098 baseEnd_8070098 := by
    simpa [prefixWord, tailWord_8070098, baseEnd_8070098] using wordTrace_append hprefix tailTrace_8070098
  have hstable : (prefixWord ++ tailWord_8070098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070098).length < 2 ^ (prefixWord ++ tailWord_8070098).sum := by decide
  have hdescent : baseEnd_8070098 < baseStart_8070098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070111 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 1, 6]
def baseStart_8070111 : Nat := 118140960795 + 8070111 * 2 ^ 59
def prefixEnd_8070111 : Nat := 4983230072969 + 3 ^ 40 * 8070111 * 2
def baseEnd_8070111 : Nat := 1381281959378726795766247

theorem tailTrace_8070111 : CollatzResearch.WordTrace tailWord_8070111 prefixEnd_8070111 1381281959378726795766247 := by
  unfold tailWord_8070111
  simp only [CollatzResearch.WordTrace]
  refine ⟨294341129266373587074610187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196227419510915724716406791 294341129266373587074610187)
  ·
    refine ⟨441511693899560380611915281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294341129266373587074610187 441511693899560380611915281)
    ·
      refine ⟨331133770424670285458936461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441511693899560380611915281 331133770424670285458936461)
      ·
        refine ⟨124175163909251357047101173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331133770424670285458936461 124175163909251357047101173)
        ·
          refine ⟨11641421616492314723165735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124175163909251357047101173 11641421616492314723165735)
          ·
            refine ⟨17462132424738472084748603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11641421616492314723165735 17462132424738472084748603)
            ·
              refine ⟨26193198637107708127122905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17462132424738472084748603 26193198637107708127122905)
              ·
                refine ⟨19644898977830781095342179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26193198637107708127122905 19644898977830781095342179)
                ·
                  refine ⟨29467348466746171643013269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19644898977830781095342179 29467348466746171643013269)
                  ·
                    refine ⟨1381281959378726795766247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29467348466746171643013269 1381281959378726795766247)
                    ·
                      rfl

theorem cell23_8070111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_8070111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070111 prefixEnd_8070111 := by exact prefixLift 8070111
  have htrace : WordTrace (prefixWord ++ tailWord_8070111) baseStart_8070111 baseEnd_8070111 := by
    simpa [prefixWord, tailWord_8070111, baseEnd_8070111] using wordTrace_append hprefix tailTrace_8070111
  have hstable : (prefixWord ++ tailWord_8070111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070111).length < 2 ^ (prefixWord ++ tailWord_8070111).sum := by decide
  have hdescent : baseEnd_8070111 < baseStart_8070111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070172 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_8070172 : Nat := 118140960795 + 8070172 * 2 ^ 59
def prefixEnd_8070172 : Nat := 4983230072969 + 3 ^ 40 * 8070172 * 2
def baseEnd_8070172 : Nat := 4143877200456104648635961

theorem tailTrace_8070172 : CollatzResearch.WordTrace tailWord_8070172 prefixEnd_8070172 4143877200456104648635961 := by
  unfold tailWord_8070172
  simp only [CollatzResearch.WordTrace]
  refine ⟨147171677059576297246290385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196228902746101729661720513 147171677059576297246290385)
  ·
    refine ⟨110378757794682222934717789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147171677059576297246290385 110378757794682222934717789)
    ·
      refine ⟨41392034173005833600519171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110378757794682222934717789 41392034173005833600519171)
      ·
        refine ⟨62088051259508750400778757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41392034173005833600519171 62088051259508750400778757)
        ·
          refine ⟨11641509611157890700146017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62088051259508750400778757 11641509611157890700146017)
          ·
            refine ⟨8731132208368418025109513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11641509611157890700146017 8731132208368418025109513)
            ·
              refine ⟨6548349156276313518832135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8731132208368418025109513 6548349156276313518832135)
              ·
                refine ⟨9822523734414470278248203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548349156276313518832135 9822523734414470278248203)
                ·
                  refine ⟨14733785601621705417372305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9822523734414470278248203 14733785601621705417372305)
                  ·
                    refine ⟨11050339201216279063029229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14733785601621705417372305 11050339201216279063029229)
                    ·
                      refine ⟨4143877200456104648635961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11050339201216279063029229 4143877200456104648635961)
                      ·
                        rfl

theorem cell23_8070172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_8070172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070172 prefixEnd_8070172 := by exact prefixLift 8070172
  have htrace : WordTrace (prefixWord ++ tailWord_8070172) baseStart_8070172 baseEnd_8070172 := by
    simpa [prefixWord, tailWord_8070172, baseEnd_8070172] using wordTrace_append hprefix tailTrace_8070172
  have hstable : (prefixWord ++ tailWord_8070172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070172).length < 2 ^ (prefixWord ++ tailWord_8070172).sum := by decide
  have hdescent : baseEnd_8070172 < baseStart_8070172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070201 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_8070201 : Nat := 118140960795 + 8070201 * 2 ^ 59
def prefixEnd_8070201 : Nat := 4983230072969 + 3 ^ 40 * 8070201 * 2
def baseEnd_8070201 : Nat := 1381297363798361678391109

theorem tailTrace_8070201 : CollatzResearch.WordTrace tailWord_8070201 prefixEnd_8070201 1381297363798361678391109 := by
  unfold tailWord_8070201
  simp only [CollatzResearch.WordTrace]
  refine ⟨294344411836047532445386457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196229607890698354963590971 294344411836047532445386457)
  ·
    refine ⟨220758308877035649334039843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294344411836047532445386457 220758308877035649334039843)
    ·
      refine ⟨331137463315553474001059765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220758308877035649334039843 331137463315553474001059765)
      ·
        refine ⟨31044137185833138187599353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331137463315553474001059765 31044137185833138187599353)
        ·
          refine ⟨23283102889374853640699515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31044137185833138187599353 23283102889374853640699515)
          ·
            refine ⟨34924654334062280461049273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283102889374853640699515 34924654334062280461049273)
            ·
              refine ⟨26193490750546710345786955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34924654334062280461049273 26193490750546710345786955)
              ·
                refine ⟨39290236125820065518680433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26193490750546710345786955 39290236125820065518680433)
                ·
                  refine ⟨29467677094365049139010325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39290236125820065518680433 29467677094365049139010325)
                  ·
                    refine ⟨1381297363798361678391109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29467677094365049139010325 1381297363798361678391109)
                    ·
                      rfl

theorem cell23_8070201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_8070201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070201 prefixEnd_8070201 := by exact prefixLift 8070201
  have htrace : WordTrace (prefixWord ++ tailWord_8070201) baseStart_8070201 baseEnd_8070201 := by
    simpa [prefixWord, tailWord_8070201, baseEnd_8070201] using wordTrace_append hprefix tailTrace_8070201
  have hstable : (prefixWord ++ tailWord_8070201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070201).length < 2 ^ (prefixWord ++ tailWord_8070201).sum := by decide
  have hdescent : baseEnd_8070201 < baseStart_8070201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070241 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_8070241 : Nat := 118140960795 + 8070241 * 2 ^ 59
def prefixEnd_8070241 : Nat := 4983230072969 + 3 ^ 40 * 8070241 * 2
def baseEnd_8070241 : Nat := 4143912630621264878673143

theorem tailTrace_8070241 : CollatzResearch.WordTrace tailWord_8070241 prefixEnd_8070241 4143912630621264878673143 := by
  unfold tailWord_8070241
  simp only [CollatzResearch.WordTrace]
  refine ⟨294345870755902619276842577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196230580503935079517895051 294345870755902619276842577)
  ·
    refine ⟨220759403066926964457631933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294345870755902619276842577 220759403066926964457631933)
    ·
      refine ⟨82784776150097611671611975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220759403066926964457631933 82784776150097611671611975)
      ·
        refine ⟨124177164225146417507417963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82784776150097611671611975 124177164225146417507417963)
        ·
          refine ⟨186265746337719626261126945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124177164225146417507417963 186265746337719626261126945)
          ·
            refine ⟨139699309753289719695845209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186265746337719626261126945 139699309753289719695845209)
            ·
              refine ⟨104774482314967289771883907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139699309753289719695845209 104774482314967289771883907)
              ·
                refine ⟨157161723472450934657825861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104774482314967289771883907 157161723472450934657825861)
                ·
                  refine ⟨29467823151084550248342349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157161723472450934657825861 29467823151084550248342349)
                  ·
                    refine ⟨11050433681656706343128381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29467823151084550248342349 11050433681656706343128381)
                    ·
                      refine ⟨4143912630621264878673143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11050433681656706343128381 4143912630621264878673143)
                      ·
                        rfl

theorem cell23_8070241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_8070241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070241 prefixEnd_8070241 := by exact prefixLift 8070241
  have htrace : WordTrace (prefixWord ++ tailWord_8070241) baseStart_8070241 baseEnd_8070241 := by
    simpa [prefixWord, tailWord_8070241, baseEnd_8070241] using wordTrace_append hprefix tailTrace_8070241
  have hstable : (prefixWord ++ tailWord_8070241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070241).length < 2 ^ (prefixWord ++ tailWord_8070241).sum := by decide
  have hdescent : baseEnd_8070241 < baseStart_8070241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070242 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8070242 : Nat := 118140960795 + 8070242 * 2 ^ 59
def prefixEnd_8070242 : Nat := 4983230072969 + 3 ^ 40 * 8070242 * 2
def baseEnd_8070242 : Nat := 4143913144101919374760639

theorem tailTrace_8070242 : CollatzResearch.WordTrace tailWord_8070242 prefixEnd_8070242 4143913144101919374760639 := by
  unfold tailWord_8070242
  simp only [CollatzResearch.WordTrace]
  refine ⟨73586476807224749111907245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196230604819265997631752653 73586476807224749111907245)
  ·
    refine ⟨27594928802709280916965217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73586476807224749111907245 27594928802709280916965217)
    ·
      refine ⟨20696196602031960687723913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27594928802709280916965217 20696196602031960687723913)
      ·
        refine ⟨15522147451523970515792935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20696196602031960687723913 15522147451523970515792935)
        ·
          refine ⟨23283221177285955773689403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522147451523970515792935 23283221177285955773689403)
          ·
            refine ⟨34924831765928933660534105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283221177285955773689403 34924831765928933660534105)
            ·
              refine ⟨26193623824446700245400579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34924831765928933660534105 26193623824446700245400579)
              ·
                refine ⟨39290435736670050368100869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26193623824446700245400579 39290435736670050368100869)
                ·
                  refine ⟨7366956700625634444018913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39290435736670050368100869 7366956700625634444018913)
                  ·
                    refine ⟨5525217525469225833014185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7366956700625634444018913 5525217525469225833014185)
                    ·
                      refine ⟨4143913144101919374760639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525217525469225833014185 4143913144101919374760639)
                      ·
                        rfl

theorem cell23_8070242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8070242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070242 prefixEnd_8070242 := by exact prefixLift 8070242
  have htrace : WordTrace (prefixWord ++ tailWord_8070242) baseStart_8070242 baseEnd_8070242 := by
    simpa [prefixWord, tailWord_8070242, baseEnd_8070242] using wordTrace_append hprefix tailTrace_8070242
  have hstable : (prefixWord ++ tailWord_8070242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070242).length < 2 ^ (prefixWord ++ tailWord_8070242).sum := by decide
  have hdescent : baseEnd_8070242 < baseStart_8070242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070301 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_8070301 : Nat := 118140960795 + 8070301 * 2 ^ 59
def prefixEnd_8070301 : Nat := 4983230072969 + 3 ^ 40 * 8070301 * 2
def baseEnd_8070301 : Nat := 4143943439460534643922867

theorem tailTrace_8070301 : CollatzResearch.WordTrace tailWord_8070301 prefixEnd_8070301 4143943439460534643922867 := by
  unfold tailWord_8070301
  simp only [CollatzResearch.WordTrace]
  refine ⟨294348059135685249524026757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196232039423790166349351171 294348059135685249524026757)
  ·
    refine ⟨55190261087940984285755017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294348059135685249524026757 55190261087940984285755017)
    ·
      refine ⟨41392695815955738214316263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55190261087940984285755017 41392695815955738214316263)
      ·
        refine ⟨62089043723933607321474395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41392695815955738214316263 62089043723933607321474395)
        ·
          refine ⟨93133565585900410982211593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62089043723933607321474395 93133565585900410982211593)
          ·
            refine ⟨69850174189425308236658695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93133565585900410982211593 69850174189425308236658695)
            ·
              refine ⟨104775261284137962354988043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69850174189425308236658695 104775261284137962354988043)
              ·
                refine ⟨157162891926206943532482065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104775261284137962354988043 157162891926206943532482065)
                ·
                  refine ⟨117872168944655207649361549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157162891926206943532482065 117872168944655207649361549)
                  ·
                    refine ⟨44202063354245702868510581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117872168944655207649361549 44202063354245702868510581)
                    ·
                      refine ⟨4143943439460534643922867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44202063354245702868510581 4143943439460534643922867)
                      ·
                        rfl

theorem cell23_8070301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_8070301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070301 prefixEnd_8070301 := by exact prefixLift 8070301
  have htrace : WordTrace (prefixWord ++ tailWord_8070301) baseStart_8070301 baseEnd_8070301 := by
    simpa [prefixWord, tailWord_8070301, baseEnd_8070301] using wordTrace_append hprefix tailTrace_8070301
  have hstable : (prefixWord ++ tailWord_8070301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070301).length < 2 ^ (prefixWord ++ tailWord_8070301).sum := by decide
  have hdescent : baseEnd_8070301 < baseStart_8070301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070331 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 3]
def baseStart_8070331 : Nat := 118140960795 + 8070331 * 2 ^ 59
def prefixEnd_8070331 : Nat := 4983230072969 + 3 ^ 40 * 8070331 * 2
def baseEnd_8070331 : Nat := 4143958843880169526547729

theorem tailTrace_8070331 : CollatzResearch.WordTrace tailWord_8070331 prefixEnd_8070331 4143958843880169526547729 := by
  unfold tailWord_8070331
  simp only [CollatzResearch.WordTrace]
  refine ⟨294349153325576564647618847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196232768883717709765079231 294349153325576564647618847)
  ·
    refine ⟨441523729988364846971428271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294349153325576564647618847 441523729988364846971428271)
    ·
      refine ⟨662285594982547270457142407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441523729988364846971428271 662285594982547270457142407)
      ·
        refine ⟨993428392473820905685713611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662285594982547270457142407 993428392473820905685713611)
        ·
          refine ⟨1490142588710731358528570417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993428392473820905685713611 1490142588710731358528570417)
          ·
            refine ⟨1117606941533048518896427813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1490142588710731358528570417 1117606941533048518896427813)
            ·
              refine ⟨209551301537446597293080215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1117606941533048518896427813 209551301537446597293080215)
              ·
                refine ⟨314326952306169895939620323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209551301537446597293080215 314326952306169895939620323)
                ·
                  refine ⟨471490428459254843909430485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314326952306169895939620323 471490428459254843909430485)
                  ·
                    refine ⟨11050556917013785404127277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 471490428459254843909430485 11050556917013785404127277)
                    ·
                      refine ⟨4143958843880169526547729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11050556917013785404127277 4143958843880169526547729)
                      ·
                        rfl

theorem cell23_8070331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 3].length) (baseStart_8070331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070331 prefixEnd_8070331 := by exact prefixLift 8070331
  have htrace : WordTrace (prefixWord ++ tailWord_8070331) baseStart_8070331 baseEnd_8070331 := by
    simpa [prefixWord, tailWord_8070331, baseEnd_8070331] using wordTrace_append hprefix tailTrace_8070331
  have hstable : (prefixWord ++ tailWord_8070331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070331).length < 2 ^ (prefixWord ++ tailWord_8070331).sum := by decide
  have hdescent : baseEnd_8070331 < baseStart_8070331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070351 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 5, 5]
def baseStart_8070351 : Nat := 118140960795 + 8070351 * 2 ^ 59
def prefixEnd_8070351 : Nat := 4983230072969 + 3 ^ 40 * 8070351 * 2
def baseEnd_8070351 : Nat := 1381323037831086482765879

theorem tailTrace_8070351 : CollatzResearch.WordTrace tailWord_8070351 prefixEnd_8070351 1381323037831086482765879 := by
  unfold tailWord_8070351
  simp only [CollatzResearch.WordTrace]
  refine ⟨294349882785504108063346907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196233255190336072042231271 294349882785504108063346907)
  ·
    refine ⟨441524824178256162095020361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294349882785504108063346907 441524824178256162095020361)
    ·
      refine ⟨331143618133692121571265271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441524824178256162095020361 331143618133692121571265271)
      ·
        refine ⟨496715427200538182356897907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331143618133692121571265271 496715427200538182356897907)
        ·
          refine ⟨745073140800807273535346861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496715427200538182356897907 745073140800807273535346861)
          ·
            refine ⟨279402427800302727575755073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745073140800807273535346861 279402427800302727575755073)
            ·
              refine ⟨209551820850227045681816305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279402427800302727575755073 209551820850227045681816305)
              ·
                refine ⟨157163865637670284261362229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209551820850227045681816305 157163865637670284261362229)
                ·
                  refine ⟨14734112403531589149502709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157163865637670284261362229 14734112403531589149502709)
                  ·
                    refine ⟨1381323037831086482765879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14734112403531589149502709 1381323037831086482765879)
                    ·
                      rfl

theorem cell23_8070351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_8070351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070351 prefixEnd_8070351 := by exact prefixLift 8070351
  have htrace : WordTrace (prefixWord ++ tailWord_8070351) baseStart_8070351 baseEnd_8070351 := by
    simpa [prefixWord, tailWord_8070351, baseEnd_8070351] using wordTrace_append hprefix tailTrace_8070351
  have hstable : (prefixWord ++ tailWord_8070351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070351).length < 2 ^ (prefixWord ++ tailWord_8070351).sum := by decide
  have hdescent : baseEnd_8070351 < baseStart_8070351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070399 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 1, 1, 3]
def baseStart_8070399 : Nat := 118140960795 + 8070399 * 2 ^ 59
def prefixEnd_8070399 : Nat := 4983230072969 + 3 ^ 40 * 8070399 * 2
def baseEnd_8070399 : Nat := 4143993760564675260497417

theorem tailTrace_8070399 : CollatzResearch.WordTrace tailWord_8070399 prefixEnd_8070399 4143993760564675260497417 := by
  unfold tailWord_8070399
  simp only [CollatzResearch.WordTrace]
  refine ⟨294351633489330212261094251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196234422326220141507396167 294351633489330212261094251)
  ·
    refine ⟨441527450233995318391641377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294351633489330212261094251 441527450233995318391641377)
    ·
      refine ⟨331145587675496488793731033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441527450233995318391641377 331145587675496488793731033)
      ·
        refine ⟨248359190756622366595298275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331145587675496488793731033 248359190756622366595298275)
        ·
          refine ⟨372538786134933549892947413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248359190756622366595298275 372538786134933549892947413)
          ·
            refine ⟨8731377800037505075615955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 372538786134933549892947413 8731377800037505075615955)
            ·
              refine ⟨13097066700056257613423933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731377800037505075615955 13097066700056257613423933)
              ·
                refine ⟨4911400012521096605033975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13097066700056257613423933 4911400012521096605033975)
                ·
                  refine ⟨7367100018781644907550963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911400012521096605033975 7367100018781644907550963)
                  ·
                    refine ⟨11050650028172467361326445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367100018781644907550963 11050650028172467361326445)
                    ·
                      refine ⟨4143993760564675260497417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11050650028172467361326445 4143993760564675260497417)
                      ·
                        rfl

theorem cell23_8070399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_8070399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070399 prefixEnd_8070399 := by exact prefixLift 8070399
  have htrace : WordTrace (prefixWord ++ tailWord_8070399) baseStart_8070399 baseEnd_8070399 := by
    simpa [prefixWord, tailWord_8070399, baseEnd_8070399] using wordTrace_append hprefix tailTrace_8070399
  have hstable : (prefixWord ++ tailWord_8070399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070399).length < 2 ^ (prefixWord ++ tailWord_8070399).sum := by decide
  have hdescent : baseEnd_8070399 < baseStart_8070399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070411 : List Nat := [1, 1, 1, 1, 5, 3, 11]
def baseStart_8070411 : Nat := 118140960795 + 8070411 * 2 ^ 59
def prefixEnd_8070411 : Nat := 4983230072969 + 3 ^ 40 * 8070411 * 2
def baseEnd_8070411 : Nat := 51160492868302829796881

theorem tailTrace_8070411 : CollatzResearch.WordTrace tailWord_8070411 prefixEnd_8070411 51160492868302829796881 := by
  unfold tailWord_8070411
  simp only [CollatzResearch.WordTrace]
  refine ⟨294352071165286738310531087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196234714110191158873687391 294352071165286738310531087)
  ·
    refine ⟨441528106747930107465796631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294352071165286738310531087 441528106747930107465796631)
    ·
      refine ⟨662292160121895161198694947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441528106747930107465796631 662292160121895161198694947)
      ·
        refine ⟨993438240182842741798042421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662292160121895161198694947 993438240182842741798042421)
        ·
          refine ⟨93134835017141507043566477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 993438240182842741798042421 93134835017141507043566477)
          ·
            refine ⟨34925563131428065141337429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93134835017141507043566477 34925563131428065141337429)
            ·
              refine ⟨51160492868302829796881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34925563131428065141337429 51160492868302829796881)
              ·
                rfl

theorem cell23_8070411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 11].length) (baseStart_8070411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070411 prefixEnd_8070411 := by exact prefixLift 8070411
  have htrace : WordTrace (prefixWord ++ tailWord_8070411) baseStart_8070411 baseEnd_8070411 := by
    simpa [prefixWord, tailWord_8070411, baseEnd_8070411] using wordTrace_append hprefix tailTrace_8070411
  have hstable : (prefixWord ++ tailWord_8070411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070411).length < 2 ^ (prefixWord ++ tailWord_8070411).sum := by decide
  have hdescent : baseEnd_8070411 < baseStart_8070411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070432 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 2, 4]
def baseStart_8070432 : Nat := 118140960795 + 8070432 * 2 ^ 59
def prefixEnd_8070432 : Nat := 4983230072969 + 3 ^ 40 * 8070432 * 2
def baseEnd_8070432 : Nat := 1381336901808757877128255

theorem tailTrace_8070432 : CollatzResearch.WordTrace tailWord_8070432 prefixEnd_8070432 1381336901808757877128255 := by
  unfold tailWord_8070432
  simp only [CollatzResearch.WordTrace]
  refine ⟨147176418549105329448522775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196235224732140439264697033 147176418549105329448522775)
  ·
    refine ⟨220764627823657994172784163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147176418549105329448522775 220764627823657994172784163)
    ·
      refine ⟨331146941735486991259176245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220764627823657994172784163 331146941735486991259176245)
      ·
        refine ⟨31045025787701905430547773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331146941735486991259176245 31045025787701905430547773)
        ·
          refine ⟨11641884670388214536455415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31045025787701905430547773 11641884670388214536455415)
          ·
            refine ⟨17462827005582321804683123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11641884670388214536455415 17462827005582321804683123)
            ·
              refine ⟨26194240508373482707024685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17462827005582321804683123 26194240508373482707024685)
              ·
                refine ⟨9822840190640056015134257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26194240508373482707024685 9822840190640056015134257)
                ·
                  refine ⟨7367130142980042011350693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9822840190640056015134257 7367130142980042011350693)
                  ·
                    refine ⟨1381336901808757877128255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367130142980042011350693 1381336901808757877128255)
                    ·
                      rfl

theorem cell23_8070432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_8070432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070432 prefixEnd_8070432 := by exact prefixLift 8070432
  have htrace : WordTrace (prefixWord ++ tailWord_8070432) baseStart_8070432 baseEnd_8070432 := by
    simpa [prefixWord, tailWord_8070432, baseEnd_8070432] using wordTrace_append hprefix tailTrace_8070432
  have hstable : (prefixWord ++ tailWord_8070432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070432).length < 2 ^ (prefixWord ++ tailWord_8070432).sum := by decide
  have hdescent : baseEnd_8070432 < baseStart_8070432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070442 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_8070442 : Nat := 118140960795 + 8070442 * 2 ^ 59
def prefixEnd_8070442 : Nat := 4983230072969 + 3 ^ 40 * 8070442 * 2
def baseEnd_8070442 : Nat := 4144015840232818592259719

theorem tailTrace_8070442 : CollatzResearch.WordTrace tailWord_8070442 prefixEnd_8070442 4144015840232818592259719 := by
  unfold tailWord_8070442
  simp only [CollatzResearch.WordTrace]
  refine ⟨73588300457043607651227395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196235467885449620403273053 73588300457043607651227395)
  ·
    refine ⟨110382450685565411476841093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73588300457043607651227395 110382450685565411476841093)
    ·
      refine ⟨20696709503543514651907705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110382450685565411476841093 20696709503543514651907705)
      ·
        refine ⟨15522532127657635988930779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20696709503543514651907705 15522532127657635988930779)
        ·
          refine ⟨23283798191486453983396169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522532127657635988930779 23283798191486453983396169)
          ·
            refine ⟨17462848643614840487547127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23283798191486453983396169 17462848643614840487547127)
            ·
              refine ⟨26194272965422260731320691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17462848643614840487547127 26194272965422260731320691)
              ·
                refine ⟨39291409448133391096981037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26194272965422260731320691 39291409448133391096981037)
                ·
                  refine ⟨14734278543050021661367889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39291409448133391096981037 14734278543050021661367889)
                  ·
                    refine ⟨11050708907287516246025917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14734278543050021661367889 11050708907287516246025917)
                    ·
                      refine ⟨4144015840232818592259719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11050708907287516246025917 4144015840232818592259719)
                      ·
                        rfl

theorem cell23_8070442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_8070442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070442 prefixEnd_8070442 := by exact prefixLift 8070442
  have htrace : WordTrace (prefixWord ++ tailWord_8070442) baseStart_8070442 baseEnd_8070442 := by
    simpa [prefixWord, tailWord_8070442, baseEnd_8070442] using wordTrace_append hprefix tailTrace_8070442
  have hstable : (prefixWord ++ tailWord_8070442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070442).length < 2 ^ (prefixWord ++ tailWord_8070442).sum := by decide
  have hdescent : baseEnd_8070442 < baseStart_8070442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070445 : List Nat := [1, 5, 3, 1, 1, 1, 2, 9]
def baseStart_8070445 : Nat := 118140960795 + 8070445 * 2 ^ 59
def prefixEnd_8070445 : Nat := 4983230072969 + 3 ^ 40 * 8070445 * 2
def baseEnd_8070445 : Nat := 153482125210177114093415

theorem tailTrace_8070445 : CollatzResearch.WordTrace tailWord_8070445 prefixEnd_8070445 153482125210177114093415 := by
  unfold tailWord_8070445
  simp only [CollatzResearch.WordTrace]
  refine ⟨294353311247163562117268789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196235540831442374744845859 294353311247163562117268789)
  ·
    refine ⟨27595622929421583948493949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294353311247163562117268789 27595622929421583948493949)
    ·
      refine ⟨10348358598533093980685231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27595622929421583948493949 10348358598533093980685231)
      ·
        refine ⟨15522537897799640971027847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348358598533093980685231 15522537897799640971027847)
        ·
          refine ⟨23283806846699461456541771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522537897799640971027847 23283806846699461456541771)
          ·
            refine ⟨34925710270049192184812657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283806846699461456541771 34925710270049192184812657)
            ·
              refine ⟨26194282702536894138609493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34925710270049192184812657 26194282702536894138609493)
              ·
                refine ⟨153482125210177114093415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26194282702536894138609493 153482125210177114093415)
                ·
                  rfl

theorem cell23_8070445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 9].length) (baseStart_8070445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070445 prefixEnd_8070445 := by exact prefixLift 8070445
  have htrace : WordTrace (prefixWord ++ tailWord_8070445) baseStart_8070445 baseEnd_8070445 := by
    simpa [prefixWord, tailWord_8070445, baseEnd_8070445] using wordTrace_append hprefix tailTrace_8070445
  have hstable : (prefixWord ++ tailWord_8070445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070445).length < 2 ^ (prefixWord ++ tailWord_8070445).sum := by decide
  have hdescent : baseEnd_8070445 < baseStart_8070445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070478 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_8070478 : Nat := 118140960795 + 8070478 * 2 ^ 59
def prefixEnd_8070478 : Nat := 4983230072969 + 3 ^ 40 * 8070478 * 2
def baseEnd_8070478 : Nat := 4144034325536380451409553

theorem tailTrace_8070478 : CollatzResearch.WordTrace tailWord_8070478 prefixEnd_8070478 4144034325536380451409553 := by
  unfold tailWord_8070478
  simp only [CollatzResearch.WordTrace]
  refine ⟨36794314357005501094152511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196236343237362672502146725 36794314357005501094152511)
  ·
    refine ⟨55191471535508251641228767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36794314357005501094152511 55191471535508251641228767)
    ·
      refine ⟨82787207303262377461843151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55191471535508251641228767 82787207303262377461843151)
      ·
        refine ⟨124180810954893566192764727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82787207303262377461843151 124180810954893566192764727)
        ·
          refine ⟨186271216432340349289147091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124180810954893566192764727 186271216432340349289147091)
          ·
            refine ⟨279406824648510523933720637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186271216432340349289147091 279406824648510523933720637)
            ·
              refine ⟨104777559243191446475145239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279406824648510523933720637 104777559243191446475145239)
              ·
                refine ⟨157166338864787169712717859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104777559243191446475145239 157166338864787169712717859)
                ·
                  refine ⟨235749508297180754569076789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157166338864787169712717859 235749508297180754569076789)
                  ·
                    refine ⟨22101516402860695740850949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 235749508297180754569076789 22101516402860695740850949)
                    ·
                      refine ⟨4144034325536380451409553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22101516402860695740850949 4144034325536380451409553)
                      ·
                        rfl

theorem cell23_8070478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_8070478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070478 prefixEnd_8070478 := by exact prefixLift 8070478
  have htrace : WordTrace (prefixWord ++ tailWord_8070478) baseStart_8070478 baseEnd_8070478 := by
    simpa [prefixWord, tailWord_8070478, baseEnd_8070478] using wordTrace_append hprefix tailTrace_8070478
  have hstable : (prefixWord ++ tailWord_8070478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070478).length < 2 ^ (prefixWord ++ tailWord_8070478).sum := by decide
  have hdescent : baseEnd_8070478 < baseStart_8070478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070488 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_8070488 : Nat := 118140960795 + 8070488 * 2 ^ 59
def prefixEnd_8070488 : Nat := 4983230072969 + 3 ^ 40 * 8070488 * 2
def baseEnd_8070488 : Nat := 1381346486780975137428169

theorem tailTrace_8070488 : CollatzResearch.WordTrace tailWord_8070488 prefixEnd_8070488 1381346486780975137428169 := by
  unfold tailWord_8070488
  simp only [CollatzResearch.WordTrace]
  refine ⟨147177439793003890230542059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196236586390671853640722745 147177439793003890230542059)
  ·
    refine ⟨220766159689505835345813089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147177439793003890230542059 220766159689505835345813089)
    ·
      refine ⟨165574619767129376509359817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220766159689505835345813089 165574619767129376509359817)
      ·
        refine ⟨124180964825347032382019863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165574619767129376509359817 124180964825347032382019863)
        ·
          refine ⟨186271447238020548573029795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124180964825347032382019863 186271447238020548573029795)
          ·
            refine ⟨279407170857030822859544693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186271447238020548573029795 279407170857030822859544693)
            ·
              refine ⟨26194422267846639643082315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279407170857030822859544693 26194422267846639643082315)
              ·
                refine ⟨39291633401769959464623473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26194422267846639643082315 39291633401769959464623473)
                ·
                  refine ⟨29468725051327469598467605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39291633401769959464623473 29468725051327469598467605)
                  ·
                    refine ⟨1381346486780975137428169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29468725051327469598467605 1381346486780975137428169)
                    ·
                      rfl

theorem cell23_8070488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_8070488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070488 prefixEnd_8070488 := by exact prefixLift 8070488
  have htrace : WordTrace (prefixWord ++ tailWord_8070488) baseStart_8070488 baseEnd_8070488 := by
    simpa [prefixWord, tailWord_8070488, baseEnd_8070488] using wordTrace_append hprefix tailTrace_8070488
  have hstable : (prefixWord ++ tailWord_8070488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070488).length < 2 ^ (prefixWord ++ tailWord_8070488).sum := by decide
  have hdescent : baseEnd_8070488 < baseStart_8070488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070512 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 4, 2, 2]
def baseStart_8070512 : Nat := 118140960795 + 8070512 * 2 ^ 59
def prefixEnd_8070512 : Nat := 4983230072969 + 3 ^ 40 * 8070512 * 2
def baseEnd_8070512 : Nat := 4144051783878633318384397

theorem tailTrace_8070512 : CollatzResearch.WordTrace tailWord_8070512 prefixEnd_8070512 4144051783878633318384397 := by
  unfold tailWord_8070512
  simp only [CollatzResearch.WordTrace]
  refine ⟨147177877468960416279978895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196237169958613888373305193 147177877468960416279978895)
  ·
    refine ⟨220766816203440624419968343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147177877468960416279978895 220766816203440624419968343)
    ·
      refine ⟨331150224305160936629952515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220766816203440624419968343 331150224305160936629952515)
      ·
        refine ⟨496725336457741404944928773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331150224305160936629952515 496725336457741404944928773)
        ·
          refine ⟨93136000585826513427174145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496725336457741404944928773 93136000585826513427174145)
          ·
            refine ⟨69852000439369885070380609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93136000585826513427174145 69852000439369885070380609)
            ·
              refine ⟨52389000329527413802785457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69852000439369885070380609 52389000329527413802785457)
              ·
                refine ⟨39291750247145560352089093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52389000329527413802785457 39291750247145560352089093)
                ·
                  refine ⟨7367203171339792566016705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39291750247145560352089093 7367203171339792566016705)
                  ·
                    refine ⟨5525402378504844424512529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7367203171339792566016705 5525402378504844424512529)
                    ·
                      refine ⟨4144051783878633318384397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525402378504844424512529 4144051783878633318384397)
                      ·
                        rfl

theorem cell23_8070512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 4, 2, 2].length) (baseStart_8070512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070512 prefixEnd_8070512 := by exact prefixLift 8070512
  have htrace : WordTrace (prefixWord ++ tailWord_8070512) baseStart_8070512 baseEnd_8070512 := by
    simpa [prefixWord, tailWord_8070512, baseEnd_8070512] using wordTrace_append hprefix tailTrace_8070512
  have hstable : (prefixWord ++ tailWord_8070512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070512).length < 2 ^ (prefixWord ++ tailWord_8070512).sum := by decide
  have hdescent : baseEnd_8070512 < baseStart_8070512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070535 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 7]
def baseStart_8070535 : Nat := 118140960795 + 8070535 * 2 ^ 59
def prefixEnd_8070535 : Nat := 4983230072969 + 3 ^ 40 * 8070535 * 2
def baseEnd_8070535 : Nat := 460451510437076303155199

theorem tailTrace_8070535 : CollatzResearch.WordTrace tailWord_8070535 prefixEnd_8070535 460451510437076303155199 := by
  unfold tailWord_8070535
  simp only [CollatzResearch.WordTrace]
  refine ⟨294356593816837507488045059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196237729211225004992030039 294356593816837507488045059)
  ·
    refine ⟨441534890725256261232067589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294356593816837507488045059 441534890725256261232067589)
    ·
      refine ⟨82787792010985548981012673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441534890725256261232067589 82787792010985548981012673)
      ·
        refine ⟨62090844008239161735759505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82787792010985548981012673 62090844008239161735759505)
        ·
          refine ⟨46568133006179371301819629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62090844008239161735759505 46568133006179371301819629)
          ·
            refine ⟨17463049877317264238182361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46568133006179371301819629 17463049877317264238182361)
            ·
              refine ⟨13097287407987948178636771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17463049877317264238182361 13097287407987948178636771)
              ·
                refine ⟨19645931111981922267955157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13097287407987948178636771 19645931111981922267955157)
                ·
                  refine ⟨460451510437076303155199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19645931111981922267955157 460451510437076303155199)
                  ·
                    rfl

theorem cell23_8070535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 7].length) (baseStart_8070535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070535 prefixEnd_8070535 := by exact prefixLift 8070535
  have htrace : WordTrace (prefixWord ++ tailWord_8070535) baseStart_8070535 baseEnd_8070535 := by
    simpa [prefixWord, tailWord_8070535, baseEnd_8070535] using wordTrace_append hprefix tailTrace_8070535
  have hstable : (prefixWord ++ tailWord_8070535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070535).length < 2 ^ (prefixWord ++ tailWord_8070535).sum := by decide
  have hdescent : baseEnd_8070535 < baseStart_8070535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070642 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 6]
def baseStart_8070642 : Nat := 118140960795 + 8070642 * 2 ^ 59
def prefixEnd_8070642 : Nat := 4983230072969 + 3 ^ 40 * 8070642 * 2
def baseEnd_8070642 : Nat := 460457615151524201084311

theorem tailTrace_8070642 : CollatzResearch.WordTrace tailWord_8070642 prefixEnd_8070642 460457615151524201084311 := by
  unfold tailWord_8070642
  simp only [CollatzResearch.WordTrace]
  refine ⟨73590124106862466190547545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196240330951633243174793453 73590124106862466190547545)
  ·
    refine ⟨55192593080146849642910659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73590124106862466190547545 55192593080146849642910659)
    ·
      refine ⟨82788889620220274464365989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55192593080146849642910659 82788889620220274464365989)
      ·
        refine ⟨15522916803791301462068623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82788889620220274464365989 15522916803791301462068623)
        ·
          refine ⟨23284375205686952193102935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522916803791301462068623 23284375205686952193102935)
          ·
            refine ⟨34926562808530428289654403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23284375205686952193102935 34926562808530428289654403)
            ·
              refine ⟨52389844212795642434481605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34926562808530428289654403 52389844212795642434481605)
              ·
                refine ⟨9823095789899182956465301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52389844212795642434481605 9823095789899182956465301)
                ·
                  refine ⟨460457615151524201084311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9823095789899182956465301 460457615151524201084311)
                  ·
                    rfl

theorem cell23_8070642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_8070642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070642 prefixEnd_8070642 := by exact prefixLift 8070642
  have htrace : WordTrace (prefixWord ++ tailWord_8070642) baseStart_8070642 baseEnd_8070642 := by
    simpa [prefixWord, tailWord_8070642, baseEnd_8070642] using wordTrace_append hprefix tailTrace_8070642
  have hstable : (prefixWord ++ tailWord_8070642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070642).length < 2 ^ (prefixWord ++ tailWord_8070642).sum := by decide
  have hdescent : baseEnd_8070642 < baseStart_8070642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070646 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_8070646 : Nat := 118140960795 + 8070646 * 2 ^ 59
def prefixEnd_8070646 : Nat := 4983230072969 + 3 ^ 40 * 8070646 * 2
def baseEnd_8070646 : Nat := 1381373530095445264702927

theorem tailTrace_8070646 : CollatzResearch.WordTrace tailWord_8070646 prefixEnd_8070646 1381373530095445264702927 := by
  unfold tailWord_8070646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397540144964710840333487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196240428212956915630223861 18397540144964710840333487)
  ·
    refine ⟨27596310217447066260500231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18397540144964710840333487 27596310217447066260500231)
    ·
      refine ⟨41394465326170599390750347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27596310217447066260500231 41394465326170599390750347)
      ·
        refine ⟨62091697989255899086125521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41394465326170599390750347 62091697989255899086125521)
        ·
          refine ⟨46568773491941924314594141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62091697989255899086125521 46568773491941924314594141)
          ·
            refine ⟨17463290059478221617972803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46568773491941924314594141 17463290059478221617972803)
            ·
              refine ⟨26194935089217332426959205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17463290059478221617972803 26194935089217332426959205)
              ·
                refine ⟨4911550329228249830054851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26194935089217332426959205 4911550329228249830054851)
                ·
                  refine ⟨7367325493842374745082277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911550329228249830054851 7367325493842374745082277)
                  ·
                    refine ⟨1381373530095445264702927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367325493842374745082277 1381373530095445264702927)
                    ·
                      rfl

theorem cell23_8070646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_8070646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070646 prefixEnd_8070646 := by exact prefixLift 8070646
  have htrace : WordTrace (prefixWord ++ tailWord_8070646) baseStart_8070646 baseEnd_8070646 := by
    simpa [prefixWord, tailWord_8070646, baseEnd_8070646] using wordTrace_append hprefix tailTrace_8070646
  have hstable : (prefixWord ++ tailWord_8070646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070646).length < 2 ^ (prefixWord ++ tailWord_8070646).sum := by decide
  have hdescent : baseEnd_8070646 < baseStart_8070646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070689 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 1, 5]
def baseStart_8070689 : Nat := 118140960795 + 8070689 * 2 ^ 59
def prefixEnd_8070689 : Nat := 4983230072969 + 3 ^ 40 * 8070689 * 2
def baseEnd_8070689 : Nat := 1381380889984826375290361

theorem tailTrace_8070689 : CollatzResearch.WordTrace tailWord_8070689 prefixEnd_8070689 1381380889984826375290361 := by
  unfold tailWord_8070689
  simp only [CollatzResearch.WordTrace]
  refine ⟨294362210658279591789151121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196241473772186394526100747 294362210658279591789151121)
  ·
    refine ⟨220771657993709693841863341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294362210658279591789151121 220771657993709693841863341)
    ·
      refine ⟨82789371747641135190698753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220771657993709693841863341 82789371747641135190698753)
      ·
        refine ⟨62092028810730851393024065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82789371747641135190698753 62092028810730851393024065)
        ·
          refine ⟨46569021608048138544768049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62092028810730851393024065 46569021608048138544768049)
          ·
            refine ⟨34926766206036103908576037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46569021608048138544768049 34926766206036103908576037)
            ·
              refine ⟨6548768663631769482858007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34926766206036103908576037 6548768663631769482858007)
              ·
                refine ⟨9823152995447654224287011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548768663631769482858007 9823152995447654224287011)
                ·
                  refine ⟨14734729493171481336430517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9823152995447654224287011 14734729493171481336430517)
                  ·
                    refine ⟨1381380889984826375290361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14734729493171481336430517 1381380889984826375290361)
                    ·
                      rfl

theorem cell23_8070689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_8070689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070689 prefixEnd_8070689 := by exact prefixLift 8070689
  have htrace : WordTrace (prefixWord ++ tailWord_8070689) baseStart_8070689 baseEnd_8070689 := by
    simpa [prefixWord, tailWord_8070689, baseEnd_8070689] using wordTrace_append hprefix tailTrace_8070689
  have hstable : (prefixWord ++ tailWord_8070689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070689).length < 2 ^ (prefixWord ++ tailWord_8070689).sum := by decide
  have hdescent : baseEnd_8070689 < baseStart_8070689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070705 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_8070705 : Nat := 118140960795 + 8070705 * 2 ^ 59
def prefixEnd_8070705 : Nat := 4983230072969 + 3 ^ 40 * 8070705 * 2
def baseEnd_8070705 : Nat := 4144150885644951063271009

theorem tailTrace_8070705 : CollatzResearch.WordTrace tailWord_8070705 prefixEnd_8070705 4144150885644951063271009 := by
  unfold tailWord_8070705
  simp only [CollatzResearch.WordTrace]
  refine ⟨294362794226221626521733569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196241862817481084347822379 294362794226221626521733569)
  ·
    refine ⟨220772095669666219891300177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294362794226221626521733569 220772095669666219891300177)
    ·
      refine ⟨165579071752249664918475133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220772095669666219891300177 165579071752249664918475133)
      ·
        refine ⟨62092151907093624344428175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165579071752249664918475133 62092151907093624344428175)
        ·
          refine ⟨93138227860640436516642263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62092151907093624344428175 93138227860640436516642263)
          ·
            refine ⟨139707341790960654774963395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93138227860640436516642263 139707341790960654774963395)
            ·
              refine ⟨209561012686440982162445093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139707341790960654774963395 209561012686440982162445093)
              ·
                refine ⟨39292689878707684155458455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209561012686440982162445093 39292689878707684155458455)
                ·
                  refine ⟨58939034818061526233187683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39292689878707684155458455 58939034818061526233187683)
                  ·
                    refine ⟨88408552227092289349781525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58939034818061526233187683 88408552227092289349781525)
                    ·
                      refine ⟨4144150885644951063271009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88408552227092289349781525 4144150885644951063271009)
                      ·
                        rfl

theorem cell23_8070705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_8070705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070705 prefixEnd_8070705 := by exact prefixLift 8070705
  have htrace : WordTrace (prefixWord ++ tailWord_8070705) baseStart_8070705 baseEnd_8070705 := by
    simpa [prefixWord, tailWord_8070705, baseEnd_8070705] using wordTrace_append hprefix tailTrace_8070705
  have hstable : (prefixWord ++ tailWord_8070705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070705).length < 2 ^ (prefixWord ++ tailWord_8070705).sum := by decide
  have hdescent : baseEnd_8070705 < baseStart_8070705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070712 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_8070712 : Nat := 118140960795 + 8070712 * 2 ^ 59
def prefixEnd_8070712 : Nat := 4983230072969 + 3 ^ 40 * 8070712 * 2
def baseEnd_8070712 : Nat := 4144154480009532535883477

theorem tailTrace_8070712 : CollatzResearch.WordTrace tailWord_8070712 prefixEnd_8070712 4144154480009532535883477 := by
  unfold tailWord_8070712
  simp only [CollatzResearch.WordTrace]
  refine ⟨147181524768598133358619195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196242033024797511144825593 147181524768598133358619195)
  ·
    refine ⟨220772287152897200037928793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147181524768598133358619195 220772287152897200037928793)
    ·
      refine ⟨165579215364672900028446595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220772287152897200037928793 165579215364672900028446595)
      ·
        refine ⟨248368823047009350042669893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165579215364672900028446595 248368823047009350042669893)
        ·
          refine ⟨46569154321314253133000605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248368823047009350042669893 46569154321314253133000605)
          ·
            refine ⟨17463432870492844924875227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46569154321314253133000605 17463432870492844924875227)
            ·
              refine ⟨26195149305739267387312841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17463432870492844924875227 26195149305739267387312841)
              ·
                refine ⟨19646361979304450540484631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26195149305739267387312841 19646361979304450540484631)
                ·
                  refine ⟨29469542968956675810726947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19646361979304450540484631 29469542968956675810726947)
                  ·
                    refine ⟨44204314453435013716090421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29469542968956675810726947 44204314453435013716090421)
                    ·
                      refine ⟨4144154480009532535883477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44204314453435013716090421 4144154480009532535883477)
                      ·
                        rfl

theorem cell23_8070712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_8070712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070712 prefixEnd_8070712 := by exact prefixLift 8070712
  have htrace : WordTrace (prefixWord ++ tailWord_8070712) baseStart_8070712 baseEnd_8070712 := by
    simpa [prefixWord, tailWord_8070712, baseEnd_8070712] using wordTrace_append hprefix tailTrace_8070712
  have hstable : (prefixWord ++ tailWord_8070712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070712).length < 2 ^ (prefixWord ++ tailWord_8070712).sum := by decide
  have hdescent : baseEnd_8070712 < baseStart_8070712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070732 : List Nat := [2, 2, 1, 3, 1, 3, 4, 7]
def baseStart_8070732 : Nat := 118140960795 + 8070732 * 2 ^ 59
def prefixEnd_8070732 : Nat := 4983230072969 + 3 ^ 40 * 8070732 * 2
def baseEnd_8070732 : Nat := 153487583319356387319755

theorem tailTrace_8070732 : CollatzResearch.WordTrace tailWord_8070732 prefixEnd_8070732 153487583319356387319755 := by
  unfold tailWord_8070732
  simp only [CollatzResearch.WordTrace]
  refine ⟨147181889498561905066483225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196242519331415873421977633 147181889498561905066483225)
  ·
    refine ⟨110386417123921428799862419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147181889498561905066483225 110386417123921428799862419)
    ·
      refine ⟨165579625685882143199793629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110386417123921428799862419 165579625685882143199793629)
      ·
        refine ⟨62092359632205803699922611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165579625685882143199793629 62092359632205803699922611)
        ·
          refine ⟨93138539448308705549883917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62092359632205803699922611 93138539448308705549883917)
          ·
            refine ⟨34926952293115764581206469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93138539448308705549883917 34926952293115764581206469)
            ·
              refine ⟨6548803554959205858976213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34926952293115764581206469 6548803554959205858976213)
              ·
                refine ⟨153487583319356387319755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6548803554959205858976213 153487583319356387319755)
                ·
                  rfl

theorem cell23_8070732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 7].length) (baseStart_8070732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070732 prefixEnd_8070732 := by exact prefixLift 8070732
  have htrace : WordTrace (prefixWord ++ tailWord_8070732) baseStart_8070732 baseEnd_8070732 := by
    simpa [prefixWord, tailWord_8070732, baseEnd_8070732] using wordTrace_append hprefix tailTrace_8070732
  have hstable : (prefixWord ++ tailWord_8070732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070732).length < 2 ^ (prefixWord ++ tailWord_8070732).sum := by decide
  have hdescent : baseEnd_8070732 < baseStart_8070732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070743 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 1, 2, 2]
def baseStart_8070743 : Nat := 118140960795 + 8070743 * 2 ^ 59
def prefixEnd_8070743 : Nat := 4983230072969 + 3 ^ 40 * 8070743 * 2
def baseEnd_8070743 : Nat := 4144170397909821914595835

theorem tailTrace_8070743 : CollatzResearch.WordTrace tailWord_8070743 prefixEnd_8070743 4144170397909821914595835 := by
  unfold tailWord_8070743
  simp only [CollatzResearch.WordTrace]
  refine ⟨294364180200083959011616883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196242786800055972674411255 294364180200083959011616883)
  ·
    refine ⟨441546270300125938517425325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294364180200083959011616883 441546270300125938517425325)
    ·
      refine ⟨165579851362547226944034497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441546270300125938517425325 165579851362547226944034497)
      ·
        refine ⟨124184888521910420208025873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165579851362547226944034497 124184888521910420208025873)
        ·
          refine ⟨93138666391432815156019405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124184888521910420208025873 93138666391432815156019405)
          ·
            refine ⟨34926999896787305683507277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93138666391432815156019405 34926999896787305683507277)
            ·
              refine ⟨13097624961295239631315229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34926999896787305683507277 13097624961295239631315229)
              ·
                refine ⟨4911609360485714861743211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13097624961295239631315229 4911609360485714861743211)
                ·
                  refine ⟨7367414040728572292614817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911609360485714861743211 7367414040728572292614817)
                  ·
                    refine ⟨5525560530546429219461113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7367414040728572292614817 5525560530546429219461113)
                    ·
                      refine ⟨4144170397909821914595835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525560530546429219461113 4144170397909821914595835)
                      ·
                        rfl

theorem cell23_8070743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_8070743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070743 prefixEnd_8070743 := by exact prefixLift 8070743
  have htrace : WordTrace (prefixWord ++ tailWord_8070743) baseStart_8070743 baseEnd_8070743 := by
    simpa [prefixWord, tailWord_8070743, baseEnd_8070743] using wordTrace_append hprefix tailTrace_8070743
  have hstable : (prefixWord ++ tailWord_8070743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070743).length < 2 ^ (prefixWord ++ tailWord_8070743).sum := by decide
  have hdescent : baseEnd_8070743 < baseStart_8070743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070759 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_8070759 : Nat := 118140960795 + 8070759 * 2 ^ 59
def prefixEnd_8070759 : Nat := 4983230072969 + 3 ^ 40 * 8070759 * 2
def baseEnd_8070759 : Nat := 4144178613600293851995761

theorem tailTrace_8070759 : CollatzResearch.WordTrace tailWord_8070759 prefixEnd_8070759 4144178613600293851995761 := by
  unfold tailWord_8070759
  simp only [CollatzResearch.WordTrace]
  refine ⟨294364763768025993744199331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196243175845350662496132887 294364763768025993744199331)
  ·
    refine ⟨441547145652038990616298997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294364763768025993744199331 441547145652038990616298997)
    ·
      refine ⟨41395044904878655370278031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441547145652038990616298997 41395044904878655370278031)
      ·
        refine ⟨62092567357317983055417047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41395044904878655370278031 62092567357317983055417047)
        ·
          refine ⟨93138851035976974583125571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62092567357317983055417047 93138851035976974583125571)
          ·
            refine ⟨139708276553965461874688357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93138851035976974583125571 139708276553965461874688357)
            ·
              refine ⟨26195301853868524101504067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139708276553965461874688357 26195301853868524101504067)
              ·
                refine ⟨39292952780802786152256101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26195301853868524101504067 39292952780802786152256101)
                ·
                  refine ⟨7367428646400522403548019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39292952780802786152256101 7367428646400522403548019)
                  ·
                    refine ⟨11051142969600783605322029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367428646400522403548019 11051142969600783605322029)
                    ·
                      refine ⟨4144178613600293851995761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11051142969600783605322029 4144178613600293851995761)
                      ·
                        rfl

theorem cell23_8070759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_8070759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070759 prefixEnd_8070759 := by exact prefixLift 8070759
  have htrace : WordTrace (prefixWord ++ tailWord_8070759) baseStart_8070759 baseEnd_8070759 := by
    simpa [prefixWord, tailWord_8070759, baseEnd_8070759] using wordTrace_append hprefix tailTrace_8070759
  have hstable : (prefixWord ++ tailWord_8070759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070759).length < 2 ^ (prefixWord ++ tailWord_8070759).sum := by decide
  have hdescent : baseEnd_8070759 < baseStart_8070759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070775 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 8]
def baseStart_8070775 : Nat := 118140960795 + 8070775 * 2 ^ 59
def prefixEnd_8070775 : Nat := 4983230072969 + 3 ^ 40 * 8070775 * 2
def baseEnd_8070775 : Nat := 1381395609763588596465229

theorem tailTrace_8070775 : CollatzResearch.WordTrace tailWord_8070775 prefixEnd_8070775 1381395609763588596465229 := by
  unfold tailWord_8070775
  simp only [CollatzResearch.WordTrace]
  refine ⟨294365347335968028476781779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196243564890645352317854519 294365347335968028476781779)
  ·
    refine ⟨441548021003952042715172669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294365347335968028476781779 441548021003952042715172669)
    ·
      refine ⟨165580507876482016018189751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441548021003952042715172669 165580507876482016018189751)
      ·
        refine ⟨248370761814723024027284627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165580507876482016018189751 248370761814723024027284627)
        ·
          refine ⟨372556142722084536040926941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248370761814723024027284627 372556142722084536040926941)
          ·
            refine ⟨139708553520781701015347603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372556142722084536040926941 139708553520781701015347603)
            ·
              refine ⟨209562830281172551523021405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139708553520781701015347603 209562830281172551523021405)
              ·
                refine ⟨78586061355439706821133027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209562830281172551523021405 78586061355439706821133027)
                ·
                  refine ⟨117879092033159560231699541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78586061355439706821133027 117879092033159560231699541)
                  ·
                    refine ⟨1381395609763588596465229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117879092033159560231699541 1381395609763588596465229)
                    ·
                      rfl

theorem cell23_8070775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_8070775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070775 prefixEnd_8070775 := by exact prefixLift 8070775
  have htrace : WordTrace (prefixWord ++ tailWord_8070775) baseStart_8070775 baseEnd_8070775 := by
    simpa [prefixWord, tailWord_8070775, baseEnd_8070775] using wordTrace_append hprefix tailTrace_8070775
  have hstable : (prefixWord ++ tailWord_8070775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070775).length < 2 ^ (prefixWord ++ tailWord_8070775).sum := by decide
  have hdescent : baseEnd_8070775 < baseStart_8070775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070829 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_8070829 : Nat := 118140960795 + 8070829 * 2 ^ 59
def prefixEnd_8070829 : Nat := 4983230072969 + 3 ^ 40 * 8070829 * 2
def baseEnd_8070829 : Nat := 4144214557246108578120439

theorem tailTrace_8070829 : CollatzResearch.WordTrace tailWord_8070829 prefixEnd_8070829 4144214557246108578120439 := by
  unfold tailWord_8070829
  simp only [CollatzResearch.WordTrace]
  refine ⟨294367316877772395699247541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196244877918514930466165027 294367316877772395699247541)
  ·
    refine ⟨27596935957291162096804457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294367316877772395699247541 27596935957291162096804457)
    ·
      refine ⟨20697701967968371572603343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27596935957291162096804457 20697701967968371572603343)
      ·
        refine ⟨31046552951952557358905015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20697701967968371572603343 31046552951952557358905015)
        ·
          refine ⟨46569829427928836038357523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31046552951952557358905015 46569829427928836038357523)
          ·
            refine ⟨69854744141893254057536285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46569829427928836038357523 69854744141893254057536285)
            ·
              refine ⟨26195529053209970271576107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69854744141893254057536285 26195529053209970271576107)
              ·
                refine ⟨39293293579814955407364161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26195529053209970271576107 39293293579814955407364161)
                ·
                  refine ⟨29469970184861216555523121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39293293579814955407364161 29469970184861216555523121)
                  ·
                    refine ⟨22102477638645912416642341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29469970184861216555523121 22102477638645912416642341)
                    ·
                      refine ⟨4144214557246108578120439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22102477638645912416642341 4144214557246108578120439)
                      ·
                        rfl

theorem cell23_8070829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_8070829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070829 prefixEnd_8070829 := by exact prefixLift 8070829
  have htrace : WordTrace (prefixWord ++ tailWord_8070829) baseStart_8070829 baseEnd_8070829 := by
    simpa [prefixWord, tailWord_8070829, baseEnd_8070829] using wordTrace_append hprefix tailTrace_8070829
  have hstable : (prefixWord ++ tailWord_8070829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070829).length < 2 ^ (prefixWord ++ tailWord_8070829).sum := by decide
  have hdescent : baseEnd_8070829 < baseStart_8070829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070832 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_8070832 : Nat := 118140960795 + 8070832 * 2 ^ 59
def prefixEnd_8070832 : Nat := 4983230072969 + 3 ^ 40 * 8070832 * 2
def baseEnd_8070832 : Nat := 4144216097688072066382925

theorem tailTrace_8070832 : CollatzResearch.WordTrace tailWord_8070832 prefixEnd_8070832 4144216097688072066382925 := by
  unfold tailWord_8070832
  simp only [CollatzResearch.WordTrace]
  refine ⟨147183713148380763605803375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196244950864507684807737833 147183713148380763605803375)
  ·
    refine ⟨220775569722571145408705063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147183713148380763605803375 220775569722571145408705063)
    ·
      refine ⟨331163354583856718113057595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220775569722571145408705063 331163354583856718113057595)
      ·
        refine ⟨496745031875785077169586393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331163354583856718113057595 496745031875785077169586393)
        ·
          refine ⟨372558773906838807877189795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496745031875785077169586393 372558773906838807877189795)
          ·
            refine ⟨558838160860258211815784693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372558773906838807877189795 558838160860258211815784693)
            ·
              refine ⟨52391077580649207357729815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558838160860258211815784693 52391077580649207357729815)
              ·
                refine ⟨78586616370973811036594723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52391077580649207357729815 78586616370973811036594723)
                ·
                  refine ⟨117879924556460716554892085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78586616370973811036594723 117879924556460716554892085)
                  ·
                    refine ⟨11051242927168192177021133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117879924556460716554892085 11051242927168192177021133)
                    ·
                      refine ⟨4144216097688072066382925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11051242927168192177021133 4144216097688072066382925)
                      ·
                        rfl

theorem cell23_8070832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_8070832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070832 prefixEnd_8070832 := by exact prefixLift 8070832
  have htrace : WordTrace (prefixWord ++ tailWord_8070832) baseStart_8070832 baseEnd_8070832 := by
    simpa [prefixWord, tailWord_8070832, baseEnd_8070832] using wordTrace_append hprefix tailTrace_8070832
  have hstable : (prefixWord ++ tailWord_8070832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070832).length < 2 ^ (prefixWord ++ tailWord_8070832).sum := by decide
  have hdescent : baseEnd_8070832 < baseStart_8070832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070854 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_8070854 : Nat := 118140960795 + 8070854 * 2 ^ 59
def prefixEnd_8070854 : Nat := 4983230072969 + 3 ^ 40 * 8070854 * 2
def baseEnd_8070854 : Nat := 4144227394262470980307825

theorem tailTrace_8070854 : CollatzResearch.WordTrace tailWord_8070854 prefixEnd_8070854 4144227394262470980307825 := by
  unfold tailWord_8070854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199007146958807030278363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196245485801787883312605077 9199007146958807030278363)
  ·
    refine ⟨13798510720438210545417545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9199007146958807030278363 13798510720438210545417545)
    ·
      refine ⟨10348883040328657909063159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13798510720438210545417545 10348883040328657909063159)
      ·
        refine ⟨15523324560492986863594739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348883040328657909063159 15523324560492986863594739)
        ·
          refine ⟨23284986840739480295392109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15523324560492986863594739 23284986840739480295392109)
          ·
            refine ⟨8731870065277305110772041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23284986840739480295392109 8731870065277305110772041)
            ·
              refine ⟨6548902548957978833079031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8731870065277305110772041 6548902548957978833079031)
              ·
                refine ⟨9823353823436968249618547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548902548957978833079031 9823353823436968249618547)
                ·
                  refine ⟨14735030735155452374427821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9823353823436968249618547 14735030735155452374427821)
                  ·
                    refine ⟨5525636525683294640410433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14735030735155452374427821 5525636525683294640410433)
                    ·
                      refine ⟨4144227394262470980307825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525636525683294640410433 4144227394262470980307825)
                      ·
                        rfl

theorem cell23_8070854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_8070854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070854 prefixEnd_8070854 := by exact prefixLift 8070854
  have htrace : WordTrace (prefixWord ++ tailWord_8070854) baseStart_8070854 baseEnd_8070854 := by
    simpa [prefixWord, tailWord_8070854, baseEnd_8070854] using wordTrace_append hprefix tailTrace_8070854
  have hstable : (prefixWord ++ tailWord_8070854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070854).length < 2 ^ (prefixWord ++ tailWord_8070854).sum := by decide
  have hdescent : baseEnd_8070854 < baseStart_8070854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070899 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 3, 4]
def baseStart_8070899 : Nat := 118140960795 + 8070899 * 2 ^ 59
def prefixEnd_8070899 : Nat := 4983230072969 + 3 ^ 40 * 8070899 * 2
def baseEnd_8070899 : Nat := 1381416833630641101415039

theorem tailTrace_8070899 : CollatzResearch.WordTrace tailWord_8070899 prefixEnd_8070899 1381416833630641101415039 := by
  unfold tailWord_8070899
  simp only [CollatzResearch.WordTrace]
  refine ⟨294369869987518797654295751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196246579991679198436197167 294369869987518797654295751)
  ·
    refine ⟨441554804981278196481443627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294369869987518797654295751 441554804981278196481443627)
    ·
      refine ⟨662332207471917294722165441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441554804981278196481443627 662332207471917294722165441)
      ·
        refine ⟨496749155603937971041624081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662332207471917294722165441 496749155603937971041624081)
        ·
          refine ⟨372561866702953478281218061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496749155603937971041624081 372561866702953478281218061)
          ·
            refine ⟨139710700013607554355456773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372561866702953478281218061 139710700013607554355456773)
            ·
              refine ⟨26195756252551416441648145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139710700013607554355456773 26195756252551416441648145)
              ·
                refine ⟨19646817189413562331236109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26195756252551416441648145 19646817189413562331236109)
                ·
                  refine ⟨7367556446030085874213541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19646817189413562331236109 7367556446030085874213541)
                  ·
                    refine ⟨1381416833630641101415039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367556446030085874213541 1381416833630641101415039)
                    ·
                      rfl

theorem cell23_8070899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 4].length) (baseStart_8070899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070899 prefixEnd_8070899 := by exact prefixLift 8070899
  have htrace : WordTrace (prefixWord ++ tailWord_8070899) baseStart_8070899 baseEnd_8070899 := by
    simpa [prefixWord, tailWord_8070899, baseEnd_8070899] using wordTrace_append hprefix tailTrace_8070899
  have hstable : (prefixWord ++ tailWord_8070899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070899).length < 2 ^ (prefixWord ++ tailWord_8070899).sum := by decide
  have hdescent : baseEnd_8070899 < baseStart_8070899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8070996 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_8070996 : Nat := 118140960795 + 8070996 * 2 ^ 59
def prefixEnd_8070996 : Nat := 4983230072969 + 3 ^ 40 * 8070996 * 2
def baseEnd_8070996 : Nat := 4144300308515409424732171

theorem tailTrace_8070996 : CollatzResearch.WordTrace tailWord_8070996 prefixEnd_8070996 4144300308515409424732171 := by
  unfold tailWord_8070996
  simp only [CollatzResearch.WordTrace]
  refine ⟨147186703934083691610288421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196248938578778255480384561 147186703934083691610288421)
  ·
    refine ⟨27597506987640692176929079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147186703934083691610288421 27597506987640692176929079)
    ·
      refine ⟨41396260481461038265393619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27597506987640692176929079 41396260481461038265393619)
      ·
        refine ⟨62094390722191557398090429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41396260481461038265393619 62094390722191557398090429)
        ·
          refine ⟨23285396520821834024283911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62094390722191557398090429 23285396520821834024283911)
          ·
            refine ⟨34928094781232751036425867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23285396520821834024283911 34928094781232751036425867)
            ·
              refine ⟨52392142171849126554638801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34928094781232751036425867 52392142171849126554638801)
              ·
                refine ⟨39294106628886844915979101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52392142171849126554638801 39294106628886844915979101)
                ·
                  refine ⟨14735289985832566843492163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39294106628886844915979101 14735289985832566843492163)
                  ·
                    refine ⟨22102934978748850265238245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14735289985832566843492163 22102934978748850265238245)
                    ·
                      refine ⟨4144300308515409424732171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22102934978748850265238245 4144300308515409424732171)
                      ·
                        rfl

theorem cell23_8070996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_8070996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8070996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8070996 prefixEnd_8070996 := by exact prefixLift 8070996
  have htrace : WordTrace (prefixWord ++ tailWord_8070996) baseStart_8070996 baseEnd_8070996 := by
    simpa [prefixWord, tailWord_8070996, baseEnd_8070996] using wordTrace_append hprefix tailTrace_8070996
  have hstable : (prefixWord ++ tailWord_8070996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8070996).length < 2 ^ (prefixWord ++ tailWord_8070996).sum := by decide
  have hdescent : baseEnd_8070996 < baseStart_8070996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8070996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071016 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_8071016 : Nat := 118140960795 + 8071016 * 2 ^ 59
def prefixEnd_8071016 : Nat := 4983230072969 + 3 ^ 40 * 8071016 * 2
def baseEnd_8071016 : Nat := 4144310578128499346482079

theorem tailTrace_8071016 : CollatzResearch.WordTrace tailWord_8071016 prefixEnd_8071016 4144310578128499346482079 := by
  unfold tailWord_8071016
  simp only [CollatzResearch.WordTrace]
  refine ⟨147187068664047463318152451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196249424885396617757536601 147187068664047463318152451)
  ·
    refine ⟨220780602996071194977228677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147187068664047463318152451 220780602996071194977228677)
    ·
      refine ⟨41396363061763349058230377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220780602996071194977228677 41396363061763349058230377)
      ·
        refine ⟨31047272296322511793672783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41396363061763349058230377 31047272296322511793672783)
        ·
          refine ⟨46570908444483767690509175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31047272296322511793672783 46570908444483767690509175)
          ·
            refine ⟨69856362666725651535763763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46570908444483767690509175 69856362666725651535763763)
            ·
              refine ⟨104784544000088477303645645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69856362666725651535763763 104784544000088477303645645)
              ·
                refine ⟨39294204000033178988867117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104784544000088477303645645 39294204000033178988867117)
                ·
                  refine ⟨14735326500012442120825169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39294204000033178988867117 14735326500012442120825169)
                  ·
                    refine ⟨11051494875009331590618877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14735326500012442120825169 11051494875009331590618877)
                    ·
                      refine ⟨4144310578128499346482079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11051494875009331590618877 4144310578128499346482079)
                      ·
                        rfl

theorem cell23_8071016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_8071016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071016 prefixEnd_8071016 := by exact prefixLift 8071016
  have htrace : WordTrace (prefixWord ++ tailWord_8071016) baseStart_8071016 baseEnd_8071016 := by
    simpa [prefixWord, tailWord_8071016, baseEnd_8071016] using wordTrace_append hprefix tailTrace_8071016
  have hstable : (prefixWord ++ tailWord_8071016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071016).length < 2 ^ (prefixWord ++ tailWord_8071016).sum := by decide
  have hdescent : baseEnd_8071016 < baseStart_8071016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071030 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_8071030 : Nat := 118140960795 + 8071030 * 2 ^ 59
def prefixEnd_8071030 : Nat := 4983230072969 + 3 ^ 40 * 8071030 * 2
def baseEnd_8071030 : Nat := 4144317766857662291707015

theorem tailTrace_8071030 : CollatzResearch.WordTrace tailWord_8071030 prefixEnd_8071030 4144317766857662291707015 := by
  unfold tailWord_8071030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398415496877762939207159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196249765300029471351543029 18398415496877762939207159)
  ·
    refine ⟨27597623245316644408810739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18398415496877762939207159 27597623245316644408810739)
    ·
      refine ⟨41396434867974966613216109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27597623245316644408810739 41396434867974966613216109)
      ·
        refine ⟨15523663075490612479956041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41396434867974966613216109 15523663075490612479956041)
        ·
          refine ⟨11642747306617959359967031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15523663075490612479956041 11642747306617959359967031)
          ·
            refine ⟨17464120959926939039950547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11642747306617959359967031 17464120959926939039950547)
            ·
              refine ⟨26196181439890408559925821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17464120959926939039950547 26196181439890408559925821)
              ·
                refine ⟨9823568039958903209972183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26196181439890408559925821 9823568039958903209972183)
                ·
                  refine ⟨14735352059938354814958275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9823568039958903209972183 14735352059938354814958275)
                  ·
                    refine ⟨22103028089907532222437413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14735352059938354814958275 22103028089907532222437413)
                    ·
                      refine ⟨4144317766857662291707015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22103028089907532222437413 4144317766857662291707015)
                      ·
                        rfl

theorem cell23_8071030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_8071030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071030 prefixEnd_8071030 := by exact prefixLift 8071030
  have htrace : WordTrace (prefixWord ++ tailWord_8071030) baseStart_8071030 baseEnd_8071030 := by
    simpa [prefixWord, tailWord_8071030, baseEnd_8071030] using wordTrace_append hprefix tailTrace_8071030
  have hstable : (prefixWord ++ tailWord_8071030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071030).length < 2 ^ (prefixWord ++ tailWord_8071030).sum := by decide
  have hdescent : baseEnd_8071030 < baseStart_8071030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071063 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_8071063 : Nat := 118140960795 + 8071063 * 2 ^ 59
def prefixEnd_8071063 : Nat := 4983230072969 + 3 ^ 40 * 8071063 * 2
def baseEnd_8071063 : Nat := 4144334711719260662594363

theorem tailTrace_8071063 : CollatzResearch.WordTrace tailWord_8071063 prefixEnd_8071063 4144334711719260662594363 := by
  unfold tailWord_8071063
  simp only [CollatzResearch.WordTrace]
  refine ⟨294375851558924653663265843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196250567705949769108843895 294375851558924653663265843)
  ·
    refine ⟨441563777338386980494898765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294375851558924653663265843 441563777338386980494898765)
    ·
      refine ⟨165586416501895117685587037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441563777338386980494898765 165586416501895117685587037)
      ·
        refine ⟨62094906188210669132095139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165586416501895117685587037 62094906188210669132095139)
        ·
          refine ⟨93142359282316003698142709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62094906188210669132095139 93142359282316003698142709)
          ·
            refine ⟨8732096182717125346700879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93142359282316003698142709 8732096182717125346700879)
            ·
              refine ⟨13098144274075688020051319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732096182717125346700879 13098144274075688020051319)
              ·
                refine ⟨19647216411113532030076979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13098144274075688020051319 19647216411113532030076979)
                ·
                  refine ⟨29470824616670298045115469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19647216411113532030076979 29470824616670298045115469)
                  ·
                    refine ⟨11051559231251361766918301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29470824616670298045115469 11051559231251361766918301)
                    ·
                      refine ⟨4144334711719260662594363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11051559231251361766918301 4144334711719260662594363)
                      ·
                        rfl

theorem cell23_8071063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_8071063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071063 prefixEnd_8071063 := by exact prefixLift 8071063
  have htrace : WordTrace (prefixWord ++ tailWord_8071063) baseStart_8071063 baseEnd_8071063 := by
    simpa [prefixWord, tailWord_8071063, baseEnd_8071063] using wordTrace_append hprefix tailTrace_8071063
  have hstable : (prefixWord ++ tailWord_8071063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071063).length < 2 ^ (prefixWord ++ tailWord_8071063).sum := by decide
  have hdescent : baseEnd_8071063 < baseStart_8071063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071103 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 4, 2, 2]
def baseStart_8071103 : Nat := 118140960795 + 8071103 * 2 ^ 59
def prefixEnd_8071103 : Nat := 4983230072969 + 3 ^ 40 * 8071103 * 2
def baseEnd_8071103 : Nat := 4144355250945440506094179

theorem tailTrace_8071103 : CollatzResearch.WordTrace tailWord_8071103 prefixEnd_8071103 4144355250945440506094179 := by
  unfold tailWord_8071103
  simp only [CollatzResearch.WordTrace]
  refine ⟨294377310478779740494721963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196251540319186493663147975 294377310478779740494721963)
  ·
    refine ⟨441565965718169610742082945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294377310478779740494721963 441565965718169610742082945)
    ·
      refine ⟨331174474288627208056562209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441565965718169610742082945 331174474288627208056562209)
      ·
        refine ⟨248380855716470406042421657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331174474288627208056562209 248380855716470406042421657)
        ·
          refine ⟨186285641787352804531816243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248380855716470406042421657 186285641787352804531816243)
          ·
            refine ⟨279428462681029206797724365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186285641787352804531816243 279428462681029206797724365)
            ·
              refine ⟨104785673505385952549146637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279428462681029206797724365 104785673505385952549146637)
              ·
                refine ⟨39294627564519732205929989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104785673505385952549146637 39294627564519732205929989)
                ·
                  refine ⟨7367742668347449788611873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39294627564519732205929989 7367742668347449788611873)
                  ·
                    refine ⟨5525807001260587341458905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7367742668347449788611873 5525807001260587341458905)
                    ·
                      refine ⟨4144355250945440506094179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525807001260587341458905 4144355250945440506094179)
                      ·
                        rfl

theorem cell23_8071103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_8071103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071103 prefixEnd_8071103 := by exact prefixLift 8071103
  have htrace : WordTrace (prefixWord ++ tailWord_8071103) baseStart_8071103 baseEnd_8071103 := by
    simpa [prefixWord, tailWord_8071103, baseEnd_8071103] using wordTrace_append hprefix tailTrace_8071103
  have hstable : (prefixWord ++ tailWord_8071103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071103).length < 2 ^ (prefixWord ++ tailWord_8071103).sum := by decide
  have hdescent : baseEnd_8071103 < baseStart_8071103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071109 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 7]
def baseStart_8071109 : Nat := 118140960795 + 8071109 * 2 ^ 59
def prefixEnd_8071109 : Nat := 4983230072969 + 3 ^ 40 * 8071109 * 2
def baseEnd_8071109 : Nat := 460484259092151942513239

theorem tailTrace_8071109 : CollatzResearch.WordTrace tailWord_8071109 prefixEnd_8071109 460484259092151942513239 := by
  unfold tailWord_8071109
  simp only [CollatzResearch.WordTrace]
  refine ⟨294377529316758003519440381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196251686211172002346293587 294377529316758003519440381)
  ·
    refine ⟨110391573493784251319790143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294377529316758003519440381 110391573493784251319790143)
    ·
      refine ⟨165587360240676376979685215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110391573493784251319790143 165587360240676376979685215)
      ·
        refine ⟨248381040361014565469527823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165587360240676376979685215 248381040361014565469527823)
        ·
          refine ⟨372571560541521848204291735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248381040361014565469527823 372571560541521848204291735)
          ·
            refine ⟨558857340812282772306437603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372571560541521848204291735 558857340812282772306437603)
            ·
              refine ⟨838286011218424158459656405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558857340812282772306437603 838286011218424158459656405)
              ·
                refine ⟨19647328387931816213898197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 838286011218424158459656405 19647328387931816213898197)
                ·
                  refine ⟨460484259092151942513239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19647328387931816213898197 460484259092151942513239)
                  ·
                    rfl

theorem cell23_8071109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_8071109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071109 prefixEnd_8071109 := by exact prefixLift 8071109
  have htrace : WordTrace (prefixWord ++ tailWord_8071109) baseStart_8071109 baseEnd_8071109 := by
    simpa [prefixWord, tailWord_8071109, baseEnd_8071109] using wordTrace_append hprefix tailTrace_8071109
  have hstable : (prefixWord ++ tailWord_8071109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071109).length < 2 ^ (prefixWord ++ tailWord_8071109).sum := by decide
  have hdescent : baseEnd_8071109 < baseStart_8071109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071176 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_8071176 : Nat := 118140960795 + 8071176 * 2 ^ 59
def prefixEnd_8071176 : Nat := 4983230072969 + 3 ^ 40 * 8071176 * 2
def baseEnd_8071176 : Nat := 4144392735033218720481343

theorem tailTrace_8071176 : CollatzResearch.WordTrace tailWord_8071176 prefixEnd_8071176 4144392735033218720481343 := by
  unfold tailWord_8071176
  simp only [CollatzResearch.WordTrace]
  refine ⟨147189986503757636981064691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196253315338343515974752921 147189986503757636981064691)
  ·
    refine ⟨220784979755636455471597037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147189986503757636981064691 220784979755636455471597037)
    ·
      refine ⟨82794367408363670801848889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220784979755636455471597037 82794367408363670801848889)
      ·
        refine ⟨62095775556272753101386667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82794367408363670801848889 62095775556272753101386667)
        ·
          refine ⟨93143663334409129652080001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62095775556272753101386667 93143663334409129652080001)
          ·
            refine ⟨69857747500806847239060001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93143663334409129652080001 69857747500806847239060001)
            ·
              refine ⟨52393310625605135429295001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69857747500806847239060001 52393310625605135429295001)
              ·
                refine ⟨39294982969203851571971251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52393310625605135429295001 39294982969203851571971251)
                ·
                  refine ⟨58942474453805777357956877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39294982969203851571971251 58942474453805777357956877)
                  ·
                    refine ⟨22103427920177166509233829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58942474453805777357956877 22103427920177166509233829)
                    ·
                      refine ⟨4144392735033218720481343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22103427920177166509233829 4144392735033218720481343)
                      ·
                        rfl

theorem cell23_8071176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_8071176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071176 prefixEnd_8071176 := by exact prefixLift 8071176
  have htrace : WordTrace (prefixWord ++ tailWord_8071176) baseStart_8071176 baseEnd_8071176 := by
    simpa [prefixWord, tailWord_8071176, baseEnd_8071176] using wordTrace_append hprefix tailTrace_8071176
  have hstable : (prefixWord ++ tailWord_8071176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071176).length < 2 ^ (prefixWord ++ tailWord_8071176).sum := by decide
  have hdescent : baseEnd_8071176 < baseStart_8071176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071210 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_8071210 : Nat := 118140960795 + 8071210 * 2 ^ 59
def prefixEnd_8071210 : Nat := 4983230072969 + 3 ^ 40 * 8071210 * 2
def baseEnd_8071210 : Nat := 4144410193375471587456187

theorem tailTrace_8071210 : CollatzResearch.WordTrace tailWord_8071210 prefixEnd_8071210 4144410193375471587456187 := by
  unfold tailWord_8071210
  simp only [CollatzResearch.WordTrace]
  refine ⟨73595303272348024442216771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196254142059594731845911389 73595303272348024442216771)
  ·
    refine ⟨110392954908522036663325157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73595303272348024442216771 110392954908522036663325157)
    ·
      refine ⟨20698679045347881874373467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110392954908522036663325157 20698679045347881874373467)
      ·
        refine ⟨31048018568021822811560201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20698679045347881874373467 31048018568021822811560201)
        ·
          refine ⟨23286013926016367108670151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31048018568021822811560201 23286013926016367108670151)
          ·
            refine ⟨34929020889024550663005227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23286013926016367108670151 34929020889024550663005227)
            ·
              refine ⟨52393531333536825994507841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34929020889024550663005227 52393531333536825994507841)
              ·
                refine ⟨39295148500152619495880881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52393531333536825994507841 39295148500152619495880881)
                ·
                  refine ⟨29471361375114464621910661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39295148500152619495880881 29471361375114464621910661)
                  ·
                    refine ⟨5525880257833962116608249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29471361375114464621910661 5525880257833962116608249)
                    ·
                      refine ⟨4144410193375471587456187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5525880257833962116608249 4144410193375471587456187)
                      ·
                        rfl

theorem cell23_8071210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_8071210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071210 prefixEnd_8071210 := by exact prefixLift 8071210
  have htrace : WordTrace (prefixWord ++ tailWord_8071210) baseStart_8071210 baseEnd_8071210 := by
    simpa [prefixWord, tailWord_8071210, baseEnd_8071210] using wordTrace_append hprefix tailTrace_8071210
  have hstable : (prefixWord ++ tailWord_8071210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071210).length < 2 ^ (prefixWord ++ tailWord_8071210).sum := by decide
  have hdescent : baseEnd_8071210 < baseStart_8071210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071216 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 8]
def baseStart_8071216 : Nat := 118140960795 + 8071216 * 2 ^ 59
def prefixEnd_8071216 : Nat := 4983230072969 + 3 ^ 40 * 8071216 * 2
def baseEnd_8071216 : Nat := 460490363806599840442351

theorem tailTrace_8071216 : CollatzResearch.WordTrace tailWord_8071216 prefixEnd_8071216 460490363806599840442351 := by
  unfold tailWord_8071216
  simp only [CollatzResearch.WordTrace]
  refine ⟨147190715963685180396792751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196254287951580240529057001 147190715963685180396792751)
  ·
    refine ⟨220786073945527770595189127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147190715963685180396792751 220786073945527770595189127)
    ·
      refine ⟨331179110918291655892783691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220786073945527770595189127 331179110918291655892783691)
      ·
        refine ⟨496768666377437483839175537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331179110918291655892783691 496768666377437483839175537)
        ·
          refine ⟨372576499783078112879381653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496768666377437483839175537 372576499783078112879381653)
          ·
            refine ⟨17464523427331786541221015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 372576499783078112879381653 17464523427331786541221015)
            ·
              refine ⟨26196785140997679811831523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17464523427331786541221015 26196785140997679811831523)
              ·
                refine ⟨39295177711496519717747285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26196785140997679811831523 39295177711496519717747285)
                ·
                  refine ⟨460490363806599840442351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39295177711496519717747285 460490363806599840442351)
                  ·
                    rfl

theorem cell23_8071216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_8071216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071216 prefixEnd_8071216 := by exact prefixLift 8071216
  have htrace : WordTrace (prefixWord ++ tailWord_8071216) baseStart_8071216 baseEnd_8071216 := by
    simpa [prefixWord, tailWord_8071216, baseEnd_8071216] using wordTrace_append hprefix tailTrace_8071216
  have hstable : (prefixWord ++ tailWord_8071216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071216).length < 2 ^ (prefixWord ++ tailWord_8071216).sum := by decide
  have hdescent : baseEnd_8071216 < baseStart_8071216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071297 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 1, 5]
def baseStart_8071297 : Nat := 118140960795 + 8071297 * 2 ^ 59
def prefixEnd_8071297 : Nat := 4983230072969 + 3 ^ 40 * 8071297 * 2
def baseEnd_8071297 : Nat := 1381484955397470915689429

theorem tailTrace_8071297 : CollatzResearch.WordTrace tailWord_8071297 prefixEnd_8071297 1381484955397470915689429 := by
  unfold tailWord_8071297
  simp only [CollatzResearch.WordTrace]
  refine ⟨294384386240076911627284145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196256257493384607751522763 294384386240076911627284145)
  ·
    refine ⟨220788289680057683720463109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294384386240076911627284145 220788289680057683720463109)
    ·
      refine ⟨41397804315010815697586833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220788289680057683720463109 41397804315010815697586833)
      ·
        refine ⟨31048353236258111773190125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41397804315010815697586833 31048353236258111773190125)
        ·
          refine ⟨11643132463596791914946297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31048353236258111773190125 11643132463596791914946297)
          ·
            refine ⟨8732349347697593936209723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11643132463596791914946297 8732349347697593936209723)
            ·
              refine ⟨13098524021546390904314585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732349347697593936209723 13098524021546390904314585)
              ·
                refine ⟨9823893016159793178235939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13098524021546390904314585 9823893016159793178235939)
                ·
                  refine ⟨14735839524239689767353909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9823893016159793178235939 14735839524239689767353909)
                  ·
                    refine ⟨1381484955397470915689429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14735839524239689767353909 1381484955397470915689429)
                    ·
                      rfl

theorem cell23_8071297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_8071297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071297 prefixEnd_8071297 := by exact prefixLift 8071297
  have htrace : WordTrace (prefixWord ++ tailWord_8071297) baseStart_8071297 baseEnd_8071297 := by
    simpa [prefixWord, tailWord_8071297, baseEnd_8071297] using wordTrace_append hprefix tailTrace_8071297
  have hstable : (prefixWord ++ tailWord_8071297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071297).length < 2 ^ (prefixWord ++ tailWord_8071297).sum := by decide
  have hdescent : baseEnd_8071297 < baseStart_8071297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071310 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_8071310 : Nat := 118140960795 + 8071310 * 2 ^ 59
def prefixEnd_8071310 : Nat := 4983230072969 + 3 ^ 40 * 8071310 * 2
def baseEnd_8071310 : Nat := 1381487180480307065401909

theorem tailTrace_8071310 : CollatzResearch.WordTrace tailWord_8071310 prefixEnd_8071310 1381487180480307065401909 := by
  unfold tailWord_8071310
  simp only [CollatzResearch.WordTrace]
  refine ⟨36798107548628726855938423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196256573592686543231671589 36798107548628726855938423)
  ·
    refine ⟨55197161322943090283907635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36798107548628726855938423 55197161322943090283907635)
    ·
      refine ⟨82795741984414635425861453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55197161322943090283907635 82795741984414635425861453)
      ·
        refine ⟨31048403244155488284698045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82795741984414635425861453 31048403244155488284698045)
        ·
          refine ⟨11643151216558308106761767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31048403244155488284698045 11643151216558308106761767)
          ·
            refine ⟨17464726824837462160142651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11643151216558308106761767 17464726824837462160142651)
            ·
              refine ⟨26197090237256193240213977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17464726824837462160142651 26197090237256193240213977)
              ·
                refine ⟨19647817677942144930160483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26197090237256193240213977 19647817677942144930160483)
                ·
                  refine ⟨29471726516913217395240725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19647817677942144930160483 29471726516913217395240725)
                  ·
                    refine ⟨1381487180480307065401909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29471726516913217395240725 1381487180480307065401909)
                    ·
                      rfl

theorem cell23_8071310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_8071310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071310 prefixEnd_8071310 := by exact prefixLift 8071310
  have htrace : WordTrace (prefixWord ++ tailWord_8071310) baseStart_8071310 baseEnd_8071310 := by
    simpa [prefixWord, tailWord_8071310, baseEnd_8071310] using wordTrace_append hprefix tailTrace_8071310
  have hstable : (prefixWord ++ tailWord_8071310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071310).length < 2 ^ (prefixWord ++ tailWord_8071310).sum := by decide
  have hdescent : baseEnd_8071310 < baseStart_8071310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071327 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 2, 4]
def baseStart_8071327 : Nat := 118140960795 + 8071327 * 2 ^ 59
def prefixEnd_8071327 : Nat := 4983230072969 + 3 ^ 40 * 8071327 * 2
def baseEnd_8071327 : Nat := 1381490090204015876564383

theorem tailTrace_8071327 : CollatzResearch.WordTrace tailWord_8071327 prefixEnd_8071327 1381490090204015876564383 := by
  unfold tailWord_8071327
  simp only [CollatzResearch.WordTrace]
  refine ⟨294385480429968226750876235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196256986953312151167250823 294385480429968226750876235)
  ·
    refine ⟨441578220644952340126314353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294385480429968226750876235 441578220644952340126314353)
    ·
      refine ⟨331183665483714255094735765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441578220644952340126314353 331183665483714255094735765)
      ·
        refine ⟨15524234319549105707565739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331183665483714255094735765 15524234319549105707565739)
        ·
          refine ⟨23286351479323658561348609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15524234319549105707565739 23286351479323658561348609)
          ·
            refine ⟨17464763609492743921011457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23286351479323658561348609 17464763609492743921011457)
            ·
              refine ⟨13098572707119557940758593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17464763609492743921011457 13098572707119557940758593)
              ·
                refine ⟨9823929530339668455568945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13098572707119557940758593 9823929530339668455568945)
                ·
                  refine ⟨7367947147754751341676709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9823929530339668455568945 7367947147754751341676709)
                  ·
                    refine ⟨1381490090204015876564383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7367947147754751341676709 1381490090204015876564383)
                    ·
                      rfl

theorem cell23_8071327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_8071327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071327 prefixEnd_8071327 := by exact prefixLift 8071327
  have htrace : WordTrace (prefixWord ++ tailWord_8071327) baseStart_8071327 baseEnd_8071327 := by
    simpa [prefixWord, tailWord_8071327, baseEnd_8071327] using wordTrace_append hprefix tailTrace_8071327
  have hstable : (prefixWord ++ tailWord_8071327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071327).length < 2 ^ (prefixWord ++ tailWord_8071327).sum := by decide
  have hdescent : baseEnd_8071327 < baseStart_8071327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071333 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_8071333 : Nat := 118140960795 + 8071333 * 2 ^ 59
def prefixEnd_8071333 : Nat := 4983230072969 + 3 ^ 40 * 8071333 * 2
def baseEnd_8071333 : Nat := 4144473351495974606218121

theorem tailTrace_8071333 : CollatzResearch.WordTrace tailWord_8071333 prefixEnd_8071333 4144473351495974606218121 := by
  unfold tailWord_8071333
  simp only [CollatzResearch.WordTrace]
  refine ⟨294385699267946489775594653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196257132845297659850396435 294385699267946489775594653)
  ·
    refine ⟨110394637225479933665847995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294385699267946489775594653 110394637225479933665847995)
    ·
      refine ⟨165591955838219900498771993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110394637225479933665847995 165591955838219900498771993)
      ·
        refine ⟨124193966878664925374078995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165591955838219900498771993 124193966878664925374078995)
        ·
          refine ⟨186290950317997388061118493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124193966878664925374078995 186290950317997388061118493)
          ·
            refine ⟨69859106369249020522919435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186290950317997388061118493 69859106369249020522919435)
            ·
              refine ⟨104788659553873530784379153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69859106369249020522919435 104788659553873530784379153)
              ·
                refine ⟨78591494665405148088284365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104788659553873530784379153 78591494665405148088284365)
                ·
                  refine ⟨29471810499526930533106637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78591494665405148088284365 29471810499526930533106637)
                  ·
                    refine ⟨11051928937322598949914989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29471810499526930533106637 11051928937322598949914989)
                    ·
                      refine ⟨4144473351495974606218121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11051928937322598949914989 4144473351495974606218121)
                      ·
                        rfl

theorem cell23_8071333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_8071333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071333 prefixEnd_8071333 := by exact prefixLift 8071333
  have htrace : WordTrace (prefixWord ++ tailWord_8071333) baseStart_8071333 baseEnd_8071333 := by
    simpa [prefixWord, tailWord_8071333, baseEnd_8071333] using wordTrace_append hprefix tailTrace_8071333
  have hstable : (prefixWord ++ tailWord_8071333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071333).length < 2 ^ (prefixWord ++ tailWord_8071333).sum := by decide
  have hdescent : baseEnd_8071333 < baseStart_8071333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071384 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_8071384 : Nat := 118140960795 + 8071384 * 2 ^ 59
def prefixEnd_8071384 : Nat := 4983230072969 + 3 ^ 40 * 8071384 * 2
def baseEnd_8071384 : Nat := 4144499539009353906680387

theorem tailTrace_8071384 : CollatzResearch.WordTrace tailWord_8071384 prefixEnd_8071384 4144499539009353906680387 := by
  unfold tailWord_8071384
  simp only [CollatzResearch.WordTrace]
  refine ⟨147193779695380862742850603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196258372927174483657134137 147193779695380862742850603)
  ·
    refine ⟨220790669543071294114275905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147193779695380862742850603 220790669543071294114275905)
    ·
      refine ⟨165593002157303470585706929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220790669543071294114275905 165593002157303470585706929)
      ·
        refine ⟨124194751617977602939280197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165593002157303470585706929 124194751617977602939280197)
        ·
          refine ⟨23286515928370800551115037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124194751617977602939280197 23286515928370800551115037)
          ·
            refine ⟨8732443473139050206668139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23286515928370800551115037 8732443473139050206668139)
            ·
              refine ⟨13098665209708575310002209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732443473139050206668139 13098665209708575310002209)
              ·
                refine ⟨9823998907281431482501657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13098665209708575310002209 9823998907281431482501657)
                ·
                  refine ⟨7367999180461073611876243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9823998907281431482501657 7367999180461073611876243)
                  ·
                    refine ⟨11051998770691610417814365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367999180461073611876243 11051998770691610417814365)
                    ·
                      refine ⟨4144499539009353906680387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11051998770691610417814365 4144499539009353906680387)
                      ·
                        rfl

theorem cell23_8071384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_8071384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071384 prefixEnd_8071384 := by exact prefixLift 8071384
  have htrace : WordTrace (prefixWord ++ tailWord_8071384) baseStart_8071384 baseEnd_8071384 := by
    simpa [prefixWord, tailWord_8071384, baseEnd_8071384] using wordTrace_append hprefix tailTrace_8071384
  have hstable : (prefixWord ++ tailWord_8071384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071384).length < 2 ^ (prefixWord ++ tailWord_8071384).sum := by decide
  have hdescent : baseEnd_8071384 < baseStart_8071384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071403 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4]
def baseStart_8071403 : Nat := 118140960795 + 8071403 * 2 ^ 59
def prefixEnd_8071403 : Nat := 4983230072969 + 3 ^ 40 * 8071403 * 2
def baseEnd_8071403 : Nat := 4144509295141789332342799

theorem tailTrace_8071403 : CollatzResearch.WordTrace tailWord_8071403 prefixEnd_8071403 4144509295141789332342799 := by
  unfold tailWord_8071403
  simp only [CollatzResearch.WordTrace]
  refine ⟨294388252377692891730642863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196258834918461927820428575 294388252377692891730642863)
  ·
    refine ⟨441582378566539337595964295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294388252377692891730642863 441582378566539337595964295)
    ·
      refine ⟨662373567849809006393946443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441582378566539337595964295 662373567849809006393946443)
      ·
        refine ⟨993560351774713509590919665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662373567849809006393946443 993560351774713509590919665)
        ·
          refine ⟨745170263831035132193189749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993560351774713509590919665 745170263831035132193189749)
          ·
            refine ⟨69859712234159543643111539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 745170263831035132193189749 69859712234159543643111539)
            ·
              refine ⟨104789568351239315464667309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69859712234159543643111539 104789568351239315464667309)
              ·
                refine ⟨39296088131714743299250241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104789568351239315464667309 39296088131714743299250241)
                ·
                  refine ⟨29472066098786057474437681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39296088131714743299250241 29472066098786057474437681)
                  ·
                    refine ⟨22104049574089543105828261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29472066098786057474437681 22104049574089543105828261)
                    ·
                      refine ⟨4144509295141789332342799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22104049574089543105828261 4144509295141789332342799)
                      ·
                        rfl

theorem cell23_8071403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_8071403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071403 prefixEnd_8071403 := by exact prefixLift 8071403
  have htrace : WordTrace (prefixWord ++ tailWord_8071403) baseStart_8071403 baseEnd_8071403 := by
    simpa [prefixWord, tailWord_8071403, baseEnd_8071403] using wordTrace_append hprefix tailTrace_8071403
  have hstable : (prefixWord ++ tailWord_8071403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071403).length < 2 ^ (prefixWord ++ tailWord_8071403).sum := by decide
  have hdescent : baseEnd_8071403 < baseStart_8071403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071407 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 1, 4, 2]
def baseStart_8071407 : Nat := 118140960795 + 8071407 * 2 ^ 59
def prefixEnd_8071407 : Nat := 4983230072969 + 3 ^ 40 * 8071407 * 2
def baseEnd_8071407 : Nat := 4144511349064407316692781

theorem tailTrace_8071407 : CollatzResearch.WordTrace tailWord_8071407 prefixEnd_8071407 4144511349064407316692781 := by
  unfold tailWord_8071407
  simp only [CollatzResearch.WordTrace]
  refine ⟨294388398269678400413788475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196258932179785600275858983 294388398269678400413788475)
  ·
    refine ⟨441582597404517600620682713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294388398269678400413788475 441582597404517600620682713)
    ·
      refine ⟨331186948053388200465512035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441582597404517600620682713 331186948053388200465512035)
      ·
        refine ⟨496780422080082300698268053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331186948053388200465512035 496780422080082300698268053)
        ·
          refine ⟨23286582285003857845231315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 496780422080082300698268053 23286582285003857845231315)
          ·
            refine ⟨34929873427505786767846973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23286582285003857845231315 34929873427505786767846973)
            ·
              refine ⟨13098702535314670037942615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34929873427505786767846973 13098702535314670037942615)
              ·
                refine ⟨19648053802972005056913923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13098702535314670037942615 19648053802972005056913923)
                ·
                  refine ⟨29472080704458007585370885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19648053802972005056913923 29472080704458007585370885)
                  ·
                    refine ⟨5526015132085876422257041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29472080704458007585370885 5526015132085876422257041)
                    ·
                      refine ⟨4144511349064407316692781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526015132085876422257041 4144511349064407316692781)
                      ·
                        rfl

theorem cell23_8071407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4, 2].length) (baseStart_8071407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071407 prefixEnd_8071407 := by exact prefixLift 8071407
  have htrace : WordTrace (prefixWord ++ tailWord_8071407) baseStart_8071407 baseEnd_8071407 := by
    simpa [prefixWord, tailWord_8071407, baseEnd_8071407] using wordTrace_append hprefix tailTrace_8071407
  have hstable : (prefixWord ++ tailWord_8071407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071407).length < 2 ^ (prefixWord ++ tailWord_8071407).sum := by decide
  have hdescent : baseEnd_8071407 < baseStart_8071407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071458 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_8071458 : Nat := 118140960795 + 8071458 * 2 ^ 59
def prefixEnd_8071458 : Nat := 4983230072969 + 3 ^ 40 * 8071458 * 2
def baseEnd_8071458 : Nat := 4144537536577786617155047

theorem tailTrace_8071458 : CollatzResearch.WordTrace tailWord_8071458 prefixEnd_8071458 4144537536577786617155047 := by
  unfold tailWord_8071458
  simp only [CollatzResearch.WordTrace]
  refine ⟨73597564598123409030973757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196260172261662424082596685 73597564598123409030973757)
  ·
    refine ⟨27599086724296278386615159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73597564598123409030973757 27599086724296278386615159)
    ·
      refine ⟨41398630086444417579922739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27599086724296278386615159 41398630086444417579922739)
      ·
        refine ⟨62097945129666626369884109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41398630086444417579922739 62097945129666626369884109)
        ·
          refine ⟨23286729423624984888706541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62097945129666626369884109 23286729423624984888706541)
          ·
            refine ⟨8732523533859369333264953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23286729423624984888706541 8732523533859369333264953)
            ·
              refine ⟨6549392650394526999948715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8732523533859369333264953 6549392650394526999948715)
              ·
                refine ⟨9824088975591790499923073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549392650394526999948715 9824088975591790499923073)
                ·
                  refine ⟨7368066731693842874942305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9824088975591790499923073 7368066731693842874942305)
                  ·
                    refine ⟨5526050048770382156206729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368066731693842874942305 5526050048770382156206729)
                    ·
                      refine ⟨4144537536577786617155047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526050048770382156206729 4144537536577786617155047)
                      ·
                        rfl

theorem cell23_8071458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_8071458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071458 prefixEnd_8071458 := by exact prefixLift 8071458
  have htrace : WordTrace (prefixWord ++ tailWord_8071458) baseStart_8071458 baseEnd_8071458 := by
    simpa [prefixWord, tailWord_8071458, baseEnd_8071458] using wordTrace_append hprefix tailTrace_8071458
  have hstable : (prefixWord ++ tailWord_8071458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071458).length < 2 ^ (prefixWord ++ tailWord_8071458).sum := by decide
  have hdescent : baseEnd_8071458 < baseStart_8071458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071480 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_8071480 : Nat := 118140960795 + 8071480 * 2 ^ 59
def prefixEnd_8071480 : Nat := 4983230072969 + 3 ^ 40 * 8071480 * 2
def baseEnd_8071480 : Nat := 4144548833152185531079945

theorem tailTrace_8071480 : CollatzResearch.WordTrace tailWord_8071480 prefixEnd_8071480 4144548833152185531079945 := by
  unfold tailWord_8071480
  simp only [CollatzResearch.WordTrace]
  refine ⟨147195530399206966940597947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196260707198942622587463929 147195530399206966940597947)
  ·
    refine ⟨220793295598810450410896921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147195530399206966940597947 220793295598810450410896921)
    ·
      refine ⟨165594971699107837808172691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220793295598810450410896921 165594971699107837808172691)
      ·
        refine ⟨248392457548661756712259037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165594971699107837808172691 248392457548661756712259037)
        ·
          refine ⟨93147171580748158767097139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248392457548661756712259037 93147171580748158767097139)
          ·
            refine ⟨139720757371122238150645709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93147171580748158767097139 139720757371122238150645709)
            ·
              refine ⟨52395284014170839306492141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139720757371122238150645709 52395284014170839306492141)
              ·
                refine ⟨19648231505314064739934553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52395284014170839306492141 19648231505314064739934553)
                ·
                  refine ⟨14736173628985548554950915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19648231505314064739934553 14736173628985548554950915)
                  ·
                    refine ⟨22104260443478322832426373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14736173628985548554950915 22104260443478322832426373)
                    ·
                      refine ⟨4144548833152185531079945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22104260443478322832426373 4144548833152185531079945)
                      ·
                        rfl

theorem cell23_8071480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_8071480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071480 prefixEnd_8071480 := by exact prefixLift 8071480
  have htrace : WordTrace (prefixWord ++ tailWord_8071480) baseStart_8071480 baseEnd_8071480 := by
    simpa [prefixWord, tailWord_8071480, baseEnd_8071480] using wordTrace_append hprefix tailTrace_8071480
  have hstable : (prefixWord ++ tailWord_8071480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071480).length < 2 ^ (prefixWord ++ tailWord_8071480).sum := by decide
  have hdescent : baseEnd_8071480 < baseStart_8071480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071541 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_8071541 : Nat := 118140960795 + 8071541 * 2 ^ 59
def prefixEnd_8071541 : Nat := 4983230072969 + 3 ^ 40 * 8071541 * 2
def baseEnd_8071541 : Nat := 1381526718490703264139055

theorem tailTrace_8071541 : CollatzResearch.WordTrace tailWord_8071541 prefixEnd_8071541 1381526718490703264139055 := by
  unfold tailWord_8071541
  simp only [CollatzResearch.WordTrace]
  refine ⟨294393285651192941299166477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196262190434128627532777651 294393285651192941299166477)
  ·
    refine ⟨110397482119197352987187429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294393285651192941299166477 110397482119197352987187429)
    ·
      refine ⟨20699527897349503685097643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110397482119197352987187429 20699527897349503685097643)
      ·
        refine ⟨31049291846024255527646465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20699527897349503685097643 31049291846024255527646465)
        ·
          refine ⟨23286968884518191645734849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31049291846024255527646465 23286968884518191645734849)
          ·
            refine ⟨17465226663388643734301137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23286968884518191645734849 17465226663388643734301137)
            ·
              refine ⟨13098919997541482800725853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17465226663388643734301137 13098919997541482800725853)
              ·
                refine ⟨4912094999078056050272195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13098919997541482800725853 4912094999078056050272195)
                ·
                  refine ⟨7368142498617084075408293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912094999078056050272195 7368142498617084075408293)
                  ·
                    refine ⟨1381526718490703264139055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7368142498617084075408293 1381526718490703264139055)
                    ·
                      rfl

theorem cell23_8071541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_8071541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071541 prefixEnd_8071541 := by exact prefixLift 8071541
  have htrace : WordTrace (prefixWord ++ tailWord_8071541) baseStart_8071541 baseEnd_8071541 := by
    simpa [prefixWord, tailWord_8071541, baseEnd_8071541] using wordTrace_append hprefix tailTrace_8071541
  have hstable : (prefixWord ++ tailWord_8071541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071541).length < 2 ^ (prefixWord ++ tailWord_8071541).sum := by decide
  have hdescent : baseEnd_8071541 < baseStart_8071541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071554 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_8071554 : Nat := 118140960795 + 8071554 * 2 ^ 59
def prefixEnd_8071554 : Nat := 4983230072969 + 3 ^ 40 * 8071554 * 2
def baseEnd_8071554 : Nat := 460509647857846471283845

theorem tailTrace_8071554 : CollatzResearch.WordTrace tailWord_8071554 prefixEnd_8071554 460509647857846471283845 := by
  unfold tailWord_8071554
  simp only [CollatzResearch.WordTrace]
  refine ⟨73598439950036461129847429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196262506533430563012926477 73598439950036461129847429)
  ·
    refine ⟨13799707490631836461846393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73598439950036461129847429 13799707490631836461846393)
    ·
      refine ⟨10349780617973877346384795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13799707490631836461846393 10349780617973877346384795)
      ·
        refine ⟨15524670926960816019577193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10349780617973877346384795 15524670926960816019577193)
        ·
          refine ⟨11643503195220612014682895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15524670926960816019577193 11643503195220612014682895)
          ·
            refine ⟨17465254792830918022024343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11643503195220612014682895 17465254792830918022024343)
            ·
              refine ⟨26197882189246377033036515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17465254792830918022024343 26197882189246377033036515)
              ·
                refine ⟨39296823283869565549554773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26197882189246377033036515 39296823283869565549554773)
                ·
                  refine ⟨460509647857846471283845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39296823283869565549554773 460509647857846471283845)
                  ·
                    rfl

theorem cell23_8071554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_8071554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071554 prefixEnd_8071554 := by exact prefixLift 8071554
  have htrace : WordTrace (prefixWord ++ tailWord_8071554) baseStart_8071554 baseEnd_8071554 := by
    simpa [prefixWord, tailWord_8071554, baseEnd_8071554] using wordTrace_append hprefix tailTrace_8071554
  have hstable : (prefixWord ++ tailWord_8071554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071554).length < 2 ^ (prefixWord ++ tailWord_8071554).sum := by decide
  have hdescent : baseEnd_8071554 < baseStart_8071554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071557 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 4, 3, 2]
def baseStart_8071557 : Nat := 118140960795 + 8071557 * 2 ^ 59
def prefixEnd_8071557 : Nat := 4983230072969 + 3 ^ 40 * 8071557 * 2
def baseEnd_8071557 : Nat := 4144588371162581729817091

theorem tailTrace_8071557 : CollatzResearch.WordTrace tailWord_8071557 prefixEnd_8071557 4144588371162581729817091 := by
  unfold tailWord_8071557
  simp only [CollatzResearch.WordTrace]
  refine ⟨294393869219134976031748925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196262579479423317354499283 294393869219134976031748925)
  ·
    refine ⟨110397700957175616011905847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294393869219134976031748925 110397700957175616011905847)
    ·
      refine ⟨165596551435763424017858771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110397700957175616011905847 165596551435763424017858771)
      ·
        refine ⟨248394827153645136026788157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165596551435763424017858771 248394827153645136026788157)
        ·
          refine ⟨93148060182616926010045559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248394827153645136026788157 93148060182616926010045559)
          ·
            refine ⟨139722090273925389015068339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93148060182616926010045559 139722090273925389015068339)
            ·
              refine ⟨209583135410888083522602509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139722090273925389015068339 209583135410888083522602509)
              ·
                refine ⟨78593675779083031320975941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209583135410888083522602509 78593675779083031320975941)
                ·
                  refine ⟨14736314208578068372682989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78593675779083031320975941 14736314208578068372682989)
                  ·
                    refine ⟨5526117828216775639756121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14736314208578068372682989 5526117828216775639756121)
                    ·
                      refine ⟨4144588371162581729817091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526117828216775639756121 4144588371162581729817091)
                      ·
                        rfl

theorem cell23_8071557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_8071557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071557 prefixEnd_8071557 := by exact prefixLift 8071557
  have htrace : WordTrace (prefixWord ++ tailWord_8071557) baseStart_8071557 baseEnd_8071557 := by
    simpa [prefixWord, tailWord_8071557, baseEnd_8071557] using wordTrace_append hprefix tailTrace_8071557
  have hstable : (prefixWord ++ tailWord_8071557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071557).length < 2 ^ (prefixWord ++ tailWord_8071557).sum := by decide
  have hdescent : baseEnd_8071557 < baseStart_8071557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071564 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_8071564 : Nat := 118140960795 + 8071564 * 2 ^ 59
def prefixEnd_8071564 : Nat := 4983230072969 + 3 ^ 40 * 8071564 * 2
def baseEnd_8071564 : Nat := 4144591965527163202429559

theorem tailTrace_8071564 : CollatzResearch.WordTrace tailWord_8071564 prefixEnd_8071564 4144591965527163202429559 := by
  unfold tailWord_8071564
  simp only [CollatzResearch.WordTrace]
  refine ⟨147197062265054808113626873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196262749686739744151502497 147197062265054808113626873)
  ·
    refine ⟨110397796698791106085220155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147197062265054808113626873 110397796698791106085220155)
    ·
      refine ⟨165596695048186659127830233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110397796698791106085220155 165596695048186659127830233)
      ·
        refine ⟨124197521286139994345872675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165596695048186659127830233 124197521286139994345872675)
        ·
          refine ⟨186296281929209991518809013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124197521286139994345872675 186296281929209991518809013)
          ·
            refine ⟨17465276430863436704888345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186296281929209991518809013 17465276430863436704888345)
            ·
              refine ⟨13098957323147577528666259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17465276430863436704888345 13098957323147577528666259)
              ·
                refine ⟨19648435984721366292999389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13098957323147577528666259 19648435984721366292999389)
                ·
                  refine ⟨7368163494270512359874771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19648435984721366292999389 7368163494270512359874771)
                  ·
                    refine ⟨11052245241405768539812157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7368163494270512359874771 11052245241405768539812157)
                    ·
                      refine ⟨4144591965527163202429559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11052245241405768539812157 4144591965527163202429559)
                      ·
                        rfl

theorem cell23_8071564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_8071564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071564 prefixEnd_8071564 := by exact prefixLift 8071564
  have htrace : WordTrace (prefixWord ++ tailWord_8071564) baseStart_8071564 baseEnd_8071564 := by
    simpa [prefixWord, tailWord_8071564, baseEnd_8071564] using wordTrace_append hprefix tailTrace_8071564
  have hstable : (prefixWord ++ tailWord_8071564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071564).length < 2 ^ (prefixWord ++ tailWord_8071564).sum := by decide
  have hdescent : baseEnd_8071564 < baseStart_8071564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071587 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4]
def baseStart_8071587 : Nat := 118140960795 + 8071587 * 2 ^ 59
def prefixEnd_8071587 : Nat := 4983230072969 + 3 ^ 40 * 8071587 * 2
def baseEnd_8071587 : Nat := 4144603775582216612441953

theorem tailTrace_8071587 : CollatzResearch.WordTrace tailWord_8071587 prefixEnd_8071587 4144603775582216612441953 := by
  unfold tailWord_8071587
  simp only [CollatzResearch.WordTrace]
  refine ⟨294394963409026291155341015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196263308939350860770227343 294394963409026291155341015)
  ·
    refine ⟨441592445113539436733011523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294394963409026291155341015 441592445113539436733011523)
    ·
      refine ⟨662388667670309155099517285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441592445113539436733011523 662388667670309155099517285)
      ·
        refine ⟨124197875188182966581159491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 662388667670309155099517285 124197875188182966581159491)
        ·
          refine ⟨186296812782274449871739237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124197875188182966581159491 186296812782274449871739237)
          ·
            refine ⟨34930652396676459350951107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186296812782274449871739237 34930652396676459350951107)
            ·
              refine ⟨52395978595014689026426661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34930652396676459350951107 52395978595014689026426661)
              ·
                refine ⟨9824245986565254192454999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52395978595014689026426661 9824245986565254192454999)
                ·
                  refine ⟨14736368979847881288682499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9824245986565254192454999 14736368979847881288682499)
                  ·
                    refine ⟨22104553469771821933023749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14736368979847881288682499 22104553469771821933023749)
                    ·
                      refine ⟨4144603775582216612441953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22104553469771821933023749 4144603775582216612441953)
                      ·
                        rfl

theorem cell23_8071587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_8071587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071587 prefixEnd_8071587 := by exact prefixLift 8071587
  have htrace : WordTrace (prefixWord ++ tailWord_8071587) baseStart_8071587 baseEnd_8071587 := by
    simpa [prefixWord, tailWord_8071587, baseEnd_8071587] using wordTrace_append hprefix tailTrace_8071587
  have hstable : (prefixWord ++ tailWord_8071587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071587).length < 2 ^ (prefixWord ++ tailWord_8071587).sum := by decide
  have hdescent : baseEnd_8071587 < baseStart_8071587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071607 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_8071607 : Nat := 118140960795 + 8071607 * 2 ^ 59
def prefixEnd_8071607 : Nat := 4983230072969 + 3 ^ 40 * 8071607 * 2
def baseEnd_8071607 : Nat := 4144614045195306534191861

theorem tailTrace_8071607 : CollatzResearch.WordTrace tailWord_8071607 prefixEnd_8071607 4144614045195306534191861 := by
  unfold tailWord_8071607
  simp only [CollatzResearch.WordTrace]
  refine ⟨294395692868953834571069075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196263795245969223047379383 294395692868953834571069075)
  ·
    refine ⟨441593539303430751856603613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294395692868953834571069075 441593539303430751856603613)
    ·
      refine ⟨165597577238786531946226355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441593539303430751856603613 165597577238786531946226355)
      ·
        refine ⟨248396365858179797919339533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165597577238786531946226355 248396365858179797919339533)
        ·
          refine ⟨93148637196817424219752325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248396365858179797919339533 93148637196817424219752325)
          ·
            refine ⟨17465369474403267041203561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93148637196817424219752325 17465369474403267041203561)
            ·
              refine ⟨13099027105802450280902671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17465369474403267041203561 13099027105802450280902671)
              ·
                refine ⟨19648540658703675421354007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13099027105802450280902671 19648540658703675421354007)
                ·
                  refine ⟨29472810988055513132031011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19648540658703675421354007 29472810988055513132031011)
                  ·
                    refine ⟨44209216482083269698046517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29472810988055513132031011 44209216482083269698046517)
                    ·
                      refine ⟨4144614045195306534191861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44209216482083269698046517 4144614045195306534191861)
                      ·
                        rfl

theorem cell23_8071607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_8071607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071607 prefixEnd_8071607 := by exact prefixLift 8071607
  have htrace : WordTrace (prefixWord ++ tailWord_8071607) baseStart_8071607 baseEnd_8071607 := by
    simpa [prefixWord, tailWord_8071607, baseEnd_8071607] using wordTrace_append hprefix tailTrace_8071607
  have hstable : (prefixWord ++ tailWord_8071607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071607).length < 2 ^ (prefixWord ++ tailWord_8071607).sum := by decide
  have hdescent : baseEnd_8071607 < baseStart_8071607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071630 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_8071630 : Nat := 118140960795 + 8071630 * 2 ^ 59
def prefixEnd_8071630 : Nat := 4983230072969 + 3 ^ 40 * 8071630 * 2
def baseEnd_8071630 : Nat := 4144625855250359944204255

theorem tailTrace_8071630 : CollatzResearch.WordTrace tailWord_8071630 prefixEnd_8071630 4144625855250359944204255 := by
  unfold tailWord_8071630
  simp only [CollatzResearch.WordTrace]
  refine ⟨36799566468483813687394543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196264354498580339666104229 36799566468483813687394543)
  ·
    refine ⟨55199349702725720531091815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36799566468483813687394543 55199349702725720531091815)
    ·
      refine ⟨82799024554088580796637723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55199349702725720531091815 82799024554088580796637723)
      ·
        refine ⟨124198536831132871194956585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82799024554088580796637723 124198536831132871194956585)
        ·
          refine ⟨93148902623349653396217439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124198536831132871194956585 93148902623349653396217439)
          ·
            refine ⟨139723353935024480094326159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93148902623349653396217439 139723353935024480094326159)
            ·
              refine ⟨209585030902536720141489239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139723353935024480094326159 209585030902536720141489239)
              ·
                refine ⟨314377546353805080212233859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209585030902536720141489239 314377546353805080212233859)
                ·
                  refine ⟨471566319530707620318350789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314377546353805080212233859 471566319530707620318350789)
                  ·
                    refine ⟨88418684912007678809690773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471566319530707620318350789 88418684912007678809690773)
                    ·
                      refine ⟨4144625855250359944204255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88418684912007678809690773 4144625855250359944204255)
                      ·
                        rfl

theorem cell23_8071630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_8071630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071630 prefixEnd_8071630 := by exact prefixLift 8071630
  have htrace : WordTrace (prefixWord ++ tailWord_8071630) baseStart_8071630 baseEnd_8071630 := by
    simpa [prefixWord, tailWord_8071630, baseEnd_8071630] using wordTrace_append hprefix tailTrace_8071630
  have hstable : (prefixWord ++ tailWord_8071630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071630).length < 2 ^ (prefixWord ++ tailWord_8071630).sum := by decide
  have hdescent : baseEnd_8071630 < baseStart_8071630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071734 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_8071734 : Nat := 118140960795 + 8071734 * 2 ^ 59
def prefixEnd_8071734 : Nat := 4983230072969 + 3 ^ 40 * 8071734 * 2
def baseEnd_8071734 : Nat := 460519917470936393033753

theorem tailTrace_8071734 : CollatzResearch.WordTrace tailWord_8071734 prefixEnd_8071734 460519917470936393033753 := by
  unfold tailWord_8071734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400020308718358453808891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196266883292995823507294837 18400020308718358453808891)
  ·
    refine ⟨27600030463077537680713337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18400020308718358453808891 27600030463077537680713337)
    ·
      refine ⟨20700022847308153260535003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27600030463077537680713337 20700022847308153260535003)
      ·
        refine ⟨31050034270962229890802505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20700022847308153260535003 31050034270962229890802505)
        ·
          refine ⟨23287525703221672418101879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31050034270962229890802505 23287525703221672418101879)
          ·
            refine ⟨34931288554832508627152819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23287525703221672418101879 34931288554832508627152819)
            ·
              refine ⟨52396932832248762940729229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34931288554832508627152819 52396932832248762940729229)
              ·
                refine ⟨19648849812093286102773461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52396932832248762940729229 19648849812093286102773461)
                ·
                  refine ⟨460519917470936393033753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19648849812093286102773461 460519917470936393033753)
                  ·
                    rfl

theorem cell23_8071734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_8071734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071734 prefixEnd_8071734 := by exact prefixLift 8071734
  have htrace : WordTrace (prefixWord ++ tailWord_8071734) baseStart_8071734 baseEnd_8071734 := by
    simpa [prefixWord, tailWord_8071734, baseEnd_8071734] using wordTrace_append hprefix tailTrace_8071734
  have hstable : (prefixWord ++ tailWord_8071734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071734).length < 2 ^ (prefixWord ++ tailWord_8071734).sum := by decide
  have hdescent : baseEnd_8071734 < baseStart_8071734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071745 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_8071745 : Nat := 118140960795 + 8071745 * 2 ^ 59
def prefixEnd_8071745 : Nat := 4983230072969 + 3 ^ 40 * 8071745 * 2
def baseEnd_8071745 : Nat := 4144684905525626994266227

theorem tailTrace_8071745 : CollatzResearch.WordTrace tailWord_8071745 prefixEnd_8071745 4144684905525626994266227 := by
  unfold tailWord_8071745
  simp only [CollatzResearch.WordTrace]
  refine ⟨294400726142453884139592689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196267150761635922759728459 294400726142453884139592689)
  ·
    refine ⟨220800544606840413104694517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294400726142453884139592689 220800544606840413104694517)
    ·
      refine ⟨20700051056891288728565111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220800544606840413104694517 20700051056891288728565111)
      ·
        refine ⟨31050076585336933092847667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20700051056891288728565111 31050076585336933092847667)
        ·
          refine ⟨46575114878005399639271501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31050076585336933092847667 46575114878005399639271501)
          ·
            refine ⟨17465668079252024864726813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46575114878005399639271501 17465668079252024864726813)
            ·
              refine ⟨6549625529719509324272555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17465668079252024864726813 6549625529719509324272555)
              ·
                refine ⟨9824438294579263986408833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549625529719509324272555 9824438294579263986408833)
                ·
                  refine ⟨7368328720934447989806625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9824438294579263986408833 7368328720934447989806625)
                  ·
                    refine ⟨5526246540700835992354969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368328720934447989806625 5526246540700835992354969)
                    ·
                      refine ⟨4144684905525626994266227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526246540700835992354969 4144684905525626994266227)
                      ·
                        rfl

theorem cell23_8071745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_8071745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071745 prefixEnd_8071745 := by exact prefixLift 8071745
  have htrace : WordTrace (prefixWord ++ tailWord_8071745) baseStart_8071745 baseEnd_8071745 := by
    simpa [prefixWord, tailWord_8071745, baseEnd_8071745] using wordTrace_append hprefix tailTrace_8071745
  have hstable : (prefixWord ++ tailWord_8071745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071745).length < 2 ^ (prefixWord ++ tailWord_8071745).sum := by decide
  have hdescent : baseEnd_8071745 < baseStart_8071745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071767 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_8071767 : Nat := 118140960795 + 8071767 * 2 ^ 59
def prefixEnd_8071767 : Nat := 4983230072969 + 3 ^ 40 * 8071767 * 2
def baseEnd_8071767 : Nat := 4144696202100025908191125

theorem tailTrace_8071767 : CollatzResearch.WordTrace tailWord_8071767 prefixEnd_8071767 4144696202100025908191125 := by
  unfold tailWord_8071767
  simp only [CollatzResearch.WordTrace]
  refine ⟨294401528548374181896893555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196267685698916121264595703 294401528548374181896893555)
  ·
    refine ⟨441602292822561272845340333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294401528548374181896893555 441602292822561272845340333)
    ·
      refine ⟨165600859808460477317002625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441602292822561272845340333 165600859808460477317002625)
      ·
        refine ⟨124200644856345357987751969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165600859808460477317002625 124200644856345357987751969)
        ·
          refine ⟨93150483642259018490813977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124200644856345357987751969 93150483642259018490813977)
          ·
            refine ⟨69862862731694263868110483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93150483642259018490813977 69862862731694263868110483)
            ·
              refine ⟨104794294097541395802165725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69862862731694263868110483 104794294097541395802165725)
              ·
                refine ⟨39297860286578023425812147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104794294097541395802165725 39297860286578023425812147)
                ·
                  refine ⟨58946790429867035138718221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39297860286578023425812147 58946790429867035138718221)
                  ·
                    refine ⟨22105046411200138177019333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58946790429867035138718221 22105046411200138177019333)
                    ·
                      refine ⟨4144696202100025908191125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22105046411200138177019333 4144696202100025908191125)
                      ·
                        rfl

theorem cell23_8071767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_8071767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071767 prefixEnd_8071767 := by exact prefixLift 8071767
  have htrace : WordTrace (prefixWord ++ tailWord_8071767) baseStart_8071767 baseEnd_8071767 := by
    simpa [prefixWord, tailWord_8071767, baseEnd_8071767] using wordTrace_append hprefix tailTrace_8071767
  have hstable : (prefixWord ++ tailWord_8071767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071767).length < 2 ^ (prefixWord ++ tailWord_8071767).sum := by decide
  have hdescent : baseEnd_8071767 < baseStart_8071767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071787 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 3]
def baseStart_8071787 : Nat := 118140960795 + 8071787 * 2 ^ 59
def prefixEnd_8071787 : Nat := 4983230072969 + 3 ^ 40 * 8071787 * 2
def baseEnd_8071787 : Nat := 4144706471713115829941033

theorem tailTrace_8071787 : CollatzResearch.WordTrace tailWord_8071787 prefixEnd_8071787 4144706471713115829941033 := by
  unfold tailWord_8071787
  simp only [CollatzResearch.WordTrace]
  refine ⟨294402258008301725312621615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196268172005534483541747743 294402258008301725312621615)
  ·
    refine ⟨441603387012452587968932423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294402258008301725312621615 441603387012452587968932423)
    ·
      refine ⟨662405080518678881953398635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441603387012452587968932423 662405080518678881953398635)
      ·
        refine ⟨993607620778018322930097953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662405080518678881953398635 993607620778018322930097953)
        ·
          refine ⟨745205715583513742197573465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993607620778018322930097953 745205715583513742197573465)
          ·
            refine ⟨558904286687635306648180099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745205715583513742197573465 558904286687635306648180099)
            ·
              refine ⟨838356430031452959972270149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558904286687635306648180099 838356430031452959972270149)
              ·
                refine ⟨157191830630897429994800653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838356430031452959972270149 157191830630897429994800653)
                ·
                  refine ⟨58946936486586536248050245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157191830630897429994800653 58946936486586536248050245)
                  ·
                    refine ⟨11052550591234975546509421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58946936486586536248050245 11052550591234975546509421)
                    ·
                      refine ⟨4144706471713115829941033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11052550591234975546509421 4144706471713115829941033)
                      ·
                        rfl

theorem cell23_8071787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 3].length) (baseStart_8071787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071787 prefixEnd_8071787 := by exact prefixLift 8071787
  have htrace : WordTrace (prefixWord ++ tailWord_8071787) baseStart_8071787 baseEnd_8071787 := by
    simpa [prefixWord, tailWord_8071787, baseEnd_8071787] using wordTrace_append hprefix tailTrace_8071787
  have hstable : (prefixWord ++ tailWord_8071787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071787).length < 2 ^ (prefixWord ++ tailWord_8071787).sum := by decide
  have hdescent : baseEnd_8071787 < baseStart_8071787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071841 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 6]
def baseStart_8071841 : Nat := 118140960795 + 8071841 * 2 ^ 59
def prefixEnd_8071841 : Nat := 4983230072969 + 3 ^ 40 * 8071841 * 2
def baseEnd_8071841 : Nat := 460526022185384290962865

theorem tailTrace_8071841 : CollatzResearch.WordTrace tailWord_8071841 prefixEnd_8071841 460526022185384290962865 := by
  unfold tailWord_8071841
  simp only [CollatzResearch.WordTrace]
  refine ⟨294404227550106092535087377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196269485033404061690058251 294404227550106092535087377)
  ·
    refine ⟨220803170662579569401315533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294404227550106092535087377 220803170662579569401315533)
    ·
      refine ⟨82801188998467338525493325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220803170662579569401315533 82801188998467338525493325)
      ·
        refine ⟨31050445874425251947059997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82801188998467338525493325 31050445874425251947059997)
        ·
          refine ⟨11643917202909469480147499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31050445874425251947059997 11643917202909469480147499)
          ·
            refine ⟨17465875804364204220221249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11643917202909469480147499 17465875804364204220221249)
            ·
              refine ⟨13099406853273153165165937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17465875804364204220221249 13099406853273153165165937)
              ·
                refine ⟨9824555139954864873874453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13099406853273153165165937 9824555139954864873874453)
                ·
                  refine ⟨460526022185384290962865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9824555139954864873874453 460526022185384290962865)
                  ·
                    rfl

theorem cell23_8071841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 6].length) (baseStart_8071841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071841 prefixEnd_8071841 := by exact prefixLift 8071841
  have htrace : WordTrace (prefixWord ++ tailWord_8071841) baseStart_8071841 baseEnd_8071841 := by
    simpa [prefixWord, tailWord_8071841, baseEnd_8071841] using wordTrace_append hprefix tailTrace_8071841
  have hstable : (prefixWord ++ tailWord_8071841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071841).length < 2 ^ (prefixWord ++ tailWord_8071841).sum := by decide
  have hdescent : baseEnd_8071841 < baseStart_8071841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071877 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_8071877 : Nat := 118140960795 + 8071877 * 2 ^ 59
def prefixEnd_8071877 : Nat := 4983230072969 + 3 ^ 40 * 8071877 * 2
def baseEnd_8071877 : Nat := 4144752684972020477815619

theorem tailTrace_8071877 : CollatzResearch.WordTrace tailWord_8071877 prefixEnd_8071877 4144752684972020477815619 := by
  unfold tailWord_8071877
  simp only [CollatzResearch.WordTrace]
  refine ⟨294405540577975670683397885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196270360385317113788931923 294405540577975670683397885)
  ·
    refine ⟨110402077716740876506274207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294405540577975670683397885 110402077716740876506274207)
    ·
      refine ⟨165603116575111314759411311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110402077716740876506274207 165603116575111314759411311)
      ·
        refine ⟨248404674862666972139116967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165603116575111314759411311 248404674862666972139116967)
        ·
          refine ⟨372607012294000458208675451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248404674862666972139116967 372607012294000458208675451)
          ·
            refine ⟨558910518441000687313013177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372607012294000458208675451 558910518441000687313013177)
            ·
              refine ⟨419182888830750515484759883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558910518441000687313013177 419182888830750515484759883)
              ·
                refine ⟨628774333246125773227139825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419182888830750515484759883 628774333246125773227139825)
                ·
                  refine ⟨471580749934594329920354869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628774333246125773227139825 471580749934594329920354869)
                  ·
                    refine ⟨44210695306368218430033269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 471580749934594329920354869 44210695306368218430033269)
                    ·
                      refine ⟨4144752684972020477815619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44210695306368218430033269 4144752684972020477815619)
                      ·
                        rfl

theorem cell23_8071877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_8071877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071877 prefixEnd_8071877 := by exact prefixLift 8071877
  have htrace : WordTrace (prefixWord ++ tailWord_8071877) baseStart_8071877 baseEnd_8071877 := by
    simpa [prefixWord, tailWord_8071877, baseEnd_8071877] using wordTrace_append hprefix tailTrace_8071877
  have hstable : (prefixWord ++ tailWord_8071877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071877).length < 2 ^ (prefixWord ++ tailWord_8071877).sum := by decide
  have hdescent : baseEnd_8071877 < baseStart_8071877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071887 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_8071887 : Nat := 118140960795 + 8071887 * 2 ^ 59
def prefixEnd_8071887 : Nat := 4983230072969 + 3 ^ 40 * 8071887 * 2
def baseEnd_8071887 : Nat := 4144757819778565438690573

theorem tailTrace_8071887 : CollatzResearch.WordTrace tailWord_8071887 prefixEnd_8071887 4144757819778565438690573 := by
  unfold tailWord_8071887
  simp only [CollatzResearch.WordTrace]
  refine ⟨294405905307939442391261915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196270603538626294927507943 294405905307939442391261915)
  ·
    refine ⟨441608857961909163586892873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294405905307939442391261915 441608857961909163586892873)
    ·
      refine ⟨331206643471431872690169655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441608857961909163586892873 331206643471431872690169655)
      ·
        refine ⟨496809965207147809035254483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331206643471431872690169655 496809965207147809035254483)
        ·
          refine ⟨745214947810721713552881725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496809965207147809035254483 745214947810721713552881725)
          ·
            refine ⟨279455605429020642582330647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745214947810721713552881725 279455605429020642582330647)
            ·
              refine ⟨419183408143530963873495971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279455605429020642582330647 419183408143530963873495971)
              ·
                refine ⟨628775112215296445810243957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419183408143530963873495971 628775112215296445810243957)
                ·
                  refine ⟨58947666770184041794710371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 628775112215296445810243957 58947666770184041794710371)
                  ·
                    refine ⟨88421500155276062692065557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58947666770184041794710371 88421500155276062692065557)
                    ·
                      refine ⟨4144757819778565438690573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88421500155276062692065557 4144757819778565438690573)
                      ·
                        rfl

theorem cell23_8071887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_8071887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071887 prefixEnd_8071887 := by exact prefixLift 8071887
  have htrace : WordTrace (prefixWord ++ tailWord_8071887) baseStart_8071887 baseEnd_8071887 := by
    simpa [prefixWord, tailWord_8071887, baseEnd_8071887] using wordTrace_append hprefix tailTrace_8071887
  have hstable : (prefixWord ++ tailWord_8071887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071887).length < 2 ^ (prefixWord ++ tailWord_8071887).sum := by decide
  have hdescent : baseEnd_8071887 < baseStart_8071887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071897 : List Nat := [1, 2, 1, 2, 3, 2, 12]
def baseStart_8071897 : Nat := 118140960795 + 8071897 * 2 ^ 59
def prefixEnd_8071897 : Nat := 4983230072969 + 3 ^ 40 * 8071897 * 2
def baseEnd_8071897 : Nat := 51169913019569264192167

theorem tailTrace_8071897 : CollatzResearch.WordTrace tailWord_8071897 prefixEnd_8071897 51169913019569264192167 := by
  unfold tailWord_8071897
  simp only [CollatzResearch.WordTrace]
  refine ⟨294406270037903214099125945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196270846691935476066083963 294406270037903214099125945)
  ·
    refine ⟨220804702528427410574344459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294406270037903214099125945 220804702528427410574344459)
    ·
      refine ⟨331207053792641115861516689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220804702528427410574344459 331207053792641115861516689)
      ·
        refine ⟨248405290344480836896137517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331207053792641115861516689 248405290344480836896137517)
        ·
          refine ⟨93151983879180313836051569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248405290344480836896137517 93151983879180313836051569)
          ·
            refine ⟨69863987909385235377038677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93151983879180313836051569 69863987909385235377038677)
            ·
              refine ⟨51169913019569264192167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 69863987909385235377038677 51169913019569264192167)
              ·
                rfl

theorem cell23_8071897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 12].length) (baseStart_8071897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071897 prefixEnd_8071897 := by exact prefixLift 8071897
  have htrace : WordTrace (prefixWord ++ tailWord_8071897) baseStart_8071897 baseEnd_8071897 := by
    simpa [prefixWord, tailWord_8071897, baseEnd_8071897] using wordTrace_append hprefix tailTrace_8071897
  have hstable : (prefixWord ++ tailWord_8071897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071897).length < 2 ^ (prefixWord ++ tailWord_8071897).sum := by decide
  have hdescent : baseEnd_8071897 < baseStart_8071897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071908 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_8071908 : Nat := 118140960795 + 8071908 * 2 ^ 59
def prefixEnd_8071908 : Nat := 4983230072969 + 3 ^ 40 * 8071908 * 2
def baseEnd_8071908 : Nat := 4144768602872309856527977

theorem tailTrace_8071908 : CollatzResearch.WordTrace tailWord_8071908 prefixEnd_8071908 4144768602872309856527977 := by
  unfold tailWord_8071908
  simp only [CollatzResearch.WordTrace]
  refine ⟨147203335620431681488888189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196271114160575575318517585 147203335620431681488888189)
  ·
    refine ⟨55201250857661880558333071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147203335620431681488888189 55201250857661880558333071)
    ·
      refine ⟨82801876286492820837499607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55201250857661880558333071 82801876286492820837499607)
      ·
        refine ⟨124202814429739231256249411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82801876286492820837499607 124202814429739231256249411)
        ·
          refine ⟨186304221644608846884374117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124202814429739231256249411 186304221644608846884374117)
          ·
            refine ⟨34932041558364158790820147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186304221644608846884374117 34932041558364158790820147)
            ·
              refine ⟨52398062337546238186230221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34932041558364158790820147 52398062337546238186230221)
              ·
                refine ⟨19649273376579839319836333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52398062337546238186230221 19649273376579839319836333)
                ·
                  refine ⟨7368477516217439744938625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19649273376579839319836333 7368477516217439744938625)
                  ·
                    refine ⟨5526358137163079808703969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368477516217439744938625 5526358137163079808703969)
                    ·
                      refine ⟨4144768602872309856527977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526358137163079808703969 4144768602872309856527977)
                      ·
                        rfl

theorem cell23_8071908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_8071908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071908 prefixEnd_8071908 := by exact prefixLift 8071908
  have htrace : WordTrace (prefixWord ++ tailWord_8071908) baseStart_8071908 baseEnd_8071908 := by
    simpa [prefixWord, tailWord_8071908, baseEnd_8071908] using wordTrace_append hprefix tailTrace_8071908
  have hstable : (prefixWord ++ tailWord_8071908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071908).length < 2 ^ (prefixWord ++ tailWord_8071908).sum := by decide
  have hdescent : baseEnd_8071908 < baseStart_8071908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8071959 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 1, 2, 2]
def baseStart_8071959 : Nat := 118140960795 + 8071959 * 2 ^ 59
def prefixEnd_8071959 : Nat := 4983230072969 + 3 ^ 40 * 8071959 * 2
def baseEnd_8071959 : Nat := 4144794790385689156990243

theorem tailTrace_8071959 : CollatzResearch.WordTrace tailWord_8071959 prefixEnd_8071959 4144794790385689156990243 := by
  unfold tailWord_8071959
  simp only [CollatzResearch.WordTrace]
  refine ⟨294408531363678598687882931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196272354242452399125255287 294408531363678598687882931)
  ·
    refine ⟨441612797045517898031824397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294408531363678598687882931 441612797045517898031824397)
    ·
      refine ⟨165604798892069211761934149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441612797045517898031824397 165604798892069211761934149)
      ·
        refine ⟨31050899792262977205362653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165604798892069211761934149 31050899792262977205362653)
        ·
          refine ⟨11644087422098616452010995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31050899792262977205362653 11644087422098616452010995)
          ·
            refine ⟨17466131133147924678016493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11644087422098616452010995 17466131133147924678016493)
            ·
              refine ⟨6549799174930471754256185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17466131133147924678016493 6549799174930471754256185)
              ·
                refine ⟨4912349381197853815692139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6549799174930471754256185 4912349381197853815692139)
                ·
                  refine ⟨7368524071796780723538209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912349381197853815692139 7368524071796780723538209)
                  ·
                    refine ⟨5526393053847585542653657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368524071796780723538209 5526393053847585542653657)
                    ·
                      refine ⟨4144794790385689156990243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526393053847585542653657 4144794790385689156990243)
                      ·
                        rfl

theorem cell23_8071959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_8071959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8071959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8071959 prefixEnd_8071959 := by exact prefixLift 8071959
  have htrace : WordTrace (prefixWord ++ tailWord_8071959) baseStart_8071959 baseEnd_8071959 := by
    simpa [prefixWord, tailWord_8071959, baseEnd_8071959] using wordTrace_append hprefix tailTrace_8071959
  have hstable : (prefixWord ++ tailWord_8071959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8071959).length < 2 ^ (prefixWord ++ tailWord_8071959).sum := by decide
  have hdescent : baseEnd_8071959 < baseStart_8071959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8071959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072014 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_8072014 : Nat := 118140960795 + 8072014 * 2 ^ 59
def prefixEnd_8072014 : Nat := 4983230072969 + 3 ^ 40 * 8072014 * 2
def baseEnd_8072014 : Nat := 4144823031821686441802489

theorem tailTrace_8072014 : CollatzResearch.WordTrace tailWord_8072014 prefixEnd_8072014 4144823031821686441802489 := by
  unfold tailWord_8072014
  simp only [CollatzResearch.WordTrace]
  refine ⟨36801317172309917885141887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196273691585652895387423397 36801317172309917885141887)
  ·
    refine ⟨55201975758464876827712831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36801317172309917885141887 55201975758464876827712831)
    ·
      refine ⟨82802963637697315241569247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55201975758464876827712831 82802963637697315241569247)
      ·
        refine ⟨124204445456545972862353871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82802963637697315241569247 124204445456545972862353871)
        ·
          refine ⟨186306668184818959293530807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124204445456545972862353871 186306668184818959293530807)
          ·
            refine ⟨279460002277228438940296211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186306668184818959293530807 279460002277228438940296211)
            ·
              refine ⟨419190003415842658410444317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279460002277228438940296211 419190003415842658410444317)
              ·
                refine ⟨157196251280940996903916619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419190003415842658410444317 157196251280940996903916619)
                ·
                  refine ⟨235794376921411495355874929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157196251280940996903916619 235794376921411495355874929)
                  ·
                    refine ⟨176845782691058621516906197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235794376921411495355874929 176845782691058621516906197)
                    ·
                      refine ⟨4144823031821686441802489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176845782691058621516906197 4144823031821686441802489)
                      ·
                        rfl

theorem cell23_8072014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_8072014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072014 prefixEnd_8072014 := by exact prefixLift 8072014
  have htrace : WordTrace (prefixWord ++ tailWord_8072014) baseStart_8072014 baseEnd_8072014 := by
    simpa [prefixWord, tailWord_8072014, baseEnd_8072014] using wordTrace_append hprefix tailTrace_8072014
  have hstable : (prefixWord ++ tailWord_8072014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072014).length < 2 ^ (prefixWord ++ tailWord_8072014).sum := by decide
  have hdescent : baseEnd_8072014 < baseStart_8072014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072028 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_8072028 : Nat := 118140960795 + 8072028 * 2 ^ 59
def prefixEnd_8072028 : Nat := 4983230072969 + 3 ^ 40 * 8072028 * 2
def baseEnd_8072028 : Nat := 4144830220550849387027425

theorem tailTrace_8072028 : CollatzResearch.WordTrace tailWord_8072028 prefixEnd_8072028 4144830220550849387027425 := by
  unfold tailWord_8072028
  simp only [CollatzResearch.WordTrace]
  refine ⟨147205524000214311736072369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196274032000285748981429825 147205524000214311736072369)
  ·
    refine ⟨110404143000160733802054277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147205524000214311736072369 110404143000160733802054277)
    ·
      refine ⟨20700776812530137587885177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110404143000160733802054277 20700776812530137587885177)
      ·
        refine ⟨15525582609397603190913883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20700776812530137587885177 15525582609397603190913883)
        ·
          refine ⟨23288373914096404786370825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525582609397603190913883 23288373914096404786370825)
          ·
            refine ⟨17466280435572303589778119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23288373914096404786370825 17466280435572303589778119)
            ·
              refine ⟨26199420653358455384667179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17466280435572303589778119 26199420653358455384667179)
              ·
                refine ⟨39299130980037683077000769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26199420653358455384667179 39299130980037683077000769)
                ·
                  refine ⟨29474348235028262307750577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39299130980037683077000769 29474348235028262307750577)
                  ·
                    refine ⟨22105761176271196730812933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29474348235028262307750577 22105761176271196730812933)
                    ·
                      refine ⟨4144830220550849387027425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22105761176271196730812933 4144830220550849387027425)
                      ·
                        rfl

theorem cell23_8072028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_8072028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072028 prefixEnd_8072028 := by exact prefixLift 8072028
  have htrace : WordTrace (prefixWord ++ tailWord_8072028) baseStart_8072028 baseEnd_8072028 := by
    simpa [prefixWord, tailWord_8072028, baseEnd_8072028] using wordTrace_append hprefix tailTrace_8072028
  have hstable : (prefixWord ++ tailWord_8072028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072028).length < 2 ^ (prefixWord ++ tailWord_8072028).sum := by decide
  have hdescent : baseEnd_8072028 < baseStart_8072028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072031 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_8072031 : Nat := 118140960795 + 8072031 * 2 ^ 59
def prefixEnd_8072031 : Nat := 4983230072969 + 3 ^ 40 * 8072031 * 2
def baseEnd_8072031 : Nat := 4144831760992812875289911

theorem tailTrace_8072031 : CollatzResearch.WordTrace tailWord_8072031 prefixEnd_8072031 4144831760992812875289911 := by
  unfold tailWord_8072031
  simp only [CollatzResearch.WordTrace]
  refine ⟨294411157419417754984503947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196274104946278503323002631 294411157419417754984503947)
  ·
    refine ⟨441616736129126632476755921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294411157419417754984503947 441616736129126632476755921)
    ·
      refine ⟨331212552096844974357566941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441616736129126632476755921 331212552096844974357566941)
      ·
        refine ⟨124204707036316865384087603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331212552096844974357566941 124204707036316865384087603)
        ·
          refine ⟨186307060554475298076131405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124204707036316865384087603 186307060554475298076131405)
          ·
            refine ⟨69865147707928236778549277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186307060554475298076131405 69865147707928236778549277)
            ·
              refine ⟨26199430390473088791955979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69865147707928236778549277 26199430390473088791955979)
              ·
                refine ⟨39299145585709633187933969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26199430390473088791955979 39299145585709633187933969)
                ·
                  refine ⟨29474359189282224890950477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39299145585709633187933969 29474359189282224890950477)
                  ·
                    refine ⟨11052884695980834334106429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29474359189282224890950477 11052884695980834334106429)
                    ·
                      refine ⟨4144831760992812875289911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11052884695980834334106429 4144831760992812875289911)
                      ·
                        rfl

theorem cell23_8072031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_8072031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072031 prefixEnd_8072031 := by exact prefixLift 8072031
  have htrace : WordTrace (prefixWord ++ tailWord_8072031) baseStart_8072031 baseEnd_8072031 := by
    simpa [prefixWord, tailWord_8072031, baseEnd_8072031] using wordTrace_append hprefix tailTrace_8072031
  have hstable : (prefixWord ++ tailWord_8072031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072031).length < 2 ^ (prefixWord ++ tailWord_8072031).sum := by decide
  have hdescent : baseEnd_8072031 < baseStart_8072031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072051 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 2, 5]
def baseStart_8072051 : Nat := 118140960795 + 8072051 * 2 ^ 59
def prefixEnd_8072051 : Nat := 4983230072969 + 3 ^ 40 * 8072051 * 2
def baseEnd_8072051 : Nat := 1381614010201967599013273

theorem tailTrace_8072051 : CollatzResearch.WordTrace tailWord_8072051 prefixEnd_8072051 1381614010201967599013273 := by
  unfold tailWord_8072051
  simp only [CollatzResearch.WordTrace]
  refine ⟨294411886879345298400232007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196274591252896865600154671 294411886879345298400232007)
  ·
    refine ⟨441617830319017947600348011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294411886879345298400232007 441617830319017947600348011)
    ·
      refine ⟨662426745478526921400522017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441617830319017947600348011 662426745478526921400522017)
      ·
        refine ⟨496820059108895191050391513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662426745478526921400522017 496820059108895191050391513)
        ·
          refine ⟨372615044331671393287793635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496820059108895191050391513 372615044331671393287793635)
          ·
            refine ⟨558922566497507089931690453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372615044331671393287793635 558922566497507089931690453)
            ·
              refine ⟨13099747652285322420273995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 558922566497507089931690453 13099747652285322420273995)
              ·
                refine ⟨19649621478427983630410993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13099747652285322420273995 19649621478427983630410993)
                ·
                  refine ⟨14737216108820987722808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19649621478427983630410993 14737216108820987722808245)
                  ·
                    refine ⟨1381614010201967599013273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14737216108820987722808245 1381614010201967599013273)
                    ·
                      rfl

theorem cell23_8072051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 5].length) (baseStart_8072051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072051 prefixEnd_8072051 := by exact prefixLift 8072051
  have htrace : WordTrace (prefixWord ++ tailWord_8072051) baseStart_8072051 baseEnd_8072051 := by
    simpa [prefixWord, tailWord_8072051, baseEnd_8072051] using wordTrace_append hprefix tailTrace_8072051
  have hstable : (prefixWord ++ tailWord_8072051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072051).length < 2 ^ (prefixWord ++ tailWord_8072051).sum := by decide
  have hdescent : baseEnd_8072051 < baseStart_8072051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072125 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_8072125 : Nat := 118140960795 + 8072125 * 2 ^ 59
def prefixEnd_8072125 : Nat := 4983230072969 + 3 ^ 40 * 8072125 * 2
def baseEnd_8072125 : Nat := 4144880028174335507514479

theorem tailTrace_8072125 : CollatzResearch.WordTrace tailWord_8072125 prefixEnd_8072125 4144880028174335507514479 := by
  unfold tailWord_8072125
  simp only [CollatzResearch.WordTrace]
  refine ⟨294414585881077209038425829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196276390587384806025617219 294414585881077209038425829)
  ·
    refine ⟨55202734852701976694704843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294414585881077209038425829 55202734852701976694704843)
    ·
      refine ⟨82804102279052965042057265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55202734852701976694704843 82804102279052965042057265)
      ·
        refine ⟨62103076709289723781542949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82804102279052965042057265 62103076709289723781542949)
        ·
          refine ⟨11644326882991823209039303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62103076709289723781542949 11644326882991823209039303)
          ·
            refine ⟨17466490324487734813558955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11644326882991823209039303 17466490324487734813558955)
            ·
              refine ⟨26199735486731602220338433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17466490324487734813558955 26199735486731602220338433)
              ·
                refine ⟨19649801615048701665253825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26199735486731602220338433 19649801615048701665253825)
                ·
                  refine ⟨14737351211286526248940369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19649801615048701665253825 14737351211286526248940369)
                  ·
                    refine ⟨11053013408464894686705277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14737351211286526248940369 11053013408464894686705277)
                    ·
                      refine ⟨4144880028174335507514479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11053013408464894686705277 4144880028174335507514479)
                      ·
                        rfl

theorem cell23_8072125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_8072125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072125 prefixEnd_8072125 := by exact prefixLift 8072125
  have htrace : WordTrace (prefixWord ++ tailWord_8072125) baseStart_8072125 baseEnd_8072125 := by
    simpa [prefixWord, tailWord_8072125, baseEnd_8072125] using wordTrace_append hprefix tailTrace_8072125
  have hstable : (prefixWord ++ tailWord_8072125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072125).length < 2 ^ (prefixWord ++ tailWord_8072125).sum := by decide
  have hdescent : baseEnd_8072125 < baseStart_8072125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072175 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 1, 5]
def baseStart_8072175 : Nat := 118140960795 + 8072175 * 2 ^ 59
def prefixEnd_8072175 : Nat := 4983230072969 + 3 ^ 40 * 8072175 * 2
def baseEnd_8072175 : Nat := 1381635234069020103963083

theorem tailTrace_8072175 : CollatzResearch.WordTrace tailWord_8072175 prefixEnd_8072175 1381635234069020103963083 := by
  unfold tailWord_8072175
  simp only [CollatzResearch.WordTrace]
  refine ⟨294416409530896067577745979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196277606353930711718497319 294416409530896067577745979)
  ·
    refine ⟨441624614296344101366618969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294416409530896067577745979 441624614296344101366618969)
    ·
      refine ⟨331218460722258076024964227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441624614296344101366618969 331218460722258076024964227)
      ·
        refine ⟨496827691083387114037446341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331218460722258076024964227 496827691083387114037446341)
        ·
          refine ⟨93155192078135083882021189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496827691083387114037446341 93155192078135083882021189)
          ·
            refine ⟨17466598514650328227878973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93155192078135083882021189 17466598514650328227878973)
            ·
              refine ⟨6549974442993873085454615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17466598514650328227878973 6549974442993873085454615)
              ·
                refine ⟨9824961664490809628181923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549974442993873085454615 9824961664490809628181923)
                ·
                  refine ⟨14737442496736214442272885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9824961664490809628181923 14737442496736214442272885)
                  ·
                    refine ⟨1381635234069020103963083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14737442496736214442272885 1381635234069020103963083)
                    ·
                      rfl

theorem cell23_8072175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 5].length) (baseStart_8072175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072175 prefixEnd_8072175 := by exact prefixLift 8072175
  have htrace : WordTrace (prefixWord ++ tailWord_8072175) baseStart_8072175 baseEnd_8072175 := by
    simpa [prefixWord, tailWord_8072175, baseEnd_8072175] using wordTrace_append hprefix tailTrace_8072175
  have hstable : (prefixWord ++ tailWord_8072175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072175).length < 2 ^ (prefixWord ++ tailWord_8072175).sum := by decide
  have hdescent : baseEnd_8072175 < baseStart_8072175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072182 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_8072182 : Nat := 118140960795 + 8072182 * 2 ^ 59
def prefixEnd_8072182 : Nat := 4983230072969 + 3 ^ 40 * 8072182 * 2
def baseEnd_8072182 : Nat := 4144909296571641784501717

theorem tailTrace_8072182 : CollatzResearch.WordTrace tailWord_8072182 prefixEnd_8072182 4144909296571641784501717 := by
  unfold tailWord_8072182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18401041552616919235828175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196277776561247138515500533 18401041552616919235828175)
  ·
    refine ⟨27601562328925378853742263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18401041552616919235828175 27601562328925378853742263)
    ·
      refine ⟨41402343493388068280613395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27601562328925378853742263 41402343493388068280613395)
      ·
        refine ⟨62103515240082102420920093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41402343493388068280613395 62103515240082102420920093)
        ·
          refine ⟨23288818215030788407845035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62103515240082102420920093 23288818215030788407845035)
          ·
            refine ⟨34933227322546182611767553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23288818215030788407845035 34933227322546182611767553)
            ·
              refine ⟨26199920491909636958825665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34933227322546182611767553 26199920491909636958825665)
              ·
                refine ⟨19649940368932227719119249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26199920491909636958825665 19649940368932227719119249)
                ·
                  refine ⟨14737455276699170789339437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19649940368932227719119249 14737455276699170789339437)
                  ·
                    refine ⟨5526545728762189046002289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14737455276699170789339437 5526545728762189046002289)
                    ·
                      refine ⟨4144909296571641784501717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526545728762189046002289 4144909296571641784501717)
                      ·
                        rfl

theorem cell23_8072182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_8072182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072182 prefixEnd_8072182 := by exact prefixLift 8072182
  have htrace : WordTrace (prefixWord ++ tailWord_8072182) baseStart_8072182 baseEnd_8072182 := by
    simpa [prefixWord, tailWord_8072182, baseEnd_8072182] using wordTrace_append hprefix tailTrace_8072182
  have hstable : (prefixWord ++ tailWord_8072182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072182).length < 2 ^ (prefixWord ++ tailWord_8072182).sum := by decide
  have hdescent : baseEnd_8072182 < baseStart_8072182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072215 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_8072215 : Nat := 118140960795 + 8072215 * 2 ^ 59
def prefixEnd_8072215 : Nat := 4983230072969 + 3 ^ 40 * 8072215 * 2
def baseEnd_8072215 : Nat := 4144926241433240155389065

theorem tailTrace_8072215 : CollatzResearch.WordTrace tailWord_8072215 prefixEnd_8072215 4144926241433240155389065 := by
  unfold tailWord_8072215
  simp only [CollatzResearch.WordTrace]
  refine ⟨294417868450751154409202099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196278578967167436272801399 294417868450751154409202099)
  ·
    refine ⟨441626802676126731613803149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294417868450751154409202099 441626802676126731613803149)
    ·
      refine ⟨165610051003547524355176181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441626802676126731613803149 165610051003547524355176181)
      ·
        refine ⟨15525942281582580408297767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165610051003547524355176181 15525942281582580408297767)
        ·
          refine ⟨23288913422373870612446651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525942281582580408297767 23288913422373870612446651)
          ·
            refine ⟨34933370133560805918669977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23288913422373870612446651 34933370133560805918669977)
            ·
              refine ⟨26200027600170604439002483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34933370133560805918669977 26200027600170604439002483)
              ·
                refine ⟨39300041400255906658503725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26200027600170604439002483 39300041400255906658503725)
                ·
                  refine ⟨14737515525095964996938897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39300041400255906658503725 14737515525095964996938897)
                  ·
                    refine ⟨11053136643821973747704173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14737515525095964996938897 11053136643821973747704173)
                    ·
                      refine ⟨4144926241433240155389065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11053136643821973747704173 4144926241433240155389065)
                      ·
                        rfl

theorem cell23_8072215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_8072215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072215 prefixEnd_8072215 := by exact prefixLift 8072215
  have htrace : WordTrace (prefixWord ++ tailWord_8072215) baseStart_8072215 baseEnd_8072215 := by
    simpa [prefixWord, tailWord_8072215, baseEnd_8072215] using wordTrace_append hprefix tailTrace_8072215
  have hstable : (prefixWord ++ tailWord_8072215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072215).length < 2 ^ (prefixWord ++ tailWord_8072215).sum := by decide
  have hdescent : baseEnd_8072215 < baseStart_8072215 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
