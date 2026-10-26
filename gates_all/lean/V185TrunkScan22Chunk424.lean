import V185TrunkScan22Chunk423

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3778904 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_3778904 : Nat := 118140960795 + 3778904 * 2 ^ 59
def prefixEnd_3778904 : Nat := 4983230072969 + 3 ^ 40 * 3778904 * 2
def baseEnd_3778904 : Nat := 1293596066131992169614095

theorem tailTrace_3778904 : CollatzResearch.WordTrace tailWord_3778904 prefixEnd_3778904 1293596066131992169614095 := by
  unfold tailWord_3778904
  simp only [CollatzResearch.WordTrace]
  refine ⟨68913975950841834133275883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91885301267789112177701177 68913975950841834133275883)
  ·
    refine ⟨103370963926262751199913825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68913975950841834133275883 103370963926262751199913825)
    ·
      refine ⟨77528222944697063399935369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103370963926262751199913825 77528222944697063399935369)
      ·
        refine ⟨58146167208522797549951527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77528222944697063399935369 58146167208522797549951527)
        ·
          refine ⟨87219250812784196324927291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58146167208522797549951527 87219250812784196324927291)
          ·
            refine ⟨130828876219176294487390937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87219250812784196324927291 130828876219176294487390937)
            ·
              refine ⟨98121657164382220865543203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130828876219176294487390937 98121657164382220865543203)
              ·
                refine ⟨147182485746573331298314805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98121657164382220865543203 147182485746573331298314805)
                ·
                  refine ⟨13798358038741249809217013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147182485746573331298314805 13798358038741249809217013)
                  ·
                    refine ⟨1293596066131992169614095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13798358038741249809217013 1293596066131992169614095)
                    ·
                      rfl

theorem cell22_3778904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_3778904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778904 prefixEnd_3778904 := by exact prefixLift 3778904
  have htrace : WordTrace (prefixWord ++ tailWord_3778904) baseStart_3778904 baseEnd_3778904 := by
    simpa [prefixWord, tailWord_3778904, baseEnd_3778904] using wordTrace_append hprefix tailTrace_3778904
  have hstable : (prefixWord ++ tailWord_3778904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778904).length < 2 ^ (prefixWord ++ tailWord_3778904).sum := by decide
  have hdescent : baseEnd_3778904 < baseStart_3778904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778968 : List Nat := [2, 1, 2, 5, 1, 3, 1, 7]
def baseStart_3778968 : Nat := 118140960795 + 3778968 * 2 ^ 59
def prefixEnd_3778968 : Nat := 4983230072969 + 3 ^ 40 * 3778968 * 2
def baseEnd_3778968 : Nat := 143735330515546370668211

theorem tailTrace_3778968 : CollatzResearch.WordTrace tailWord_3778968 prefixEnd_3778968 143735330515546370668211 := by
  unfold tailWord_3778968
  simp only [CollatzResearch.WordTrace]
  refine ⟨68915143086725903598440779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91886857448967871464587705 68915143086725903598440779)
  ·
    refine ⟨103372714630088855397661169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68915143086725903598440779 103372714630088855397661169)
    ·
      refine ⟨77529535972566641548245877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103372714630088855397661169 77529535972566641548245877)
      ·
        refine ⟨7268393997428122645148051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77529535972566641548245877 7268393997428122645148051)
        ·
          refine ⟨10902590996142183967722077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7268393997428122645148051 10902590996142183967722077)
          ·
            refine ⟨4088471623553318987895779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10902590996142183967722077 4088471623553318987895779)
            ·
              refine ⟨6132707435329978481843669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088471623553318987895779 6132707435329978481843669)
              ·
                refine ⟨143735330515546370668211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6132707435329978481843669 143735330515546370668211)
                ·
                  rfl

theorem cell22_3778968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_3778968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778968 prefixEnd_3778968 := by exact prefixLift 3778968
  have htrace : WordTrace (prefixWord ++ tailWord_3778968) baseStart_3778968 baseEnd_3778968 := by
    simpa [prefixWord, tailWord_3778968, baseEnd_3778968] using wordTrace_append hprefix tailTrace_3778968
  have hstable : (prefixWord ++ tailWord_3778968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778968).length < 2 ^ (prefixWord ++ tailWord_3778968).sum := by decide
  have hdescent : baseEnd_3778968 < baseStart_3778968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778983 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3778983 : Nat := 118140960795 + 3778983 * 2 ^ 59
def prefixEnd_3778983 : Nat := 4983230072969 + 3 ^ 40 * 3778983 * 2
def baseEnd_3778983 : Nat := 1293623109446462296888853

theorem tailTrace_3778983 : CollatzResearch.WordTrace tailWord_3778983 prefixEnd_3778983 1293623109446462296888853 := by
  unfold tailWord_3778983
  simp only [CollatzResearch.WordTrace]
  refine ⟨137830833268397464758677603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91887222178931643172451735 137830833268397464758677603)
  ·
    refine ⟨206746249902596197138016405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137830833268397464758677603 206746249902596197138016405)
    ·
      refine ⟨9691230464184196740844519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206746249902596197138016405 9691230464184196740844519)
      ·
        refine ⟨14536845696276295111266779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9691230464184196740844519 14536845696276295111266779)
        ·
          refine ⟨21805268544414442666900169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14536845696276295111266779 21805268544414442666900169)
          ·
            refine ⟨16353951408310832000175127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21805268544414442666900169 16353951408310832000175127)
            ·
              refine ⟨24530927112466248000262691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16353951408310832000175127 24530927112466248000262691)
              ·
                refine ⟨36796390668699372000394037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24530927112466248000262691 36796390668699372000394037)
                ·
                  refine ⟨3449661625190566125036941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36796390668699372000394037 3449661625190566125036941)
                  ·
                    refine ⟨1293623109446462296888853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3449661625190566125036941 1293623109446462296888853)
                    ·
                      rfl

theorem cell22_3778983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3778983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3778983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3778983 prefixEnd_3778983 := by exact prefixLift 3778983
  have htrace : WordTrace (prefixWord ++ tailWord_3778983) baseStart_3778983 baseEnd_3778983 := by
    simpa [prefixWord, tailWord_3778983, baseEnd_3778983] using wordTrace_append hprefix tailTrace_3778983
  have hstable : (prefixWord ++ tailWord_3778983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778983).length < 2 ^ (prefixWord ++ tailWord_3778983).sum := by decide
  have hdescent : baseEnd_3778983 < baseStart_3778983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779028 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3779028 : Nat := 118140960795 + 3779028 * 2 ^ 59
def prefixEnd_3779028 : Nat := 4983230072969 + 3 ^ 40 * 3779028 * 2
def baseEnd_3779028 : Nat := 1293638513866097179513715

theorem tailTrace_3779028 : CollatzResearch.WordTrace tailWord_3779028 prefixEnd_3779028 1293638513866097179513715 := by
  unfold tailWord_3779028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68916237276617218722032869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91888316368822958296043825 68916237276617218722032869)
  ·
    refine ⟨12921794489365728510381163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68916237276617218722032869 12921794489365728510381163)
    ·
      refine ⟨19382691734048592765571745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12921794489365728510381163 19382691734048592765571745)
      ·
        refine ⟨14537018800536444574178809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19382691734048592765571745 14537018800536444574178809)
        ·
          refine ⟨10902764100402333430634107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14537018800536444574178809 10902764100402333430634107)
          ·
            refine ⟨16354146150603500145951161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902764100402333430634107 16354146150603500145951161)
            ·
              refine ⟨12265609612952625109463371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16354146150603500145951161 12265609612952625109463371)
              ·
                refine ⟨18398414419428937664195057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12265609612952625109463371 18398414419428937664195057)
                ·
                  refine ⟨13798810814571703248146293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18398414419428937664195057 13798810814571703248146293)
                  ·
                    refine ⟨1293638513866097179513715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13798810814571703248146293 1293638513866097179513715)
                    ·
                      rfl

theorem cell22_3779028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3779028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779028 prefixEnd_3779028 := by exact prefixLift 3779028
  have htrace : WordTrace (prefixWord ++ tailWord_3779028) baseStart_3779028 baseEnd_3779028 := by
    simpa [prefixWord, tailWord_3779028, baseEnd_3779028] using wordTrace_append hprefix tailTrace_3779028
  have hstable : (prefixWord ++ tailWord_3779028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779028).length < 2 ^ (prefixWord ++ tailWord_3779028).sum := by decide
  have hdescent : baseEnd_3779028 < baseStart_3779028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779041 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 6]
def baseStart_3779041 : Nat := 118140960795 + 3779041 * 2 ^ 59
def prefixEnd_3779041 : Nat := 4983230072969 + 3 ^ 40 * 3779041 * 2
def baseEnd_3779041 : Nat := 431214321343923159646225

theorem tailTrace_3779041 : CollatzResearch.WordTrace tailWord_3779041 prefixEnd_3779041 431214321343923159646225 := by
  unfold tailWord_3779041
  simp only [CollatzResearch.WordTrace]
  refine ⟨137832948702187340664288977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91888632468124893776192651 137832948702187340664288977)
  ·
    refine ⟨103374711526640505498216733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137832948702187340664288977 103374711526640505498216733)
    ·
      refine ⟨38765516822490189561831275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103374711526640505498216733 38765516822490189561831275)
      ·
        refine ⟨58148275233735284342746913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38765516822490189561831275 58148275233735284342746913)
        ·
          refine ⟨43611206425301463257060185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58148275233735284342746913 43611206425301463257060185)
          ·
            refine ⟨32708404818976097442795139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43611206425301463257060185 32708404818976097442795139)
            ·
              refine ⟨49062607228464146164192709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32708404818976097442795139 49062607228464146164192709)
              ·
                refine ⟨9199238855337027405786133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49062607228464146164192709 9199238855337027405786133)
                ·
                  refine ⟨431214321343923159646225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9199238855337027405786133 431214321343923159646225)
                  ·
                    rfl

theorem cell22_3779041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_3779041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779041 prefixEnd_3779041 := by exact prefixLift 3779041
  have htrace : WordTrace (prefixWord ++ tailWord_3779041) baseStart_3779041 baseEnd_3779041 := by
    simpa [prefixWord, tailWord_3779041, baseEnd_3779041] using wordTrace_append hprefix tailTrace_3779041
  have hstable : (prefixWord ++ tailWord_3779041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779041).length < 2 ^ (prefixWord ++ tailWord_3779041).sum := by decide
  have hdescent : baseEnd_3779041 < baseStart_3779041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779056 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_3779056 : Nat := 118140960795 + 3779056 * 2 ^ 59
def prefixEnd_3779056 : Nat := 4983230072969 + 3 ^ 40 * 3779056 * 2
def baseEnd_3779056 : Nat := 1293648098838314439813629

theorem tailTrace_3779056 : CollatzResearch.WordTrace tailWord_3779056 prefixEnd_3779056 1293648098838314439813629 := by
  unfold tailWord_3779056
  simp only [CollatzResearch.WordTrace]
  refine ⟨68916747898566499113042511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91888997198088665484056681 68916747898566499113042511)
  ·
    refine ⟨103375121847849748669563767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68916747898566499113042511 103375121847849748669563767)
    ·
      refine ⟨155062682771774623004345651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103375121847849748669563767 155062682771774623004345651)
      ·
        refine ⟨232594024157661934506518477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155062682771774623004345651 232594024157661934506518477)
        ·
          refine ⟨87222759059123225439944429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232594024157661934506518477 87222759059123225439944429)
          ·
            refine ⟨32708534647171209539979161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87222759059123225439944429 32708534647171209539979161)
            ·
              refine ⟨24531400985378407154984371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32708534647171209539979161 24531400985378407154984371)
              ·
                refine ⟨36797101478067610732476557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24531400985378407154984371 36797101478067610732476557)
                ·
                  refine ⟨13798913054275354024678709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36797101478067610732476557 13798913054275354024678709)
                  ·
                    refine ⟨1293648098838314439813629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13798913054275354024678709 1293648098838314439813629)
                    ·
                      rfl

theorem cell22_3779056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_3779056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779056 prefixEnd_3779056 := by exact prefixLift 3779056
  have htrace : WordTrace (prefixWord ++ tailWord_3779056) baseStart_3779056 baseEnd_3779056 := by
    simpa [prefixWord, tailWord_3779056, baseEnd_3779056] using wordTrace_append hprefix tailTrace_3779056
  have hstable : (prefixWord ++ tailWord_3779056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779056).length < 2 ^ (prefixWord ++ tailWord_3779056).sum := by decide
  have hdescent : baseEnd_3779056 < baseStart_3779056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779075 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 4]
def baseStart_3779075 : Nat := 118140960795 + 3779075 * 2 ^ 59
def prefixEnd_3779075 : Nat := 4983230072969 + 3 ^ 40 * 3779075 * 2
def baseEnd_3779075 : Nat := 431218200975534907862857

theorem tailTrace_3779075 : CollatzResearch.WordTrace tailWord_3779075 prefixEnd_3779075 431218200975534907862857 := by
  unfold tailWord_3779075
  simp only [CollatzResearch.WordTrace]
  refine ⟨137834188784064164471026679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91889459189376109647351119 137834188784064164471026679)
  ·
    refine ⟨206751283176096246706540019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137834188784064164471026679 206751283176096246706540019)
    ·
      refine ⟨310126924764144370059810029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206751283176096246706540019 310126924764144370059810029)
      ·
        refine ⟨116297596786554138772428761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310126924764144370059810029 116297596786554138772428761)
        ·
          refine ⟨87223197589915604079321571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116297596786554138772428761 87223197589915604079321571)
          ·
            refine ⟨130834796384873406118982357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87223197589915604079321571 130834796384873406118982357)
            ·
              refine ⟨3066440540270470455913649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130834796384873406118982357 3066440540270470455913649)
              ·
                refine ⟨2299830405202852841935237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066440540270470455913649 2299830405202852841935237)
                ·
                  refine ⟨431218200975534907862857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299830405202852841935237 431218200975534907862857)
                  ·
                    rfl

theorem cell22_3779075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 4].length) (baseStart_3779075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779075 prefixEnd_3779075 := by exact prefixLift 3779075
  have htrace : WordTrace (prefixWord ++ tailWord_3779075) baseStart_3779075 baseEnd_3779075 := by
    simpa [prefixWord, tailWord_3779075, baseEnd_3779075] using wordTrace_append hprefix tailTrace_3779075
  have hstable : (prefixWord ++ tailWord_3779075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779075).length < 2 ^ (prefixWord ++ tailWord_3779075).sum := by decide
  have hdescent : baseEnd_3779075 < baseStart_3779075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779116 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_3779116 : Nat := 118140960795 + 3779116 * 2 ^ 59
def prefixEnd_3779116 : Nat := 4983230072969 + 3 ^ 40 * 3779116 * 2
def baseEnd_3779116 : Nat := 1293668638064494283313445

theorem tailTrace_3779116 : CollatzResearch.WordTrace tailWord_3779116 prefixEnd_3779116 1293668638064494283313445 := by
  unfold tailWord_3779116
  simp only [CollatzResearch.WordTrace]
  refine ⟨68917842088457814236634601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91890456117943752315512801 68917842088457814236634601)
  ·
    refine ⟨51688381566343360677475951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68917842088457814236634601 51688381566343360677475951)
    ·
      refine ⟨77532572349515041016213927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51688381566343360677475951 77532572349515041016213927)
      ·
        refine ⟨116298858524272561524320891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77532572349515041016213927 116298858524272561524320891)
        ·
          refine ⟨174448287786408842286481337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116298858524272561524320891 174448287786408842286481337)
          ·
            refine ⟨130836215839806631714861003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174448287786408842286481337 130836215839806631714861003)
            ·
              refine ⟨196254323759709947572291505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130836215839806631714861003 196254323759709947572291505)
              ·
                refine ⟨147190742819782460679218629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196254323759709947572291505 147190742819782460679218629)
                ·
                  refine ⟨27598264278709211377353493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147190742819782460679218629 27598264278709211377353493)
                  ·
                    refine ⟨1293668638064494283313445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27598264278709211377353493 1293668638064494283313445)
                    ·
                      rfl

theorem cell22_3779116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_3779116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779116 prefixEnd_3779116 := by exact prefixLift 3779116
  have htrace : WordTrace (prefixWord ++ tailWord_3779116) baseStart_3779116 baseEnd_3779116 := by
    simpa [prefixWord, tailWord_3779116, baseEnd_3779116] using wordTrace_append hprefix tailTrace_3779116
  have hstable : (prefixWord ++ tailWord_3779116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779116).length < 2 ^ (prefixWord ++ tailWord_3779116).sum := by decide
  have hdescent : baseEnd_3779116 < baseStart_3779116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779133 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_3779133 : Nat := 118140960795 + 3779133 * 2 ^ 59
def prefixEnd_3779133 : Nat := 4983230072969 + 3 ^ 40 * 3779133 * 2
def baseEnd_3779133 : Nat := 1293674457511911905638393

theorem tailTrace_3779133 : CollatzResearch.WordTrace tailWord_3779133 prefixEnd_3779133 1293674457511911905638393 := by
  unfold tailWord_3779133
  simp only [CollatzResearch.WordTrace]
  refine ⟨137836304217854040376638053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91890869478569360251092035 137836304217854040376638053)
  ·
    refine ⟨25844307040847632570619635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137836304217854040376638053 25844307040847632570619635)
    ·
      refine ⟨38766460561271448855929453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25844307040847632570619635 38766460561271448855929453)
      ·
        refine ⟨14537422710476793320973545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38766460561271448855929453 14537422710476793320973545)
        ·
          refine ⟨10903067032857594990730159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14537422710476793320973545 10903067032857594990730159)
          ·
            refine ⟨16354600549286392486095239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10903067032857594990730159 16354600549286392486095239)
            ·
              refine ⟨24531900823929588729142859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16354600549286392486095239 24531900823929588729142859)
              ·
                refine ⟨36797851235894383093714289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24531900823929588729142859 36797851235894383093714289)
                ·
                  refine ⟨27598388426920787320285717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36797851235894383093714289 27598388426920787320285717)
                  ·
                    refine ⟨1293674457511911905638393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27598388426920787320285717 1293674457511911905638393)
                    ·
                      rfl

theorem cell22_3779133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_3779133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779133 prefixEnd_3779133 := by exact prefixLift 3779133
  have htrace : WordTrace (prefixWord ++ tailWord_3779133) baseStart_3779133 baseEnd_3779133 := by
    simpa [prefixWord, tailWord_3779133, baseEnd_3779133] using wordTrace_append hprefix tailTrace_3779133
  have hstable : (prefixWord ++ tailWord_3779133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779133).length < 2 ^ (prefixWord ++ tailWord_3779133).sum := by decide
  have hdescent : baseEnd_3779133 < baseStart_3779133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779148 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_3779148 : Nat := 118140960795 + 3779148 * 2 ^ 59
def prefixEnd_3779148 : Nat := 4983230072969 + 3 ^ 40 * 3779148 * 2
def baseEnd_3779148 : Nat := 431226530772818955504449

theorem tailTrace_3779148 : CollatzResearch.WordTrace tailWord_3779148 prefixEnd_3779148 431226530772818955504449 := by
  unfold tailWord_3779148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68918425656399848969217049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91891234208533131958956065 68918425656399848969217049)
  ·
    refine ⟨51688819242299886726912787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68918425656399848969217049 51688819242299886726912787)
    ·
      refine ⟨77533228863449830090369181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51688819242299886726912787 77533228863449830090369181)
      ·
        refine ⟨29074960823793686283888443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77533228863449830090369181 29074960823793686283888443)
        ·
          refine ⟨43612441235690529425832665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29074960823793686283888443 43612441235690529425832665)
          ·
            refine ⟨32709330926767897069374499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43612441235690529425832665 32709330926767897069374499)
            ·
              refine ⟨49063996390151845604061749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32709330926767897069374499 49063996390151845604061749)
              ·
                refine ⟨4599749661576735525380789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49063996390151845604061749 4599749661576735525380789)
                ·
                  refine ⟨431226530772818955504449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4599749661576735525380789 431226530772818955504449)
                  ·
                    rfl

theorem cell22_3779148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_3779148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779148 prefixEnd_3779148 := by exact prefixLift 3779148
  have htrace : WordTrace (prefixWord ++ tailWord_3779148) baseStart_3779148 baseEnd_3779148 := by
    simpa [prefixWord, tailWord_3779148, baseEnd_3779148] using wordTrace_append hprefix tailTrace_3779148
  have hstable : (prefixWord ++ tailWord_3779148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779148).length < 2 ^ (prefixWord ++ tailWord_3779148).sum := by decide
  have hdescent : baseEnd_3779148 < baseStart_3779148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779182 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_3779182 : Nat := 118140960795 + 3779182 * 2 ^ 59
def prefixEnd_3779182 : Nat := 4983230072969 + 3 ^ 40 * 3779182 * 2
def baseEnd_3779182 : Nat := 431230410404430703721081

theorem tailTrace_3779182 : CollatzResearch.WordTrace tailWord_3779182 prefixEnd_3779182 431230410404430703721081 := by
  unfold tailWord_3779182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17229761424334565218146475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91892060929784347830114533 17229761424334565218146475)
  ·
    refine ⟨25844642136501847827219713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17229761424334565218146475 25844642136501847827219713)
    ·
      refine ⟨19383481602376385870414785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25844642136501847827219713 19383481602376385870414785)
      ·
        refine ⟨14537611201782289402811089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19383481602376385870414785 14537611201782289402811089)
        ·
          refine ⟨10903208401336717052108317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14537611201782289402811089 10903208401336717052108317)
          ·
            refine ⟨4088703150501268894540619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10903208401336717052108317 4088703150501268894540619)
            ·
              refine ⟨6133054725751903341810929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088703150501268894540619 6133054725751903341810929)
              ·
                refine ⟨4599791044313927506358197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6133054725751903341810929 4599791044313927506358197)
                ·
                  refine ⟨431230410404430703721081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4599791044313927506358197 431230410404430703721081)
                  ·
                    rfl

theorem cell22_3779182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_3779182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779182 prefixEnd_3779182 := by exact prefixLift 3779182
  have htrace : WordTrace (prefixWord ++ tailWord_3779182) baseStart_3779182 baseEnd_3779182 := by
    simpa [prefixWord, tailWord_3779182, baseEnd_3779182] using wordTrace_append hprefix tailTrace_3779182
  have hstable : (prefixWord ++ tailWord_3779182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779182).length < 2 ^ (prefixWord ++ tailWord_3779182).sum := by decide
  have hdescent : baseEnd_3779182 < baseStart_3779182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779193 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 6]
def baseStart_3779193 : Nat := 118140960795 + 3779193 * 2 ^ 59
def prefixEnd_3779193 : Nat := 4983230072969 + 3 ^ 40 * 3779193 * 2
def baseEnd_3779193 : Nat := 431231665579363916379403

theorem tailTrace_3779193 : CollatzResearch.WordTrace tailWord_3779193 prefixEnd_3779193 431231665579363916379403 := by
  unfold tailWord_3779193
  simp only [CollatzResearch.WordTrace]
  refine ⟨137838492597636670623822233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91892328398424447082548155 137838492597636670623822233)
  ·
    refine ⟨103378869448227502967866675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137838492597636670623822233 103378869448227502967866675)
    ·
      refine ⟨155068304172341254451800013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103378869448227502967866675 155068304172341254451800013)
      ·
        refine ⟨58150614064627970419425005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155068304172341254451800013 58150614064627970419425005)
        ·
          refine ⟨21806480274235488907284377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58150614064627970419425005 21806480274235488907284377)
          ·
            refine ⟨16354860205676616680463283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21806480274235488907284377 16354860205676616680463283)
            ·
              refine ⟨24532290308514925020694925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16354860205676616680463283 24532290308514925020694925)
              ·
                refine ⟨9199608865693096882760597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24532290308514925020694925 9199608865693096882760597)
                ·
                  refine ⟨431231665579363916379403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9199608865693096882760597 431231665579363916379403)
                  ·
                    rfl

theorem cell22_3779193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_3779193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779193 prefixEnd_3779193 := by exact prefixLift 3779193
  have htrace : WordTrace (prefixWord ++ tailWord_3779193) baseStart_3779193 baseEnd_3779193 := by
    simpa [prefixWord, tailWord_3779193, baseEnd_3779193] using wordTrace_append hprefix tailTrace_3779193
  have hstable : (prefixWord ++ tailWord_3779193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779193).length < 2 ^ (prefixWord ++ tailWord_3779193).sum := by decide
  have hdescent : baseEnd_3779193 < baseStart_3779193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779223 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_3779223 : Nat := 118140960795 + 3779223 * 2 ^ 59
def prefixEnd_3779223 : Nat := 4983230072969 + 3 ^ 40 * 3779223 * 2
def baseEnd_3779223 : Nat := 1293705266351181670888117

theorem tailTrace_3779223 : CollatzResearch.WordTrace tailWord_3779223 prefixEnd_3779223 1293705266351181670888117 := by
  unfold tailWord_3779223
  simp only [CollatzResearch.WordTrace]
  refine ⟨137839586787527985747414323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91893057858351990498276215 137839586787527985747414323)
  ·
    refine ⟨206759380181291978621121485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137839586787527985747414323 206759380181291978621121485)
    ·
      refine ⟨77534767567984491982920557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206759380181291978621121485 77534767567984491982920557)
      ·
        refine ⟨29075537837994184493595209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77534767567984491982920557 29075537837994184493595209)
        ·
          refine ⟨21806653378495638370196407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29075537837994184493595209 21806653378495638370196407)
          ·
            refine ⟨32709980067743457555294611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806653378495638370196407 32709980067743457555294611)
            ·
              refine ⟨49064970101615186332941917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32709980067743457555294611 49064970101615186332941917)
              ·
                refine ⟨18399363788105694874853219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49064970101615186332941917 18399363788105694874853219)
                ·
                  refine ⟨27599045682158542312279829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18399363788105694874853219 27599045682158542312279829)
                  ·
                    refine ⟨1293705266351181670888117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27599045682158542312279829 1293705266351181670888117)
                    ·
                      rfl

theorem cell22_3779223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_3779223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779223 prefixEnd_3779223 := by exact prefixLift 3779223
  have htrace : WordTrace (prefixWord ++ tailWord_3779223) baseStart_3779223 baseEnd_3779223 := by
    simpa [prefixWord, tailWord_3779223, baseEnd_3779223] using wordTrace_append hprefix tailTrace_3779223
  have hstable : (prefixWord ++ tailWord_3779223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779223).length < 2 ^ (prefixWord ++ tailWord_3779223).sum := by decide
  have hdescent : baseEnd_3779223 < baseStart_3779223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779255 : List Nat := [1, 1, 3, 1, 6, 1, 2, 7]
def baseStart_3779255 : Nat := 118140960795 + 3779255 * 2 ^ 59
def prefixEnd_3779255 : Nat := 4983230072969 + 3 ^ 40 * 3779255 * 2
def baseEnd_3779255 : Nat := 143746246733904917120891

theorem tailTrace_3779255 : CollatzResearch.WordTrace tailWord_3779255 prefixEnd_3779255 143746246733904917120891 := by
  unfold tailWord_3779255
  simp only [CollatzResearch.WordTrace]
  refine ⟨137840753923412055212579219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91893835948941370141719479 137840753923412055212579219)
  ·
    refine ⟨206761130885118082818868829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137840753923412055212579219 206761130885118082818868829)
    ·
      refine ⟨77535424081919281057075811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206761130885118082818868829 77535424081919281057075811)
      ·
        refine ⟨116303136122878921585613717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77535424081919281057075811 116303136122878921585613717)
        ·
          refine ⟨5451709505759949449325643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116303136122878921585613717 5451709505759949449325643)
          ·
            refine ⟨8177564258639924173988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451709505759949449325643 8177564258639924173988465)
            ·
              refine ⟨6133173193979943130491349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8177564258639924173988465 6133173193979943130491349)
              ·
                refine ⟨143746246733904917120891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6133173193979943130491349 143746246733904917120891)
                ·
                  rfl

theorem cell22_3779255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 7].length) (baseStart_3779255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779255 prefixEnd_3779255 := by exact prefixLift 3779255
  have htrace : WordTrace (prefixWord ++ tailWord_3779255) baseStart_3779255 baseEnd_3779255 := by
    simpa [prefixWord, tailWord_3779255, baseEnd_3779255] using wordTrace_append hprefix tailTrace_3779255
  have hstable : (prefixWord ++ tailWord_3779255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779255).length < 2 ^ (prefixWord ++ tailWord_3779255).sum := by decide
  have hdescent : baseEnd_3779255 < baseStart_3779255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779300 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_3779300 : Nat := 118140960795 + 3779300 * 2 ^ 59
def prefixEnd_3779300 : Nat := 4983230072969 + 3 ^ 40 * 3779300 * 2
def baseEnd_3779300 : Nat := 431243875008259712237627

theorem tailTrace_3779300 : CollatzResearch.WordTrace tailWord_3779300 prefixEnd_3779300 431243875008259712237627 := by
  unfold tailWord_3779300
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921197604124513948983677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91894930138832685265311569 68921197604124513948983677)
  ·
    refine ⟨25845449101546692730868879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68921197604124513948983677 25845449101546692730868879)
    ·
      refine ⟨38768173652320039096303319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25845449101546692730868879 38768173652320039096303319)
      ·
        refine ⟨58152260478480058644454979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38768173652320039096303319 58152260478480058644454979)
        ·
          refine ⟨87228390717720087966682469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58152260478480058644454979 87228390717720087966682469)
          ·
            refine ⟨16355323259572516493752963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87228390717720087966682469 16355323259572516493752963)
            ·
              refine ⟨24532984889358774740629445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16355323259572516493752963 24532984889358774740629445)
              ·
                refine ⟨4599934666754770263868021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24532984889358774740629445 4599934666754770263868021)
                ·
                  refine ⟨431243875008259712237627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4599934666754770263868021 431243875008259712237627)
                  ·
                    rfl

theorem cell22_3779300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_3779300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779300 prefixEnd_3779300 := by exact prefixLift 3779300
  have htrace : WordTrace (prefixWord ++ tailWord_3779300) baseStart_3779300 baseEnd_3779300 := by
    simpa [prefixWord, tailWord_3779300, baseEnd_3779300] using wordTrace_append hprefix tailTrace_3779300
  have hstable : (prefixWord ++ tailWord_3779300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779300).length < 2 ^ (prefixWord ++ tailWord_3779300).sum := by decide
  have hdescent : baseEnd_3779300 < baseStart_3779300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779362 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3779362 : Nat := 118140960795 + 3779362 * 2 ^ 59
def prefixEnd_3779362 : Nat := 4983230072969 + 3 ^ 40 * 3779362 * 2
def baseEnd_3779362 : Nat := 431250949630610547220897

theorem tailTrace_3779362 : CollatzResearch.WordTrace tailWord_3779362 prefixEnd_3779362 431250949630610547220897 := by
  unfold tailWord_3779362
  simp only [CollatzResearch.WordTrace]
  refine ⟨34461164133506103121681085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91896437689349608324482893 34461164133506103121681085)
  ·
    refine ⟨12922936550064788670630407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34461164133506103121681085 12922936550064788670630407)
    ·
      refine ⟨19384404825097183005945611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12922936550064788670630407 19384404825097183005945611)
      ·
        refine ⟨29076607237645774508918417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19384404825097183005945611 29076607237645774508918417)
        ·
          refine ⟨21807455428234330881688813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29076607237645774508918417 21807455428234330881688813)
          ·
            refine ⟨8177795785587874080633305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21807455428234330881688813 8177795785587874080633305)
            ·
              refine ⟨6133346839190905560474979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8177795785587874080633305 6133346839190905560474979)
              ·
                refine ⟨9200020258786358340712469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6133346839190905560474979 9200020258786358340712469)
                ·
                  refine ⟨431250949630610547220897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9200020258786358340712469 431250949630610547220897)
                  ·
                    rfl

theorem cell22_3779362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3779362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779362 prefixEnd_3779362 := by exact prefixLift 3779362
  have htrace : WordTrace (prefixWord ++ tailWord_3779362) baseStart_3779362 baseEnd_3779362 := by
    simpa [prefixWord, tailWord_3779362, baseEnd_3779362] using wordTrace_append hprefix tailTrace_3779362
  have hstable : (prefixWord ++ tailWord_3779362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779362).length < 2 ^ (prefixWord ++ tailWord_3779362).sum := by decide
  have hdescent : baseEnd_3779362 < baseStart_3779362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779450 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_3779450 : Nat := 118140960795 + 3779450 * 2 ^ 59
def prefixEnd_3779450 : Nat := 4983230072969 + 3 ^ 40 * 3779450 * 2
def baseEnd_3779450 : Nat := 1293782973090228745462421

theorem tailTrace_3779450 : CollatzResearch.WordTrace tailWord_3779450 prefixEnd_3779450 1293782973090228745462421 := by
  unfold tailWord_3779450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34461966539426400878981951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91898577438470402343951869 34461966539426400878981951)
  ·
    refine ⟨51692949809139601318472927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34461966539426400878981951 51692949809139601318472927)
    ·
      refine ⟨77539424713709401977709391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51692949809139601318472927 77539424713709401977709391)
      ·
        refine ⟨116309137070564102966564087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77539424713709401977709391 116309137070564102966564087)
        ·
          refine ⟨174463705605846154449846131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116309137070564102966564087 174463705605846154449846131)
          ·
            refine ⟨261695558408769231674769197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174463705605846154449846131 261695558408769231674769197)
            ·
              refine ⟨98135834403288461878038449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261695558408769231674769197 98135834403288461878038449)
              ·
                refine ⟨73601875802466346408528837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98135834403288461878038449 73601875802466346408528837)
                ·
                  refine ⟨13800351712962439951599157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73601875802466346408528837 13800351712962439951599157)
                  ·
                    refine ⟨1293782973090228745462421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13800351712962439951599157 1293782973090228745462421)
                    ·
                      rfl

theorem cell22_3779450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_3779450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779450 prefixEnd_3779450 := by exact prefixLift 3779450
  have htrace : WordTrace (prefixWord ++ tailWord_3779450) baseStart_3779450 baseEnd_3779450 := by
    simpa [prefixWord, tailWord_3779450, baseEnd_3779450] using wordTrace_append hprefix tailTrace_3779450
  have hstable : (prefixWord ++ tailWord_3779450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779450).length < 2 ^ (prefixWord ++ tailWord_3779450).sum := by decide
  have hdescent : baseEnd_3779450 < baseStart_3779450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779484 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3779484 : Nat := 118140960795 + 3779484 * 2 ^ 59
def prefixEnd_3779484 : Nat := 4983230072969 + 3 ^ 40 * 3779484 * 2
def baseEnd_3779484 : Nat := 1293794611985063990112317

theorem tailTrace_3779484 : CollatzResearch.WordTrace tailWord_3779484 prefixEnd_3779484 1293794611985063990112317 := by
  unfold tailWord_3779484
  simp only [CollatzResearch.WordTrace]
  refine ⟨68924553119791213661332753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91899404159721618215110337 68924553119791213661332753)
  ·
    refine ⟨51693414839843410245999565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68924553119791213661332753 51693414839843410245999565)
    ·
      refine ⟨19385030564941278842249837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51693414839843410245999565 19385030564941278842249837)
      ·
        refine ⟨7269386461852979565843689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19385030564941278842249837 7269386461852979565843689)
        ·
          refine ⟨5452039846389734674382767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7269386461852979565843689 5452039846389734674382767)
          ·
            refine ⟨8178059769584602011574151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5452039846389734674382767 8178059769584602011574151)
            ·
              refine ⟨12267089654376903017361227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178059769584602011574151 12267089654376903017361227)
              ·
                refine ⟨18400634481565354526041841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12267089654376903017361227 18400634481565354526041841)
                ·
                  refine ⟨13800475861174015894531381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18400634481565354526041841 13800475861174015894531381)
                  ·
                    refine ⟨1293794611985063990112317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13800475861174015894531381 1293794611985063990112317)
                    ·
                      rfl

theorem cell22_3779484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3779484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779484 prefixEnd_3779484 := by exact prefixLift 3779484
  have htrace : WordTrace (prefixWord ++ tailWord_3779484) baseStart_3779484 baseEnd_3779484 := by
    simpa [prefixWord, tailWord_3779484, baseEnd_3779484] using wordTrace_append hprefix tailTrace_3779484
  have hstable : (prefixWord ++ tailWord_3779484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779484).length < 2 ^ (prefixWord ++ tailWord_3779484).sum := by decide
  have hdescent : baseEnd_3779484 < baseStart_3779484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779512 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_3779512 : Nat := 118140960795 + 3779512 * 2 ^ 59
def prefixEnd_3779512 : Nat := 4983230072969 + 3 ^ 40 * 3779512 * 2
def baseEnd_3779512 : Nat := 1293804196957281250412231

theorem tailTrace_3779512 : CollatzResearch.WordTrace tailWord_3779512 prefixEnd_3779512 1293804196957281250412231 := by
  unfold tailWord_3779512
  simp only [CollatzResearch.WordTrace]
  refine ⟨68925063741740494052342395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91900084988987325403123193 68925063741740494052342395)
  ·
    refine ⟨103387595612610741078513593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68925063741740494052342395 103387595612610741078513593)
    ·
      refine ⟨77540696709458055808885195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103387595612610741078513593 77540696709458055808885195)
      ·
        refine ⟨116311045064187083713327793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77540696709458055808885195 116311045064187083713327793)
        ·
          refine ⟨87233283798140312784995845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116311045064187083713327793 87233283798140312784995845)
          ·
            refine ⟨16356240712151308647186721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87233283798140312784995845 16356240712151308647186721)
            ·
              refine ⟨12267180534113481485390041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16356240712151308647186721 12267180534113481485390041)
              ·
                refine ⟨9200385400585111114042531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12267180534113481485390041 9200385400585111114042531)
                ·
                  refine ⟨13800578100877666671063797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9200385400585111114042531 13800578100877666671063797)
                  ·
                    refine ⟨1293804196957281250412231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13800578100877666671063797 1293804196957281250412231)
                    ·
                      rfl

theorem cell22_3779512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_3779512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779512 prefixEnd_3779512 := by exact prefixLift 3779512
  have htrace : WordTrace (prefixWord ++ tailWord_3779512) baseStart_3779512 baseEnd_3779512 := by
    simpa [prefixWord, tailWord_3779512, baseEnd_3779512] using wordTrace_append hprefix tailTrace_3779512
  have hstable : (prefixWord ++ tailWord_3779512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779512).length < 2 ^ (prefixWord ++ tailWord_3779512).sum := by decide
  have hdescent : baseEnd_3779512 < baseStart_3779512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779514 : List Nat := [3, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_3779514 : Nat := 118140960795 + 3779514 * 2 ^ 59
def prefixEnd_3779514 : Nat := 4983230072969 + 3 ^ 40 * 3779514 * 2
def baseEnd_3779514 : Nat := 431268293866051303954075

theorem tailTrace_3779514 : CollatzResearch.WordTrace tailWord_3779514 prefixEnd_3779514 431268293866051303954075 := by
  unfold tailWord_3779514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462550107368435611564399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91900133619649161630838397 34462550107368435611564399)
  ·
    refine ⟨51693825161052653417346599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34462550107368435611564399 51693825161052653417346599)
    ·
      refine ⟨77540737741578980126019899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51693825161052653417346599 77540737741578980126019899)
      ·
        refine ⟨116311106612368470189029849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77540737741578980126019899 116311106612368470189029849)
        ·
          refine ⟨87233329959276352641772387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116311106612368470189029849 87233329959276352641772387)
          ·
            refine ⟨130849994938914528962658581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87233329959276352641772387 130849994938914528962658581)
            ·
              refine ⟨6133593512761618545124621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130849994938914528962658581 6133593512761618545124621)
              ·
                refine ⟨2300097567285606954421733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6133593512761618545124621 2300097567285606954421733)
                ·
                  refine ⟨431268293866051303954075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300097567285606954421733 431268293866051303954075)
                  ·
                    rfl

theorem cell22_3779514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_3779514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779514 prefixEnd_3779514 := by exact prefixLift 3779514
  have htrace : WordTrace (prefixWord ++ tailWord_3779514) baseStart_3779514 baseEnd_3779514 := by
    simpa [prefixWord, tailWord_3779514, baseEnd_3779514] using wordTrace_append hprefix tailTrace_3779514
  have hstable : (prefixWord ++ tailWord_3779514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779514).length < 2 ^ (prefixWord ++ tailWord_3779514).sum := by decide
  have hdescent : baseEnd_3779514 < baseStart_3779514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779527 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3779527 : Nat := 118140960795 + 3779527 * 2 ^ 59
def prefixEnd_3779527 : Nat := 4983230072969 + 3 ^ 40 * 3779527 * 2
def baseEnd_3779527 : Nat := 1293809331763826211287185

theorem tailTrace_3779527 : CollatzResearch.WordTrace tailWord_3779527 prefixEnd_3779527 1293809331763826211287185 := by
  unfold tailWord_3779527
  simp only [CollatzResearch.WordTrace]
  refine ⟨137850674578426645666480835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91900449718951097110987223 137850674578426645666480835)
  ·
    refine ⟨206776011867639968499721253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137850674578426645666480835 206776011867639968499721253)
    ·
      refine ⟨38770502225182494093697735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206776011867639968499721253 38770502225182494093697735)
      ·
        refine ⟨58155753337773741140546603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38770502225182494093697735 58155753337773741140546603)
        ·
          refine ⟨87233630006660611710819905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58155753337773741140546603 87233630006660611710819905)
          ·
            refine ⟨65425222504995458783114929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87233630006660611710819905 65425222504995458783114929)
            ·
              refine ⟨49068916878746594087336197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65425222504995458783114929 49068916878746594087336197)
              ·
                refine ⟨9200421914764986391375537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49068916878746594087336197 9200421914764986391375537)
                ·
                  refine ⟨6900316436073739793531653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9200421914764986391375537 6900316436073739793531653)
                  ·
                    refine ⟨1293809331763826211287185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900316436073739793531653 1293809331763826211287185)
                    ·
                      rfl

theorem cell22_3779527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3779527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779527 prefixEnd_3779527 := by exact prefixLift 3779527
  have htrace : WordTrace (prefixWord ++ tailWord_3779527) baseStart_3779527 baseEnd_3779527 := by
    simpa [prefixWord, tailWord_3779527, baseEnd_3779527] using wordTrace_append hprefix tailTrace_3779527
  have hstable : (prefixWord ++ tailWord_3779527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779527).length < 2 ^ (prefixWord ++ tailWord_3779527).sum := by decide
  have hdescent : baseEnd_3779527 < baseStart_3779527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779559 : List Nat := [1, 1, 5, 2, 2, 1, 4, 6]
def baseStart_3779559 : Nat := 118140960795 + 3779559 * 2 ^ 59
def prefixEnd_3779559 : Nat := 4983230072969 + 3 ^ 40 * 3779559 * 2
def baseEnd_3779559 : Nat := 143757809557532088276343

theorem tailTrace_3779559 : CollatzResearch.WordTrace tailWord_3779559 prefixEnd_3779559 143757809557532088276343 := by
  unfold tailWord_3779559
  simp only [CollatzResearch.WordTrace]
  refine ⟨137851841714310715131645731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91901227809540476754430487 137851841714310715131645731)
  ·
    refine ⟨206777762571466072697468597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137851841714310715131645731 206777762571466072697468597)
    ·
      refine ⟨19385415241074944315387681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206777762571466072697468597 19385415241074944315387681)
      ·
        refine ⟨14539061430806208236540761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19385415241074944315387681 14539061430806208236540761)
        ·
          refine ⟨10904296073104656177405571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14539061430806208236540761 10904296073104656177405571)
          ·
            refine ⟨16356444109656984266108357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10904296073104656177405571 16356444109656984266108357)
            ·
              refine ⟨3066833270560684549895317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16356444109656984266108357 3066833270560684549895317)
              ·
                refine ⟨143757809557532088276343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3066833270560684549895317 143757809557532088276343)
                ·
                  rfl

theorem cell22_3779559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 6].length) (baseStart_3779559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779559 prefixEnd_3779559 := by exact prefixLift 3779559
  have htrace : WordTrace (prefixWord ++ tailWord_3779559) baseStart_3779559 baseEnd_3779559 := by
    simpa [prefixWord, tailWord_3779559, baseEnd_3779559] using wordTrace_append hprefix tailTrace_3779559
  have hstable : (prefixWord ++ tailWord_3779559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779559).length < 2 ^ (prefixWord ++ tailWord_3779559).sum := by decide
  have hdescent : baseEnd_3779559 < baseStart_3779559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779647 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_3779647 : Nat := 118140960795 + 3779647 * 2 ^ 59
def prefixEnd_3779647 : Nat := 4983230072969 + 3 ^ 40 * 3779647 * 2
def baseEnd_3779647 : Nat := 1293850410216185898286817

theorem tailTrace_3779647 : CollatzResearch.WordTrace tailWord_3779647 prefixEnd_3779647 1293850410216185898286817 := by
  unfold tailWord_3779647
  simp only [CollatzResearch.WordTrace]
  refine ⟨137855051337991906160849195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91903367558661270773899463 137855051337991906160849195)
  ·
    refine ⟨206782577006987859241273793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137855051337991906160849195 206782577006987859241273793)
    ·
      refine ⟨155086932755240894430955345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206782577006987859241273793 155086932755240894430955345)
      ·
        refine ⟨116315199566430670823216509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155086932755240894430955345 116315199566430670823216509)
        ·
          refine ⟨43618199837411501558706191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116315199566430670823216509 43618199837411501558706191)
          ·
            refine ⟨65427299756117252338059287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43618199837411501558706191 65427299756117252338059287)
            ·
              refine ⟨98140949634175878507088931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65427299756117252338059287 98140949634175878507088931)
              ·
                refine ⟨147211424451263817760633397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98140949634175878507088931 147211424451263817760633397)
                ·
                  refine ⟨13801071042305982915059381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147211424451263817760633397 13801071042305982915059381)
                  ·
                    refine ⟨1293850410216185898286817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13801071042305982915059381 1293850410216185898286817)
                    ·
                      rfl

theorem cell22_3779647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_3779647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779647 prefixEnd_3779647 := by exact prefixLift 3779647
  have htrace : WordTrace (prefixWord ++ tailWord_3779647) baseStart_3779647 baseEnd_3779647 := by
    simpa [prefixWord, tailWord_3779647, baseEnd_3779647] using wordTrace_append hprefix tailTrace_3779647
  have hstable : (prefixWord ++ tailWord_3779647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779647).length < 2 ^ (prefixWord ++ tailWord_3779647).sum := by decide
  have hdescent : baseEnd_3779647 < baseStart_3779647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779694 : List Nat := [4, 1, 2, 2, 1, 3, 9]
def baseStart_3779694 : Nat := 118140960795 + 3779694 * 2 ^ 59
def prefixEnd_3779694 : Nat := 4983230072969 + 3 ^ 40 * 3779694 * 2
def baseEnd_3779694 : Nat := 47920981454692349717099

theorem tailTrace_3779694 : CollatzResearch.WordTrace tailWord_3779694 prefixEnd_3779694 47920981454692349717099 := by
  unfold tailWord_3779694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17232095696102704148476267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91904510379214422125206757 17232095696102704148476267)
  ·
    refine ⟨25848143544154056222714401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17232095696102704148476267 25848143544154056222714401)
    ·
      refine ⟨19386107658115542167035801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25848143544154056222714401 19386107658115542167035801)
      ·
        refine ⟨14539580743586656625276851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19386107658115542167035801 14539580743586656625276851)
        ·
          refine ⟨21809371115379984937915277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14539580743586656625276851 21809371115379984937915277)
          ·
            refine ⟨8178514168267494351718229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21809371115379984937915277 8178514168267494351718229)
            ·
              refine ⟨47920981454692349717099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8178514168267494351718229 47920981454692349717099)
              ·
                rfl

theorem cell22_3779694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 9].length) (baseStart_3779694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779694 prefixEnd_3779694 := by exact prefixLift 3779694
  have htrace : WordTrace (prefixWord ++ tailWord_3779694) baseStart_3779694 baseEnd_3779694 := by
    simpa [prefixWord, tailWord_3779694, baseEnd_3779694] using wordTrace_append hprefix tailTrace_3779694
  have hstable : (prefixWord ++ tailWord_3779694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779694).length < 2 ^ (prefixWord ++ tailWord_3779694).sum := by decide
  have hdescent : baseEnd_3779694 < baseStart_3779694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779707 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_3779707 : Nat := 118140960795 + 3779707 * 2 ^ 59
def prefixEnd_3779707 : Nat := 4983230072969 + 3 ^ 40 * 3779707 * 2
def baseEnd_3779707 : Nat := 1293870949442365741786633

theorem tailTrace_3779707 : CollatzResearch.WordTrace tailWord_3779707 prefixEnd_3779707 1293870949442365741786633 := by
  unfold tailWord_3779707
  simp only [CollatzResearch.WordTrace]
  refine ⟨137857239717774536408033375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91904826478516357605355583 137857239717774536408033375)
  ·
    refine ⟨206785859576661804612050063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137857239717774536408033375 206785859576661804612050063)
    ·
      refine ⟨310178789364992706918075095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206785859576661804612050063 310178789364992706918075095)
      ·
        refine ⟨465268184047489060377112643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310178789364992706918075095 465268184047489060377112643)
        ·
          refine ⟨697902276071233590565668965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465268184047489060377112643 697902276071233590565668965)
          ·
            refine ⟨130856676763356298231062931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697902276071233590565668965 130856676763356298231062931)
            ·
              refine ⟨196285015145034447346594397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130856676763356298231062931 196285015145034447346594397)
              ·
                refine ⟨73606880679387917754972899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196285015145034447346594397 73606880679387917754972899)
                ·
                  refine ⟨110410321019081876632459349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73606880679387917754972899 110410321019081876632459349)
                  ·
                    refine ⟨1293870949442365741786633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110410321019081876632459349 1293870949442365741786633)
                    ·
                      rfl

theorem cell22_3779707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_3779707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779707 prefixEnd_3779707 := by exact prefixLift 3779707
  have htrace : WordTrace (prefixWord ++ tailWord_3779707) baseStart_3779707 baseEnd_3779707 := by
    simpa [prefixWord, tailWord_3779707, baseEnd_3779707] using wordTrace_append hprefix tailTrace_3779707
  have hstable : (prefixWord ++ tailWord_3779707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779707).length < 2 ^ (prefixWord ++ tailWord_3779707).sum := by decide
  have hdescent : baseEnd_3779707 < baseStart_3779707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779766 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3779766 : Nat := 118140960795 + 3779766 * 2 ^ 59
def prefixEnd_3779766 : Nat := 4983230072969 + 3 ^ 40 * 3779766 * 2
def baseEnd_3779766 : Nat := 1293891146348109254561453

theorem tailTrace_3779766 : CollatzResearch.WordTrace tailWord_3779766 prefixEnd_3779766 1293891146348109254561453 := by
  unfold tailWord_3779766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616211976535049342776947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91906261083040526322954101 8616211976535049342776947)
  ·
    refine ⟨12924317964802574014165421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8616211976535049342776947 12924317964802574014165421)
    ·
      refine ⟨4846619236800965255312033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12924317964802574014165421 4846619236800965255312033)
      ·
        refine ⟨3634964427600723941484025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4846619236800965255312033 3634964427600723941484025)
        ·
          refine ⟨2726223320700542956113019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3634964427600723941484025 2726223320700542956113019)
          ·
            refine ⟨4089334981050814434169529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726223320700542956113019 4089334981050814434169529)
            ·
              refine ⟨3067001235788110825627147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089334981050814434169529 3067001235788110825627147)
              ·
                refine ⟨4600501853682166238440721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067001235788110825627147 4600501853682166238440721)
                ·
                  refine ⟨3450376390261624678830541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4600501853682166238440721 3450376390261624678830541)
                  ·
                    refine ⟨1293891146348109254561453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3450376390261624678830541 1293891146348109254561453)
                    ·
                      rfl

theorem cell22_3779766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3779766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779766 prefixEnd_3779766 := by exact prefixLift 3779766
  have htrace : WordTrace (prefixWord ++ tailWord_3779766) baseStart_3779766 baseEnd_3779766 := by
    simpa [prefixWord, tailWord_3779766, baseEnd_3779766] using wordTrace_append hprefix tailTrace_3779766
  have hstable : (prefixWord ++ tailWord_3779766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779766).length < 2 ^ (prefixWord ++ tailWord_3779766).sum := by decide
  have hdescent : baseEnd_3779766 < baseStart_3779766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779784 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_3779784 : Nat := 118140960795 + 3779784 * 2 ^ 59
def prefixEnd_3779784 : Nat := 4983230072969 + 3 ^ 40 * 3779784 * 2
def baseEnd_3779784 : Nat := 431299102705321069203799

theorem tailTrace_3779784 : CollatzResearch.WordTrace tailWord_3779784 prefixEnd_3779784 431299102705321069203799 := by
  unfold tailWord_3779784
  simp only [CollatzResearch.WordTrace]
  refine ⟨68930024069247789279293203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91906698758997052372390937 68930024069247789279293203)
  ·
    refine ⟨103395036103871683918939805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68930024069247789279293203 103395036103871683918939805)
    ·
      refine ⟨38773138538951881469602427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103395036103871683918939805 38773138538951881469602427)
      ·
        refine ⟨58159707808427822204403641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38773138538951881469602427 58159707808427822204403641)
        ·
          refine ⟨43619780856320866653302731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58159707808427822204403641 43619780856320866653302731)
          ·
            refine ⟨65429671284481299979954097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43619780856320866653302731 65429671284481299979954097)
            ·
              refine ⟨49072253463360974984965573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65429671284481299979954097 49072253463360974984965573)
              ·
                refine ⟨9201047524380182809681045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49072253463360974984965573 9201047524380182809681045)
                ·
                  refine ⟨431299102705321069203799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9201047524380182809681045 431299102705321069203799)
                  ·
                    rfl

theorem cell22_3779784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_3779784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779784 prefixEnd_3779784 := by exact prefixLift 3779784
  have htrace : WordTrace (prefixWord ++ tailWord_3779784) baseStart_3779784 baseEnd_3779784 := by
    simpa [prefixWord, tailWord_3779784, baseEnd_3779784] using wordTrace_append hprefix tailTrace_3779784
  have hstable : (prefixWord ++ tailWord_3779784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779784).length < 2 ^ (prefixWord ++ tailWord_3779784).sum := by decide
  have hdescent : baseEnd_3779784 < baseStart_3779784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779786 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3779786 : Nat := 118140960795 + 3779786 * 2 ^ 59
def prefixEnd_3779786 : Nat := 4983230072969 + 3 ^ 40 * 3779786 * 2
def baseEnd_3779786 : Nat := 1293897992756835869061391

theorem tailTrace_3779786 : CollatzResearch.WordTrace tailWord_3779786 prefixEnd_3779786 1293897992756835869061391 := by
  unfold tailWord_3779786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465030271122083225039803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91906747389658888600106141 34465030271122083225039803)
  ·
    refine ⟨51697545406683124837559705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34465030271122083225039803 51697545406683124837559705)
    ·
      refine ⟨38773159055012343628169779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51697545406683124837559705 38773159055012343628169779)
      ·
        refine ⟨58159738582518515442254669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38773159055012343628169779 58159738582518515442254669)
        ·
          refine ⟨21809901968444443290845501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58159738582518515442254669 21809901968444443290845501)
          ·
            refine ⟨8178713238166666234067063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21809901968444443290845501 8178713238166666234067063)
            ·
              refine ⟨12268069857249999351100595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178713238166666234067063 12268069857249999351100595)
              ·
                refine ⟨18402104785874999026650893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12268069857249999351100595 18402104785874999026650893)
                ·
                  refine ⟨6900789294703124634994085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18402104785874999026650893 6900789294703124634994085)
                  ·
                    refine ⟨1293897992756835869061391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6900789294703124634994085 1293897992756835869061391)
                    ·
                      rfl

theorem cell22_3779786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3779786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779786 prefixEnd_3779786 := by exact prefixLift 3779786
  have htrace : WordTrace (prefixWord ++ tailWord_3779786) baseStart_3779786 baseEnd_3779786 := by
    simpa [prefixWord, tailWord_3779786, baseEnd_3779786] using wordTrace_append hprefix tailTrace_3779786
  have hstable : (prefixWord ++ tailWord_3779786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779786).length < 2 ^ (prefixWord ++ tailWord_3779786).sum := by decide
  have hdescent : baseEnd_3779786 < baseStart_3779786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779799 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_3779799 : Nat := 118140960795 + 3779799 * 2 ^ 59
def prefixEnd_3779799 : Nat := 4983230072969 + 3 ^ 40 * 3779799 * 2
def baseEnd_3779799 : Nat := 1293902442922508168486351

theorem tailTrace_3779799 : CollatzResearch.WordTrace tailWord_3779799 prefixEnd_3779799 1293902442922508168486351 := by
  unfold tailWord_3779799
  simp only [CollatzResearch.WordTrace]
  refine ⟨137860595233441236120382451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91907063488960824080254967 137860595233441236120382451)
  ·
    refine ⟨206790892850161854180573677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137860595233441236120382451 206790892850161854180573677)
    ·
      refine ⟨77546584818810695317715129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206790892850161854180573677 77546584818810695317715129)
      ·
        refine ⟨58159938614108021488286347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77546584818810695317715129 58159938614108021488286347)
        ·
          refine ⟨87239907921162032232429521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58159938614108021488286347 87239907921162032232429521)
          ·
            refine ⟨65429930940871524174322141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87239907921162032232429521 65429930940871524174322141)
            ·
              refine ⟨24536224102826821565370803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65429930940871524174322141 24536224102826821565370803)
              ·
                refine ⟨36804336154240232348056205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24536224102826821565370803 36804336154240232348056205)
                ·
                  refine ⟨13801626057840087130521077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36804336154240232348056205 13801626057840087130521077)
                  ·
                    refine ⟨1293902442922508168486351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13801626057840087130521077 1293902442922508168486351)
                    ·
                      rfl

theorem cell22_3779799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_3779799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779799 prefixEnd_3779799 := by exact prefixLift 3779799
  have htrace : WordTrace (prefixWord ++ tailWord_3779799) baseStart_3779799 baseEnd_3779799 := by
    simpa [prefixWord, tailWord_3779799, baseEnd_3779799] using wordTrace_append hprefix tailTrace_3779799
  have hstable : (prefixWord ++ tailWord_3779799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779799).length < 2 ^ (prefixWord ++ tailWord_3779799).sum := by decide
  have hdescent : baseEnd_3779799 < baseStart_3779799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779801 : List Nat := [1, 2, 1, 2, 3, 1, 1, 7, 4]
def baseStart_3779801 : Nat := 118140960795 + 3779801 * 2 ^ 59
def prefixEnd_3779801 : Nat := 4983230072969 + 3 ^ 40 * 3779801 * 2
def baseEnd_3779801 : Nat := 431301042521126943312115

theorem tailTrace_3779801 : CollatzResearch.WordTrace tailWord_3779801 prefixEnd_3779801 431301042521126943312115 := by
  unfold tailWord_3779801
  simp only [CollatzResearch.WordTrace]
  refine ⟨137860668179433990461955257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91907112119622660307970171 137860668179433990461955257)
  ·
    refine ⟨103395501134575492846466443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137860668179433990461955257 103395501134575492846466443)
    ·
      refine ⟨155093251701863239269699665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103395501134575492846466443 155093251701863239269699665)
      ·
        refine ⟨116319938776397429452274749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155093251701863239269699665 116319938776397429452274749)
        ·
          refine ⟨43619977041149036044603031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116319938776397429452274749 43619977041149036044603031)
          ·
            refine ⟨65429965561723554066904547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43619977041149036044603031 65429965561723554066904547)
            ·
              refine ⟨98144948342585331100356821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65429965561723554066904547 98144948342585331100356821)
              ·
                refine ⟨2300272226779343697664613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98144948342585331100356821 2300272226779343697664613)
                ·
                  refine ⟨431301042521126943312115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300272226779343697664613 431301042521126943312115)
                  ·
                    rfl

theorem cell22_3779801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_3779801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779801 prefixEnd_3779801 := by exact prefixLift 3779801
  have htrace : WordTrace (prefixWord ++ tailWord_3779801) baseStart_3779801 baseEnd_3779801 := by
    simpa [prefixWord, tailWord_3779801, baseEnd_3779801] using wordTrace_append hprefix tailTrace_3779801
  have hstable : (prefixWord ++ tailWord_3779801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779801).length < 2 ^ (prefixWord ++ tailWord_3779801).sum := by decide
  have hdescent : baseEnd_3779801 < baseStart_3779801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779818 : List Nat := [3, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_3779818 : Nat := 118140960795 + 3779818 * 2 ^ 59
def prefixEnd_3779818 : Nat := 4983230072969 + 3 ^ 40 * 3779818 * 2
def baseEnd_3779818 : Nat := 431302982336932817420431

theorem tailTrace_3779818 : CollatzResearch.WordTrace tailWord_3779818 prefixEnd_3779818 431302982336932817420431 := by
  unfold tailWord_3779818
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465322055093100591331027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91907525480248268243549405 34465322055093100591331027)
  ·
    refine ⟨51697983082639650886996541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34465322055093100591331027 51697983082639650886996541)
    ·
      refine ⟨19386743655989869082623703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51697983082639650886996541 19386743655989869082623703)
      ·
        refine ⟨29080115483984803623935555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19386743655989869082623703 29080115483984803623935555)
        ·
          refine ⟨43620173225977205435903333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29080115483984803623935555 43620173225977205435903333)
          ·
            refine ⟨8178782479870726019231875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43620173225977205435903333 8178782479870726019231875)
            ·
              refine ⟨12268173719806089028847813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8178782479870726019231875 12268173719806089028847813)
              ·
                refine ⟨2300282572463641692908965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12268173719806089028847813 2300282572463641692908965)
                ·
                  refine ⟨431302982336932817420431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300282572463641692908965 431302982336932817420431)
                  ·
                    rfl

theorem cell22_3779818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_3779818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779818 prefixEnd_3779818 := by exact prefixLift 3779818
  have htrace : WordTrace (prefixWord ++ tailWord_3779818) baseStart_3779818 baseEnd_3779818 := by
    simpa [prefixWord, tailWord_3779818, baseEnd_3779818] using wordTrace_append hprefix tailTrace_3779818
  have hstable : (prefixWord ++ tailWord_3779818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779818).length < 2 ^ (prefixWord ++ tailWord_3779818).sum := by decide
  have hdescent : baseEnd_3779818 < baseStart_3779818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779861 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_3779861 : Nat := 118140960795 + 3779861 * 2 ^ 59
def prefixEnd_3779861 : Nat := 4983230072969 + 3 ^ 40 * 3779861 * 2
def baseEnd_3779861 : Nat := 1293923666789560673436161

theorem tailTrace_3779861 : CollatzResearch.WordTrace tailWord_3779861 prefixEnd_3779861 1293923666789560673436161 := by
  unfold tailWord_3779861
  simp only [CollatzResearch.WordTrace]
  refine ⟨137862856559216620709139437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91908571039477747139426291 137862856559216620709139437)
  ·
    refine ⟨51698571209706232765927289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137862856559216620709139437 51698571209706232765927289)
    ·
      refine ⟨38773928407279674574445467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51698571209706232765927289 38773928407279674574445467)
      ·
        refine ⟨58160892610919511861668201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38773928407279674574445467 58160892610919511861668201)
        ·
          refine ⟨43620669458189633896251151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58160892610919511861668201 43620669458189633896251151)
          ·
            refine ⟨65431004187284450844376727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43620669458189633896251151 65431004187284450844376727)
            ·
              refine ⟨98146506280926676266565091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65431004187284450844376727 98146506280926676266565091)
              ·
                refine ⟨147219759421390014399847637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98146506280926676266565091 147219759421390014399847637)
                ·
                  refine ⟨3450463111438828462496429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 147219759421390014399847637 3450463111438828462496429)
                  ·
                    refine ⟨1293923666789560673436161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3450463111438828462496429 1293923666789560673436161)
                    ·
                      rfl

theorem cell22_3779861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_3779861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779861 prefixEnd_3779861 := by exact prefixLift 3779861
  have htrace : WordTrace (prefixWord ++ tailWord_3779861) baseStart_3779861 baseEnd_3779861 := by
    simpa [prefixWord, tailWord_3779861, baseEnd_3779861] using wordTrace_append hprefix tailTrace_3779861
  have hstable : (prefixWord ++ tailWord_3779861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779861).length < 2 ^ (prefixWord ++ tailWord_3779861).sum := by decide
  have hdescent : baseEnd_3779861 < baseStart_3779861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779908 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_3779908 : Nat := 118140960795 + 3779908 * 2 ^ 59
def prefixEnd_3779908 : Nat := 4983230072969 + 3 ^ 40 * 3779908 * 2
def baseEnd_3779908 : Nat := 431313251950022739170339

theorem tailTrace_3779908 : CollatzResearch.WordTrace tailWord_3779908 prefixEnd_3779908 431313251950022739170339 := by
  unfold tailWord_3779908
  simp only [CollatzResearch.WordTrace]
  refine ⟨68932285395023173868050189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91909713860030898490733585 68932285395023173868050189)
  ·
    refine ⟨25849607023133690200518821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68932285395023173868050189 25849607023133690200518821)
    ·
      refine ⟨4846801316837566912597279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25849607023133690200518821 4846801316837566912597279)
      ·
        refine ⟨7270201975256350368895919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4846801316837566912597279 7270201975256350368895919)
        ·
          refine ⟨10905302962884525553343879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7270201975256350368895919 10905302962884525553343879)
          ·
            refine ⟨16357954444326788330015819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10905302962884525553343879 16357954444326788330015819)
            ·
              refine ⟨24536931666490182495023729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16357954444326788330015819 24536931666490182495023729)
              ·
                refine ⟨18402698749867636871267797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24536931666490182495023729 18402698749867636871267797)
                ·
                  refine ⟨431313251950022739170339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18402698749867636871267797 431313251950022739170339)
                  ·
                    rfl

theorem cell22_3779908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_3779908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779908 prefixEnd_3779908 := by exact prefixLift 3779908
  have htrace : WordTrace (prefixWord ++ tailWord_3779908) baseStart_3779908 baseEnd_3779908 := by
    simpa [prefixWord, tailWord_3779908, baseEnd_3779908] using wordTrace_append hprefix tailTrace_3779908
  have hstable : (prefixWord ++ tailWord_3779908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779908).length < 2 ^ (prefixWord ++ tailWord_3779908).sum := by decide
  have hdescent : baseEnd_3779908 < baseStart_3779908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779938 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3779938 : Nat := 118140960795 + 3779938 * 2 ^ 59
def prefixEnd_3779938 : Nat := 4983230072969 + 3 ^ 40 * 3779938 * 2
def baseEnd_3779938 : Nat := 1293950025463158139260925

theorem tailTrace_3779938 : CollatzResearch.WordTrace tailWord_3779938 prefixEnd_3779938 1293950025463158139260925 := by
  unfold tailWord_3779938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34466416244984415714923117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91910443319958441906461645 34466416244984415714923117)
  ·
    refine ⟨12924906091869155893096169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34466416244984415714923117 12924906091869155893096169)
    ·
      refine ⟨9693679568901866919822127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12924906091869155893096169 9693679568901866919822127)
      ·
        refine ⟨14540519353352800379733191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9693679568901866919822127 14540519353352800379733191)
        ·
          refine ⟨21810779030029200569599787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14540519353352800379733191 21810779030029200569599787)
          ·
            refine ⟨32716168545043800854399681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21810779030029200569599787 32716168545043800854399681)
            ·
              refine ⟨24537126408782850640799761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32716168545043800854399681 24537126408782850640799761)
              ·
                refine ⟨18402844806587137980599821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24537126408782850640799761 18402844806587137980599821)
                ·
                  refine ⟨6901066802470176742724933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18402844806587137980599821 6901066802470176742724933)
                  ·
                    refine ⟨1293950025463158139260925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6901066802470176742724933 1293950025463158139260925)
                    ·
                      rfl

theorem cell22_3779938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3779938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779938 prefixEnd_3779938 := by exact prefixLift 3779938
  have htrace : WordTrace (prefixWord ++ tailWord_3779938) baseStart_3779938 baseEnd_3779938 := by
    simpa [prefixWord, tailWord_3779938, baseEnd_3779938] using wordTrace_append hprefix tailTrace_3779938
  have hstable : (prefixWord ++ tailWord_3779938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779938).length < 2 ^ (prefixWord ++ tailWord_3779938).sum := by decide
  have hdescent : baseEnd_3779938 < baseStart_3779938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779951 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 1, 5]
def baseStart_3779951 : Nat := 118140960795 + 3779951 * 2 ^ 59
def prefixEnd_3779951 : Nat := 4983230072969 + 3 ^ 40 * 3779951 * 2
def baseEnd_3779951 : Nat := 1293954475628830438685885

theorem tailTrace_3779951 : CollatzResearch.WordTrace tailWord_3779951 prefixEnd_3779951 1293954475628830438685885 := by
  unfold tailWord_3779951
  simp only [CollatzResearch.WordTrace]
  refine ⟨137866139128890566079915707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91910759419260377386610471 137866139128890566079915707)
  ·
    refine ⟨206799208693335849119873561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137866139128890566079915707 206799208693335849119873561)
    ·
      refine ⟨155099406520001886839905171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206799208693335849119873561 155099406520001886839905171)
      ·
        refine ⟨232649109780002830259857757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155099406520001886839905171 232649109780002830259857757)
        ·
          refine ⟨87243416167501061347446659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232649109780002830259857757 87243416167501061347446659)
          ·
            refine ⟨130865124251251592021169989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87243416167501061347446659 130865124251251592021169989)
            ·
              refine ⟨24537210797109673503969373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130865124251251592021169989 24537210797109673503969373)
              ·
                refine ⟨9201454048916127563988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24537210797109673503969373 9201454048916127563988515)
                ·
                  refine ⟨13802181073374191345982773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9201454048916127563988515 13802181073374191345982773)
                  ·
                    refine ⟨1293954475628830438685885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13802181073374191345982773 1293954475628830438685885)
                    ·
                      rfl

theorem cell22_3779951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_3779951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3779951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3779951 prefixEnd_3779951 := by exact prefixLift 3779951
  have htrace : WordTrace (prefixWord ++ tailWord_3779951) baseStart_3779951 baseEnd_3779951 := by
    simpa [prefixWord, tailWord_3779951, baseEnd_3779951] using wordTrace_append hprefix tailTrace_3779951
  have hstable : (prefixWord ++ tailWord_3779951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779951).length < 2 ^ (prefixWord ++ tailWord_3779951).sum := by decide
  have hdescent : baseEnd_3779951 < baseStart_3779951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780043 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 5]
def baseStart_3780043 : Nat := 118140960795 + 3780043 * 2 ^ 59
def prefixEnd_3780043 : Nat := 4983230072969 + 3 ^ 40 * 3780043 * 2
def baseEnd_3780043 : Nat := 431328656369657621795201

theorem tailTrace_3780043 : CollatzResearch.WordTrace tailWord_3780043 prefixEnd_3780043 431328656369657621795201 := by
  unfold tailWord_3780043
  simp only [CollatzResearch.WordTrace]
  refine ⟨137869494644557265792264783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91912996429704843861509855 137869494644557265792264783)
  ·
    refine ⟨206804241966835898688397175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137869494644557265792264783 206804241966835898688397175)
    ·
      refine ⟨310206362950253848032595763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206804241966835898688397175 310206362950253848032595763)
      ·
        refine ⟨465309544425380772048893645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310206362950253848032595763 465309544425380772048893645)
        ·
          refine ⟨174491079159517789518335117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465309544425380772048893645 174491079159517789518335117)
          ·
            refine ⟨65434154684819171069375669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174491079159517789518335117 65434154684819171069375669)
            ·
              refine ⟨6134452001701797287753969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65434154684819171069375669 6134452001701797287753969)
              ·
                refine ⟨4600839001276347965815477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6134452001701797287753969 4600839001276347965815477)
                ·
                  refine ⟨431328656369657621795201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600839001276347965815477 431328656369657621795201)
                  ·
                    rfl

theorem cell22_3780043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 5].length) (baseStart_3780043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780043 prefixEnd_3780043 := by exact prefixLift 3780043
  have htrace : WordTrace (prefixWord ++ tailWord_3780043) baseStart_3780043 baseEnd_3780043 := by
    simpa [prefixWord, tailWord_3780043, baseEnd_3780043] using wordTrace_append hprefix tailTrace_3780043
  have hstable : (prefixWord ++ tailWord_3780043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780043).length < 2 ^ (prefixWord ++ tailWord_3780043).sum := by decide
  have hdescent : baseEnd_3780043 < baseStart_3780043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780058 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3780058 : Nat := 118140960795 + 3780058 * 2 ^ 59
def prefixEnd_3780058 : Nat := 4983230072969 + 3 ^ 40 * 3780058 * 2
def baseEnd_3780058 : Nat := 1293991103915517826260557

theorem tailTrace_3780058 : CollatzResearch.WordTrace tailWord_3780058 prefixEnd_3780058 1293991103915517826260557 := by
  unfold tailWord_3780058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34467510434875730838515207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91913361159668615569373885 34467510434875730838515207)
  ·
    refine ⟨51701265652313596257772811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34467510434875730838515207 51701265652313596257772811)
    ·
      refine ⟨77551898478470394386659217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51701265652313596257772811 77551898478470394386659217)
      ·
        refine ⟨58163923858852795789994413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77551898478470394386659217 58163923858852795789994413)
        ·
          refine ⟨21811471447069798421247905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58163923858852795789994413 21811471447069798421247905)
          ·
            refine ⟨16358603585302348815935929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21811471447069798421247905 16358603585302348815935929)
            ·
              refine ⟨12268952688976761611951947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16358603585302348815935929 12268952688976761611951947)
              ·
                refine ⟨18403429033465142417927921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12268952688976761611951947 18403429033465142417927921)
                ·
                  refine ⟨13802571775098856813445941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18403429033465142417927921 13802571775098856813445941)
                  ·
                    refine ⟨1293991103915517826260557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13802571775098856813445941 1293991103915517826260557)
                    ·
                      rfl

theorem cell22_3780058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3780058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780058 prefixEnd_3780058 := by exact prefixLift 3780058
  have htrace : WordTrace (prefixWord ++ tailWord_3780058) baseStart_3780058 baseEnd_3780058 := by
    simpa [prefixWord, tailWord_3780058, baseEnd_3780058] using wordTrace_append hprefix tailTrace_3780058
  have hstable : (prefixWord ++ tailWord_3780058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780058).length < 2 ^ (prefixWord ++ tailWord_3780058).sum := by decide
  have hdescent : baseEnd_3780058 < baseStart_3780058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780150 : List Nat := [5, 1, 2, 1, 3, 10]
def baseStart_3780150 : Nat := 118140960795 + 3780150 * 2 ^ 59
def prefixEnd_3780150 : Nat := 4983230072969 + 3 ^ 40 * 3780150 * 2
def baseEnd_3780150 : Nat := 15975587622168645098275

theorem tailTrace_3780150 : CollatzResearch.WordTrace tailWord_3780150 prefixEnd_3780150 15975587622168645098275 := by
  unfold tailWord_3780150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8617087328448101441650619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91915598170113082044273269 8617087328448101441650619)
  ·
    refine ⟨12925630992672152162475929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8617087328448101441650619 12925630992672152162475929)
    ·
      refine ⟨9694223244504114121856947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12925630992672152162475929 9694223244504114121856947)
      ·
        refine ⟨14541334866756171182785421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694223244504114121856947 14541334866756171182785421)
        ·
          refine ⟨5453000575033564193544533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14541334866756171182785421 5453000575033564193544533)
          ·
            refine ⟨15975587622168645098275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5453000575033564193544533 15975587622168645098275)
            ·
              rfl

theorem cell22_3780150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 10].length) (baseStart_3780150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780150 prefixEnd_3780150 := by exact prefixLift 3780150
  have htrace : WordTrace (prefixWord ++ tailWord_3780150) baseStart_3780150 baseEnd_3780150 := by
    simpa [prefixWord, tailWord_3780150, baseEnd_3780150] using wordTrace_append hprefix tailTrace_3780150
  have hstable : (prefixWord ++ tailWord_3780150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780150).length < 2 ^ (prefixWord ++ tailWord_3780150).sum := by decide
  have hdescent : baseEnd_3780150 < baseStart_3780150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780156 : List Nat := [2, 2, 2, 2, 5, 1, 2, 2, 4]
def baseStart_3780156 : Nat := 118140960795 + 3780156 * 2 ^ 59
def prefixEnd_3780156 : Nat := 4983230072969 + 3 ^ 40 * 3780156 * 2
def baseEnd_3780156 : Nat := 431341550439426079103419

theorem tailTrace_3780156 : CollatzResearch.WordTrace tailWord_3780156 prefixEnd_3780156 431341550439426079103419 := by
  unfold tailWord_3780156
  simp only [CollatzResearch.WordTrace]
  refine ⟨68936808046573943045564161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91915744062098590727418881 68936808046573943045564161)
  ·
    refine ⟨51702606034930457284173121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68936808046573943045564161 51702606034930457284173121)
    ·
      refine ⟨38776954526197842963129841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51702606034930457284173121 38776954526197842963129841)
      ·
        refine ⟨29082715894648382222347381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38776954526197842963129841 29082715894648382222347381)
        ·
          refine ⟨2726504615123285833345067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29082715894648382222347381 2726504615123285833345067)
          ·
            refine ⟨4089756922684928750017601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726504615123285833345067 4089756922684928750017601)
            ·
              refine ⟨3067317692013696562513201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089756922684928750017601 3067317692013696562513201)
              ·
                refine ⟨2300488269010272421884901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067317692013696562513201 2300488269010272421884901)
                ·
                  refine ⟨431341550439426079103419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300488269010272421884901 431341550439426079103419)
                  ·
                    rfl

theorem cell22_3780156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_3780156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780156 prefixEnd_3780156 := by exact prefixLift 3780156
  have htrace : WordTrace (prefixWord ++ tailWord_3780156) baseStart_3780156 baseEnd_3780156 := by
    simpa [prefixWord, tailWord_3780156, baseEnd_3780156] using wordTrace_append hprefix tailTrace_3780156
  have hstable : (prefixWord ++ tailWord_3780156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780156).length < 2 ^ (prefixWord ++ tailWord_3780156).sum := by decide
  have hdescent : baseEnd_3780156 < baseStart_3780156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780165 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_3780165 : Nat := 118140960795 + 3780165 * 2 ^ 59
def prefixEnd_3780165 : Nat := 4983230072969 + 3 ^ 40 * 3780165 * 2
def baseEnd_3780165 : Nat := 1294027732202205213835229

theorem tailTrace_3780165 : CollatzResearch.WordTrace tailWord_3780165 prefixEnd_3780165 1294027732202205213835229 := by
  unfold tailWord_3780165
  simp only [CollatzResearch.WordTrace]
  refine ⟨137873944350115280628205949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91915962900076853752137299 137873944350115280628205949)
  ·
    refine ⟨51702729131293230235577231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137873944350115280628205949 51702729131293230235577231)
    ·
      refine ⟨77554093696939845353365847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51702729131293230235577231 77554093696939845353365847)
      ·
        refine ⟨116331140545409768030048771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77554093696939845353365847 116331140545409768030048771)
        ·
          refine ⟨174496710818114652045073157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116331140545409768030048771 174496710818114652045073157)
          ·
            refine ⟨32718133278396497258451217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174496710818114652045073157 32718133278396497258451217)
            ·
              refine ⟨24538599958797372943838413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32718133278396497258451217 24538599958797372943838413)
              ·
                refine ⟨9201974984549014853939405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24538599958797372943838413 9201974984549014853939405)
                ·
                  refine ⟨3450740619205880570227277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9201974984549014853939405 3450740619205880570227277)
                  ·
                    refine ⟨1294027732202205213835229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3450740619205880570227277 1294027732202205213835229)
                    ·
                      rfl

theorem cell22_3780165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_3780165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780165 prefixEnd_3780165 := by exact prefixLift 3780165
  have htrace : WordTrace (prefixWord ++ tailWord_3780165) baseStart_3780165 baseEnd_3780165 := by
    simpa [prefixWord, tailWord_3780165, baseEnd_3780165] using wordTrace_append hprefix tailTrace_3780165
  have hstable : (prefixWord ++ tailWord_3780165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780165).length < 2 ^ (prefixWord ++ tailWord_3780165).sum := by decide
  have hdescent : baseEnd_3780165 < baseStart_3780165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780167 : List Nat := [1, 1, 4, 1, 6, 1, 1, 7]
def baseStart_3780167 : Nat := 118140960795 + 3780167 * 2 ^ 59
def prefixEnd_3780167 : Nat := 4983230072969 + 3 ^ 40 * 3780167 * 2
def baseEnd_3780167 : Nat := 143780935204786430587247

theorem tailTrace_3780167 : CollatzResearch.WordTrace tailWord_3780167 prefixEnd_3780167 143780935204786430587247 := by
  unfold tailWord_3780167
  simp only [CollatzResearch.WordTrace]
  refine ⟨137874017296108034969778755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91916011530738689979852503 137874017296108034969778755)
  ·
    refine ⟨206811025944162052454668133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137874017296108034969778755 206811025944162052454668133)
    ·
      refine ⟨38777067364530384835250275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206811025944162052454668133 38777067364530384835250275)
      ·
        refine ⟨58165601046795577252875413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38777067364530384835250275 58165601046795577252875413)
        ·
          refine ⟨2726512549068542683728535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58165601046795577252875413 2726512549068542683728535)
          ·
            refine ⟨4089768823602814025592803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726512549068542683728535 4089768823602814025592803)
            ·
              refine ⟨6134653235404221038389205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089768823602814025592803 6134653235404221038389205)
              ·
                refine ⟨143780935204786430587247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6134653235404221038389205 143780935204786430587247)
                ·
                  rfl

theorem cell22_3780167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 7].length) (baseStart_3780167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780167 prefixEnd_3780167 := by exact prefixLift 3780167
  have htrace : WordTrace (prefixWord ++ tailWord_3780167) baseStart_3780167 baseEnd_3780167 := by
    simpa [prefixWord, tailWord_3780167, baseEnd_3780167] using wordTrace_append hprefix tailTrace_3780167
  have hstable : (prefixWord ++ tailWord_3780167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780167).length < 2 ^ (prefixWord ++ tailWord_3780167).sum := by decide
  have hdescent : baseEnd_3780167 < baseStart_3780167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780193 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3780193 : Nat := 118140960795 + 3780193 * 2 ^ 59
def prefixEnd_3780193 : Nat := 4983230072969 + 3 ^ 40 * 3780193 * 2
def baseEnd_3780193 : Nat := 1294037317174422474135143

theorem tailTrace_3780193 : CollatzResearch.WordTrace tailWord_3780193 prefixEnd_3780193 1294037317174422474135143 := by
  unfold tailWord_3780193
  simp only [CollatzResearch.WordTrace]
  refine ⟨137874965594013841410225233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91916643729342560940150155 137874965594013841410225233)
  ·
    refine ⟨103406224195510381057668925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137874965594013841410225233 103406224195510381057668925)
    ·
      refine ⟨38777334073316392896625847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103406224195510381057668925 38777334073316392896625847)
      ·
        refine ⟨58166001109974589344938771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38777334073316392896625847 58166001109974589344938771)
        ·
          refine ⟨87249001664961884017408157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58166001109974589344938771 87249001664961884017408157)
          ·
            refine ⟨32718375624360706506528059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87249001664961884017408157 32718375624360706506528059)
            ·
              refine ⟨49077563436541059759792089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32718375624360706506528059 49077563436541059759792089)
              ·
                refine ⟨36808172577405794819844067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49077563436541059759792089 36808172577405794819844067)
                ·
                  refine ⟨55212258866108692229766101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36808172577405794819844067 55212258866108692229766101)
                  ·
                    refine ⟨1294037317174422474135143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55212258866108692229766101 1294037317174422474135143)
                    ·
                      rfl

theorem cell22_3780193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3780193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780193 prefixEnd_3780193 := by exact prefixLift 3780193
  have htrace : WordTrace (prefixWord ++ tailWord_3780193) baseStart_3780193 baseEnd_3780193 := by
    simpa [prefixWord, tailWord_3780193, baseEnd_3780193] using wordTrace_append hprefix tailTrace_3780193
  have hstable : (prefixWord ++ tailWord_3780193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780193).length < 2 ^ (prefixWord ++ tailWord_3780193).sum := by decide
  have hdescent : baseEnd_3780193 < baseStart_3780193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780210 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_3780210 : Nat := 118140960795 + 3780210 * 2 ^ 59
def prefixEnd_3780210 : Nat := 4983230072969 + 3 ^ 40 * 3780210 * 2
def baseEnd_3780210 : Nat := 1294043136621840096460091

theorem tailTrace_3780210 : CollatzResearch.WordTrace tailWord_3780210 prefixEnd_3780210 1294043136621840096460091 := by
  unfold tailWord_3780210
  simp only [CollatzResearch.WordTrace]
  refine ⟨34468896408738063328398521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91917057089968168875729389 34468896408738063328398521)
  ·
    refine ⟨25851672306553547496298891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34468896408738063328398521 25851672306553547496298891)
    ·
      refine ⟨38777508459830321244448337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25851672306553547496298891 38777508459830321244448337)
      ·
        refine ⟨29083131344872740933336253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38777508459830321244448337 29083131344872740933336253)
        ·
          refine ⟨10906174254327277850001095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29083131344872740933336253 10906174254327277850001095)
          ·
            refine ⟨16359261381490916775001643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10906174254327277850001095 16359261381490916775001643)
            ·
              refine ⟨24538892072236375162502465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16359261381490916775001643 24538892072236375162502465)
              ·
                refine ⟨18404169054177281371876849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24538892072236375162502465 18404169054177281371876849)
                ·
                  refine ⟨13803126790632961028907637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18404169054177281371876849 13803126790632961028907637)
                  ·
                    refine ⟨1294043136621840096460091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13803126790632961028907637 1294043136621840096460091)
                    ·
                      rfl

theorem cell22_3780210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_3780210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780210 prefixEnd_3780210 := by exact prefixLift 3780210
  have htrace : WordTrace (prefixWord ++ tailWord_3780210) baseStart_3780210 baseEnd_3780210 := by
    simpa [prefixWord, tailWord_3780210, baseEnd_3780210] using wordTrace_append hprefix tailTrace_3780210
  have hstable : (prefixWord ++ tailWord_3780210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780210).length < 2 ^ (prefixWord ++ tailWord_3780210).sum := by decide
  have hdescent : baseEnd_3780210 < baseStart_3780210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780285 : List Nat := [1, 4, 1, 2, 1, 2, 4, 7]
def baseStart_3780285 : Nat := 118140960795 + 3780285 * 2 ^ 59
def prefixEnd_3780285 : Nat := 4983230072969 + 3 ^ 40 * 3780285 * 2
def baseEnd_3780285 : Nat := 143785423406062766759429

theorem tailTrace_3780285 : CollatzResearch.WordTrace tailWord_3780285 prefixEnd_3780285 143785423406062766759429 := by
  unfold tailWord_3780285
  simp only [CollatzResearch.WordTrace]
  refine ⟨137878321109680541122574309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91918880739787027415049539 137878321109680541122574309)
  ·
    refine ⟨25852185208065101460482683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137878321109680541122574309 25852185208065101460482683)
    ·
      refine ⟨38778277812097652190724025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25852185208065101460482683 38778277812097652190724025)
      ·
        refine ⟨29083708359073239143043019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38778277812097652190724025 29083708359073239143043019)
        ·
          refine ⟨43625562538609858714564529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29083708359073239143043019 43625562538609858714564529)
          ·
            refine ⟨32719171903957394035923397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43625562538609858714564529 32719171903957394035923397)
            ·
              refine ⟨6134844731992011381735637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32719171903957394035923397 6134844731992011381735637)
              ·
                refine ⟨143785423406062766759429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6134844731992011381735637 143785423406062766759429)
                ·
                  rfl

theorem cell22_3780285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 7].length) (baseStart_3780285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780285 prefixEnd_3780285 := by exact prefixLift 3780285
  have htrace : WordTrace (prefixWord ++ tailWord_3780285) baseStart_3780285 baseEnd_3780285 := by
    simpa [prefixWord, tailWord_3780285, baseEnd_3780285] using wordTrace_append hprefix tailTrace_3780285
  have hstable : (prefixWord ++ tailWord_3780285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780285).length < 2 ^ (prefixWord ++ tailWord_3780285).sum := by decide
  have hdescent : baseEnd_3780285 < baseStart_3780285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780330 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_3780330 : Nat := 118140960795 + 3780330 * 2 ^ 59
def prefixEnd_3780330 : Nat := 4983230072969 + 3 ^ 40 * 3780330 * 2
def baseEnd_3780330 : Nat := 431361405024733261153241

theorem tailTrace_3780330 : CollatzResearch.WordTrace tailWord_3780330 prefixEnd_3780330 431361405024733261153241 := by
  unfold tailWord_3780330
  simp only [CollatzResearch.WordTrace]
  refine ⟨34469990598629378451990611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91919974929678342538641629 34469990598629378451990611)
  ·
    refine ⟨51704985897944067677985917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34469990598629378451990611 51704985897944067677985917)
    ·
      refine ⟨19389369711729025379244719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51704985897944067677985917 19389369711729025379244719)
      ·
        refine ⟨29084054567593538068867079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19389369711729025379244719 29084054567593538068867079)
        ·
          refine ⟨43626081851390307103300619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29084054567593538068867079 43626081851390307103300619)
          ·
            refine ⟨65439122777085460654950929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43626081851390307103300619 65439122777085460654950929)
            ·
              refine ⟨49079342082814095491213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65439122777085460654950929 49079342082814095491213197)
              ·
                refine ⟨18404753281055285809204949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49079342082814095491213197 18404753281055285809204949)
                ·
                  refine ⟨431361405024733261153241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18404753281055285809204949 431361405024733261153241)
                  ·
                    rfl

theorem cell22_3780330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_3780330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780330 prefixEnd_3780330 := by exact prefixLift 3780330
  have htrace : WordTrace (prefixWord ++ tailWord_3780330) baseStart_3780330 baseEnd_3780330 := by
    simpa [prefixWord, tailWord_3780330, baseEnd_3780330] using wordTrace_append hprefix tailTrace_3780330
  have hstable : (prefixWord ++ tailWord_3780330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780330).length < 2 ^ (prefixWord ++ tailWord_3780330).sum := by decide
  have hdescent : baseEnd_3780330 < baseStart_3780330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780392 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_3780392 : Nat := 118140960795 + 3780392 * 2 ^ 59
def prefixEnd_3780392 : Nat := 4983230072969 + 3 ^ 40 * 3780392 * 2
def baseEnd_3780392 : Nat := 431368479647084096136511

theorem tailTrace_3780392 : CollatzResearch.WordTrace tailWord_3780392 prefixEnd_3780392 431368479647084096136511 := by
  unfold tailWord_3780392
  simp only [CollatzResearch.WordTrace]
  refine ⟨68941111860146449198359715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91921482480195265597812953 68941111860146449198359715)
  ·
    refine ⟨103411667790219673797539573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68941111860146449198359715 103411667790219673797539573)
    ·
      refine ⟨9694843855333094418519335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103411667790219673797539573 9694843855333094418519335)
      ·
        refine ⟨14542265782999641627779003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694843855333094418519335 14542265782999641627779003)
        ·
          refine ⟨21813398674499462441668505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14542265782999641627779003 21813398674499462441668505)
          ·
            refine ⟨16360049005874596831251379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21813398674499462441668505 16360049005874596831251379)
            ·
              refine ⟨24540073508811895246877069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16360049005874596831251379 24540073508811895246877069)
              ·
                refine ⟨9202527565804460717578901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24540073508811895246877069 9202527565804460717578901)
                ·
                  refine ⟨431368479647084096136511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9202527565804460717578901 431368479647084096136511)
                  ·
                    rfl

theorem cell22_3780392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_3780392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780392 prefixEnd_3780392 := by exact prefixLift 3780392
  have htrace : WordTrace (prefixWord ++ tailWord_3780392) baseStart_3780392 baseEnd_3780392 := by
    simpa [prefixWord, tailWord_3780392, baseEnd_3780392] using wordTrace_append hprefix tailTrace_3780392
  have hstable : (prefixWord ++ tailWord_3780392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780392).length < 2 ^ (prefixWord ++ tailWord_3780392).sum := by decide
  have hdescent : baseEnd_3780392 < baseStart_3780392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780437 : List Nat := [1, 3, 2, 2, 2, 4, 8]
def baseStart_3780437 : Nat := 118140960795 + 3780437 * 2 ^ 59
def prefixEnd_3780437 : Nat := 4983230072969 + 3 ^ 40 * 3780437 * 2
def baseEnd_3780437 : Nat := 47930401605958784112385

theorem tailTrace_3780437 : CollatzResearch.WordTrace tailWord_3780437 prefixEnd_3780437 47930401605958784112385 := by
  unfold tailWord_3780437
  simp only [CollatzResearch.WordTrace]
  refine ⟨137883865005129871082107565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91922576670086580721405043 137883865005129871082107565)
  ·
    refine ⟨51706449376923701655790337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137883865005129871082107565 51706449376923701655790337)
    ·
      refine ⟨38779837032692776241842753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51706449376923701655790337 38779837032692776241842753)
      ·
        refine ⟨29084877774519582181382065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38779837032692776241842753 29084877774519582181382065)
        ·
          refine ⟨21813658330889686636036549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29084877774519582181382065 21813658330889686636036549)
          ·
            refine ⟨4090060937041816244256853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21813658330889686636036549 4090060937041816244256853)
            ·
              refine ⟨47930401605958784112385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4090060937041816244256853 47930401605958784112385)
              ·
                rfl

theorem cell22_3780437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 8].length) (baseStart_3780437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780437 prefixEnd_3780437 := by exact prefixLift 3780437
  have htrace : WordTrace (prefixWord ++ tailWord_3780437) baseStart_3780437 baseEnd_3780437 := by
    simpa [prefixWord, tailWord_3780437, baseEnd_3780437] using wordTrace_append hprefix tailTrace_3780437
  have hstable : (prefixWord ++ tailWord_3780437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780437).length < 2 ^ (prefixWord ++ tailWord_3780437).sum := by decide
  have hdescent : baseEnd_3780437 < baseStart_3780437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780439 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 2, 4]
def baseStart_3780439 : Nat := 118140960795 + 3780439 * 2 ^ 59
def prefixEnd_3780439 : Nat := 4983230072969 + 3 ^ 40 * 3780439 * 2
def baseEnd_3780439 : Nat := 1294121528001759832484389

theorem tailTrace_3780439 : CollatzResearch.WordTrace tailWord_3780439 prefixEnd_3780439 1294121528001759832484389 := by
  unfold tailWord_3780439
  simp only [CollatzResearch.WordTrace]
  refine ⟨137883937951122625423680371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91922625300748416949120247 137883937951122625423680371)
  ·
    refine ⟨206825906926683938135520557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137883937951122625423680371 206825906926683938135520557)
    ·
      refine ⟨77559715097506476800820209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206825906926683938135520557 77559715097506476800820209)
      ·
        refine ⟨58169786323129857600615157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77559715097506476800820209 58169786323129857600615157)
        ·
          refine ⟨5453417467793424150057671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58169786323129857600615157 5453417467793424150057671)
          ·
            refine ⟨8180126201690136225086507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453417467793424150057671 8180126201690136225086507)
            ·
              refine ⟨12270189302535204337629761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180126201690136225086507 12270189302535204337629761)
              ·
                refine ⟨9202641976901403253222321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12270189302535204337629761 9202641976901403253222321)
                ·
                  refine ⟨6901981482676052439916741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9202641976901403253222321 6901981482676052439916741)
                  ·
                    refine ⟨1294121528001759832484389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6901981482676052439916741 1294121528001759832484389)
                    ·
                      rfl

theorem cell22_3780439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_3780439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780439 prefixEnd_3780439 := by exact prefixLift 3780439
  have htrace : WordTrace (prefixWord ++ tailWord_3780439) baseStart_3780439 baseEnd_3780439 := by
    simpa [prefixWord, tailWord_3780439, baseEnd_3780439] using wordTrace_append hprefix tailTrace_3780439
  have hstable : (prefixWord ++ tailWord_3780439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780439).length < 2 ^ (prefixWord ++ tailWord_3780439).sum := by decide
  have hdescent : baseEnd_3780439 < baseStart_3780439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780458 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_3780458 : Nat := 118140960795 + 3780458 * 2 ^ 59
def prefixEnd_3780458 : Nat := 4983230072969 + 3 ^ 40 * 3780458 * 2
def baseEnd_3780458 : Nat := 1294128032090050116259331

theorem tailTrace_3780458 : CollatzResearch.WordTrace tailWord_3780458 prefixEnd_3780458 1294128032090050116259331 := by
  unfold tailWord_3780458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34471157734513447917155507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91923087292035861112414685 34471157734513447917155507)
  ·
    refine ⟨51706736601770171875733261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34471157734513447917155507 51706736601770171875733261)
    ·
      refine ⟨19390026225663814453399973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51706736601770171875733261 19390026225663814453399973)
      ·
        refine ⟨3635629917311965210012495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19390026225663814453399973 3635629917311965210012495)
        ·
          refine ⟨5453444875967947815018743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3635629917311965210012495 5453444875967947815018743)
          ·
            refine ⟨8180167313951921722528115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453444875967947815018743 8180167313951921722528115)
            ·
              refine ⟨12270250970927882583792173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8180167313951921722528115 12270250970927882583792173)
              ·
                refine ⟨4601344114097955968922065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12270250970927882583792173 4601344114097955968922065)
                ·
                  refine ⟨3451008085573466976691549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4601344114097955968922065 3451008085573466976691549)
                  ·
                    refine ⟨1294128032090050116259331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451008085573466976691549 1294128032090050116259331)
                    ·
                      rfl

theorem cell22_3780458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_3780458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780458 prefixEnd_3780458 := by exact prefixLift 3780458
  have htrace : WordTrace (prefixWord ++ tailWord_3780458) baseStart_3780458 baseEnd_3780458 := by
    simpa [prefixWord, tailWord_3780458, baseEnd_3780458] using wordTrace_append hprefix tailTrace_3780458
  have hstable : (prefixWord ++ tailWord_3780458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780458).length < 2 ^ (prefixWord ++ tailWord_3780458).sum := by decide
  have hdescent : baseEnd_3780458 < baseStart_3780458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780469 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3780469 : Nat := 118140960795 + 3780469 * 2 ^ 59
def prefixEnd_3780469 : Nat := 4983230072969 + 3 ^ 40 * 3780469 * 2
def baseEnd_3780469 : Nat := 1294131797614849754234297

theorem tailTrace_3780469 : CollatzResearch.WordTrace tailWord_3780469 prefixEnd_3780469 1294131797614849754234297 := by
  unfold tailWord_3780469
  simp only [CollatzResearch.WordTrace]
  refine ⟨137885032141013940547272461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91923354760675960364848307 137885032141013940547272461)
  ·
    refine ⟨51706887052880227705227173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137885032141013940547272461 51706887052880227705227173)
    ·
      refine ⟨9695041322415042694730095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51706887052880227705227173 9695041322415042694730095)
      ·
        refine ⟨14542561983622564042095143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695041322415042694730095 14542561983622564042095143)
        ·
          refine ⟨21813842975433846063142715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14542561983622564042095143 21813842975433846063142715)
          ·
            refine ⟨32720764463150769094714073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21813842975433846063142715 32720764463150769094714073)
            ·
              refine ⟨24540573347363076821035555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32720764463150769094714073 24540573347363076821035555)
              ·
                refine ⟨36810860021044615231553333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24540573347363076821035555 36810860021044615231553333)
                ·
                  refine ⟨3451018126972932677958125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36810860021044615231553333 3451018126972932677958125)
                  ·
                    refine ⟨1294131797614849754234297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451018126972932677958125 1294131797614849754234297)
                    ·
                      rfl

theorem cell22_3780469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3780469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780469 prefixEnd_3780469 := by exact prefixLift 3780469
  have htrace : WordTrace (prefixWord ++ tailWord_3780469) baseStart_3780469 baseEnd_3780469 := by
    simpa [prefixWord, tailWord_3780469, baseEnd_3780469] using wordTrace_append hprefix tailTrace_3780469
  have hstable : (prefixWord ++ tailWord_3780469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780469).length < 2 ^ (prefixWord ++ tailWord_3780469).sum := by decide
  have hdescent : baseEnd_3780469 < baseStart_3780469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780503 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 1, 3]
def baseStart_3780503 : Nat := 118140960795 + 3780503 * 2 ^ 59
def prefixEnd_3780503 : Nat := 4983230072969 + 3 ^ 40 * 3780503 * 2
def baseEnd_3780503 : Nat := 1294143436509684998884193

theorem tailTrace_3780503 : CollatzResearch.WordTrace tailWord_3780503 prefixEnd_3780503 1294143436509684998884193 := by
  unfold tailWord_3780503
  simp only [CollatzResearch.WordTrace]
  refine ⟨137886272222890764354010163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91924181481927176236006775 137886272222890764354010163)
  ·
    refine ⟨206829408334336146531015245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137886272222890764354010163 206829408334336146531015245)
    ·
      refine ⟨77561028125376054949130717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206829408334336146531015245 77561028125376054949130717)
      ·
        refine ⟨29085385547016020605924019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77561028125376054949130717 29085385547016020605924019)
        ·
          refine ⟨43628078320524030908886029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29085385547016020605924019 43628078320524030908886029)
          ·
            refine ⟨16360529370196511590832261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43628078320524030908886029 16360529370196511590832261)
            ·
              refine ⟨3067599256911845923281049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16360529370196511590832261 3067599256911845923281049)
              ·
                refine ⟨2300699442683884442460787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067599256911845923281049 2300699442683884442460787)
                ·
                  refine ⟨3451049164025826663691181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300699442683884442460787 3451049164025826663691181)
                  ·
                    refine ⟨1294143436509684998884193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451049164025826663691181 1294143436509684998884193)
                    ·
                      rfl

theorem cell22_3780503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_3780503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780503 prefixEnd_3780503 := by exact prefixLift 3780503
  have htrace : WordTrace (prefixWord ++ tailWord_3780503) baseStart_3780503 baseEnd_3780503 := by
    simpa [prefixWord, tailWord_3780503, baseEnd_3780503] using wordTrace_append hprefix tailTrace_3780503
  have hstable : (prefixWord ++ tailWord_3780503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780503).length < 2 ^ (prefixWord ++ tailWord_3780503).sum := by decide
  have hdescent : baseEnd_3780503 < baseStart_3780503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780527 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 6]
def baseStart_3780527 : Nat := 118140960795 + 3780527 * 2 ^ 59
def prefixEnd_3780527 : Nat := 4983230072969 + 3 ^ 40 * 3780527 * 2
def baseEnd_3780527 : Nat := 431383884066718978761373

theorem tailTrace_3780527 : CollatzResearch.WordTrace tailWord_3780527 prefixEnd_3780527 431383884066718978761373 := by
  unfold tailWord_3780527
  simp only [CollatzResearch.WordTrace]
  refine ⟨137887147574803816452883835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91924765049869210968589223 137887147574803816452883835)
  ·
    refine ⟨206830721362205724679325753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137887147574803816452883835 206830721362205724679325753)
    ·
      refine ⟨155123041021654293509494315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206830721362205724679325753 155123041021654293509494315)
      ·
        refine ⟨232684561532481440264241473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155123041021654293509494315 232684561532481440264241473)
        ·
          refine ⟨174513421149361080198181105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232684561532481440264241473 174513421149361080198181105)
          ·
            refine ⟨130885065862020810148635829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174513421149361080198181105 130885065862020810148635829)
            ·
              refine ⟨12270474924564450951434609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130885065862020810148635829 12270474924564450951434609)
              ·
                refine ⟨9202856193423338213575957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12270474924564450951434609 9202856193423338213575957)
                ·
                  refine ⟨431383884066718978761373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9202856193423338213575957 431383884066718978761373)
                  ·
                    rfl

theorem cell22_3780527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 6].length) (baseStart_3780527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780527 prefixEnd_3780527 := by exact prefixLift 3780527
  have htrace : WordTrace (prefixWord ++ tailWord_3780527) baseStart_3780527 baseEnd_3780527 := by
    simpa [prefixWord, tailWord_3780527, baseEnd_3780527] using wordTrace_append hprefix tailTrace_3780527
  have hstable : (prefixWord ++ tailWord_3780527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780527).length < 2 ^ (prefixWord ++ tailWord_3780527).sum := by decide
  have hdescent : baseEnd_3780527 < baseStart_3780527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780529 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3780529 : Nat := 118140960795 + 3780529 * 2 ^ 59
def prefixEnd_3780529 : Nat := 4983230072969 + 3 ^ 40 * 3780529 * 2
def baseEnd_3780529 : Nat := 1294152336841029597734113

theorem tailTrace_3780529 : CollatzResearch.WordTrace tailWord_3780529 prefixEnd_3780529 1294152336841029597734113 := by
  unfold tailWord_3780529
  simp only [CollatzResearch.WordTrace]
  refine ⟨137887220520796570794456641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91924813680531047196304427 137887220520796570794456641)
  ·
    refine ⟨103415415390597428095842481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137887220520796570794456641 103415415390597428095842481)
    ·
      refine ⟨77561561542948071071881861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103415415390597428095842481 77561561542948071071881861)
      ·
        refine ⟨14542792789302763325977849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77561561542948071071881861 14542792789302763325977849)
        ·
          refine ⟨10907094591977072494483387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14542792789302763325977849 10907094591977072494483387)
          ·
            refine ⟨16360641887965608741725081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10907094591977072494483387 16360641887965608741725081)
            ·
              refine ⟨12270481415974206556293811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16360641887965608741725081 12270481415974206556293811)
              ·
                refine ⟨18405722123961309834440717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12270481415974206556293811 18405722123961309834440717)
                ·
                  refine ⟨6902145796485491187915269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18405722123961309834440717 6902145796485491187915269)
                  ·
                    refine ⟨1294152336841029597734113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6902145796485491187915269 1294152336841029597734113)
                    ·
                      rfl

theorem cell22_3780529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3780529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780529 prefixEnd_3780529 := by exact prefixLift 3780529
  have htrace : WordTrace (prefixWord ++ tailWord_3780529) baseStart_3780529 baseEnd_3780529 := by
    simpa [prefixWord, tailWord_3780529, baseEnd_3780529] using wordTrace_append hprefix tailTrace_3780529
  have hstable : (prefixWord ++ tailWord_3780529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780529).length < 2 ^ (prefixWord ++ tailWord_3780529).sum := by decide
  have hdescent : baseEnd_3780529 < baseStart_3780529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780559 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 4, 3]
def baseStart_3780559 : Nat := 118140960795 + 3780559 * 2 ^ 59
def prefixEnd_3780559 : Nat := 4983230072969 + 3 ^ 40 * 3780559 * 2
def baseEnd_3780559 : Nat := 1294162606454119519484021

theorem tailTrace_3780559 : CollatzResearch.WordTrace tailWord_3780559 prefixEnd_3780559 1294162606454119519484021 := by
  unfold tailWord_3780559
  simp only [CollatzResearch.WordTrace]
  refine ⟨137888314710687885918048731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91925543140458590612032487 137888314710687885918048731)
  ·
    refine ⟨206832472066031828877073097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137888314710687885918048731 206832472066031828877073097)
    ·
      refine ⟨155124354049523871657804823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206832472066031828877073097 155124354049523871657804823)
      ·
        refine ⟨232686531074285807486707235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155124354049523871657804823 232686531074285807486707235)
        ·
          refine ⟨349029796611428711230060853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232686531074285807486707235 349029796611428711230060853)
          ·
            refine ⟨32721543432321441677818205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349029796611428711230060853 32721543432321441677818205)
            ·
              refine ⟨12270578787120540629181827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32721543432321441677818205 12270578787120540629181827)
              ·
                refine ⟨18405868180680810943772741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12270578787120540629181827 18405868180680810943772741)
                ·
                  refine ⟨3451100283877652051957389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18405868180680810943772741 3451100283877652051957389)
                  ·
                    refine ⟨1294162606454119519484021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451100283877652051957389 1294162606454119519484021)
                    ·
                      rfl

theorem cell22_3780559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_3780559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780559 prefixEnd_3780559 := by exact prefixLift 3780559
  have htrace : WordTrace (prefixWord ++ tailWord_3780559) baseStart_3780559 baseEnd_3780559 := by
    simpa [prefixWord, tailWord_3780559, baseEnd_3780559] using wordTrace_append hprefix tailTrace_3780559
  have hstable : (prefixWord ++ tailWord_3780559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780559).length < 2 ^ (prefixWord ++ tailWord_3780559).sum := by decide
  have hdescent : baseEnd_3780559 < baseStart_3780559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780602 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_3780602 : Nat := 118140960795 + 3780602 * 2 ^ 59
def prefixEnd_3780602 : Nat := 4983230072969 + 3 ^ 40 * 3780602 * 2
def baseEnd_3780602 : Nat := 1294177326232881740658889

theorem tailTrace_3780602 : CollatzResearch.WordTrace tailWord_3780602 prefixEnd_3780602 1294177326232881740658889 := by
  unfold tailWord_3780602
  simp only [CollatzResearch.WordTrace]
  refine ⟨34472470762383026065466015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91926588699688069507909373 34472470762383026065466015)
  ·
    refine ⟨51708706143574539098199023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34472470762383026065466015 51708706143574539098199023)
    ·
      refine ⟨77563059215361808647298535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51708706143574539098199023 77563059215361808647298535)
      ·
        refine ⟨116344588823042712970947803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77563059215361808647298535 116344588823042712970947803)
        ·
          refine ⟨174516883234564069456421705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116344588823042712970947803 174516883234564069456421705)
          ·
            refine ⟨130887662425923052092316279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174516883234564069456421705 130887662425923052092316279)
            ·
              refine ⟨196331493638884578138474419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130887662425923052092316279 196331493638884578138474419)
              ·
                refine ⟨294497240458326867207711629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196331493638884578138474419 294497240458326867207711629)
                ·
                  refine ⟨110436465171872575202891861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294497240458326867207711629 110436465171872575202891861)
                  ·
                    refine ⟨1294177326232881740658889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110436465171872575202891861 1294177326232881740658889)
                    ·
                      rfl

theorem cell22_3780602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_3780602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780602 prefixEnd_3780602 := by exact prefixLift 3780602
  have htrace : WordTrace (prefixWord ++ tailWord_3780602) baseStart_3780602 baseEnd_3780602 := by
    simpa [prefixWord, tailWord_3780602, baseEnd_3780602] using wordTrace_append hprefix tailTrace_3780602
  have hstable : (prefixWord ++ tailWord_3780602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780602).length < 2 ^ (prefixWord ++ tailWord_3780602).sum := by decide
  have hdescent : baseEnd_3780602 < baseStart_3780602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780606 : List Nat := [4, 2, 2, 2, 1, 3, 8]
def baseStart_3780606 : Nat := 118140960795 + 3780606 * 2 ^ 59
def prefixEnd_3780606 : Nat := 4983230072969 + 3 ^ 40 * 3780606 * 2
def baseEnd_3780606 : Nat := 47932544278319520872551

theorem tailTrace_3780606 : CollatzResearch.WordTrace tailWord_3780606 prefixEnd_3780606 47932544278319520872551 := by
  unfold tailWord_3780606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236253617689701618126209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91926685961011741963339781 17236253617689701618126209)
  ·
    refine ⟨12927190213267276213594657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17236253617689701618126209 12927190213267276213594657)
    ·
      refine ⟨9695392659950457160195993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12927190213267276213594657 9695392659950457160195993)
      ·
        refine ⟨7271544494962842870146995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9695392659950457160195993 7271544494962842870146995)
        ·
          refine ⟨10907316742444264305220493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271544494962842870146995 10907316742444264305220493)
          ·
            refine ⟨4090243778416599114457685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10907316742444264305220493 4090243778416599114457685)
            ·
              refine ⟨47932544278319520872551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4090243778416599114457685 47932544278319520872551)
              ·
                rfl

theorem cell22_3780606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 8].length) (baseStart_3780606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780606 prefixEnd_3780606 := by exact prefixLift 3780606
  have htrace : WordTrace (prefixWord ++ tailWord_3780606) baseStart_3780606 baseEnd_3780606 := by
    simpa [prefixWord, tailWord_3780606, baseEnd_3780606] using wordTrace_append hprefix tailTrace_3780606
  have hstable : (prefixWord ++ tailWord_3780606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780606).length < 2 ^ (prefixWord ++ tailWord_3780606).sum := by decide
  have hdescent : baseEnd_3780606 < baseStart_3780606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780679 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 6]
def baseStart_3780679 : Nat := 118140960795 + 3780679 * 2 ^ 59
def prefixEnd_3780679 : Nat := 4983230072969 + 3 ^ 40 * 3780679 * 2
def baseEnd_3780679 : Nat := 431401228302159735494551

theorem tailTrace_3780679 : CollatzResearch.WordTrace tailWord_3780679 prefixEnd_3780679 431401228302159735494551 := by
  unfold tailWord_3780679
  simp only [CollatzResearch.WordTrace]
  refine ⟨137892691470253146412417091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91928460980168764274944727 137892691470253146412417091)
  ·
    refine ⟨206839037205379719618625637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137892691470253146412417091 206839037205379719618625637)
    ·
      refine ⟨38782319476008697428492307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206839037205379719618625637 38782319476008697428492307)
      ·
        refine ⟨58173479214013046142738461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38782319476008697428492307 58173479214013046142738461)
        ·
          refine ⟨21815054705254892303526923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58173479214013046142738461 21815054705254892303526923)
          ·
            refine ⟨32722582057882338455290385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21815054705254892303526923 32722582057882338455290385)
            ·
              refine ⟨24541936543411753841467789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32722582057882338455290385 24541936543411753841467789)
              ·
                refine ⟨9203226203779407690550421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24541936543411753841467789 9203226203779407690550421)
                ·
                  refine ⟨431401228302159735494551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9203226203779407690550421 431401228302159735494551)
                  ·
                    rfl

theorem cell22_3780679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 6].length) (baseStart_3780679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780679 prefixEnd_3780679 := by exact prefixLift 3780679
  have htrace : WordTrace (prefixWord ++ tailWord_3780679) baseStart_3780679 baseEnd_3780679 := by
    simpa [prefixWord, tailWord_3780679, baseEnd_3780679] using wordTrace_append hprefix tailTrace_3780679
  have hstable : (prefixWord ++ tailWord_3780679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780679).length < 2 ^ (prefixWord ++ tailWord_3780679).sum := by decide
  have hdescent : baseEnd_3780679 < baseStart_3780679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780711 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3780711 : Nat := 118140960795 + 3780711 * 2 ^ 59
def prefixEnd_3780711 : Nat := 4983230072969 + 3 ^ 40 * 3780711 * 2
def baseEnd_3780711 : Nat := 1294214639160441789683555

theorem tailTrace_3780711 : CollatzResearch.WordTrace tailWord_3780711 prefixEnd_3780711 1294214639160441789683555 := by
  unfold tailWord_3780711
  simp only [CollatzResearch.WordTrace]
  refine ⟨137893858606137215877581987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91929239070758143918387991 137893858606137215877581987)
  ·
    refine ⟨206840787909205823816372981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137893858606137215877581987 206840787909205823816372981)
    ·
      refine ⟨19391323866488045982784967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206840787909205823816372981 19391323866488045982784967)
      ·
        refine ⟨29086985799732068974177451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19391323866488045982784967 29086985799732068974177451)
        ·
          refine ⟨43630478699598103461266177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29086985799732068974177451 43630478699598103461266177)
          ·
            refine ⟨32722859024698577595949633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43630478699598103461266177 32722859024698577595949633)
            ·
              refine ⟨24542144268523933196962225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32722859024698577595949633 24542144268523933196962225)
              ·
                refine ⟨18406608201392949897721669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24542144268523933196962225 18406608201392949897721669)
                ·
                  refine ⟨3451239037761178105822813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18406608201392949897721669 3451239037761178105822813)
                  ·
                    refine ⟨1294214639160441789683555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451239037761178105822813 1294214639160441789683555)
                    ·
                      rfl

theorem cell22_3780711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3780711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780711 prefixEnd_3780711 := by exact prefixLift 3780711
  have htrace : WordTrace (prefixWord ++ tailWord_3780711) baseStart_3780711 baseEnd_3780711 := by
    simpa [prefixWord, tailWord_3780711, baseEnd_3780711] using wordTrace_append hprefix tailTrace_3780711
  have hstable : (prefixWord ++ tailWord_3780711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780711).length < 2 ^ (prefixWord ++ tailWord_3780711).sum := by decide
  have hdescent : baseEnd_3780711 < baseStart_3780711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780786 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_3780786 : Nat := 118140960795 + 3780786 * 2 ^ 59
def prefixEnd_3780786 : Nat := 4983230072969 + 3 ^ 40 * 3780786 * 2
def baseEnd_3780786 : Nat := 431413437731055531352775

theorem tailTrace_3780786 : CollatzResearch.WordTrace tailWord_3780786 prefixEnd_3780786 431413437731055531352775 := by
  unfold tailWord_3780786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34474148520216375921640553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91931062720577002457708141 34474148520216375921640553)
  ·
    refine ⟨25855611390162281941230415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34474148520216375921640553 25855611390162281941230415)
    ·
      refine ⟨38783417085243422911845623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25855611390162281941230415 38783417085243422911845623)
      ·
        refine ⟨58175125627865134367768435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38783417085243422911845623 58175125627865134367768435)
        ·
          refine ⟨87262688441797701551652653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58175125627865134367768435 87262688441797701551652653)
          ·
            refine ⟨32723508165674138081869745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87262688441797701551652653 32723508165674138081869745)
            ·
              refine ⟨24542631124255603561402309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32723508165674138081869745 24542631124255603561402309)
              ·
                refine ⟨4601743335797925667762933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24542631124255603561402309 4601743335797925667762933)
                ·
                  refine ⟨431413437731055531352775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601743335797925667762933 431413437731055531352775)
                  ·
                    rfl

theorem cell22_3780786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_3780786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780786 prefixEnd_3780786 := by exact prefixLift 3780786
  have htrace : WordTrace (prefixWord ++ tailWord_3780786) baseStart_3780786 baseEnd_3780786 := by
    simpa [prefixWord, tailWord_3780786, baseEnd_3780786] using wordTrace_append hprefix tailTrace_3780786
  have hstable : (prefixWord ++ tailWord_3780786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780786).length < 2 ^ (prefixWord ++ tailWord_3780786).sum := by decide
  have hdescent : baseEnd_3780786 < baseStart_3780786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780799 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_3780799 : Nat := 118140960795 + 3780799 * 2 ^ 59
def prefixEnd_3780799 : Nat := 4983230072969 + 3 ^ 40 * 3780799 * 2
def baseEnd_3780799 : Nat := 1294244763358838893483285

theorem tailTrace_3780799 : CollatzResearch.WordTrace tailWord_3780799 prefixEnd_3780799 1294244763358838893483285 := by
  unfold tailWord_3780799
  simp only [CollatzResearch.WordTrace]
  refine ⟨137897068229818406906785451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91931378819878937937856967 137897068229818406906785451)
  ·
    refine ⟨206845602344727610360178177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137897068229818406906785451 206845602344727610360178177)
    ·
      refine ⟨155134201758545707770133633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206845602344727610360178177 155134201758545707770133633)
      ·
        refine ⟨116350651318909280827600225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155134201758545707770133633 116350651318909280827600225)
        ·
          refine ⟨87262988489181960620700169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116350651318909280827600225 87262988489181960620700169)
          ·
            refine ⟨65447241366886470465525127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87262988489181960620700169 65447241366886470465525127)
            ·
              refine ⟨98170862050329705698287691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65447241366886470465525127 98170862050329705698287691)
              ·
                refine ⟨147256293075494558547431537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98170862050329705698287691 147256293075494558547431537)
                ·
                  refine ⟨110442219806620918910573653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147256293075494558547431537 110442219806620918910573653)
                  ·
                    refine ⟨1294244763358838893483285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110442219806620918910573653 1294244763358838893483285)
                    ·
                      rfl

theorem cell22_3780799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_3780799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780799 prefixEnd_3780799 := by exact prefixLift 3780799
  have htrace : WordTrace (prefixWord ++ tailWord_3780799) baseStart_3780799 baseEnd_3780799 := by
    simpa [prefixWord, tailWord_3780799, baseEnd_3780799] using wordTrace_append hprefix tailTrace_3780799
  have hstable : (prefixWord ++ tailWord_3780799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780799).length < 2 ^ (prefixWord ++ tailWord_3780799).sum := by decide
  have hdescent : baseEnd_3780799 < baseStart_3780799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780846 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3780846 : Nat := 118140960795 + 3780846 * 2 ^ 59
def prefixEnd_3780846 : Nat := 4983230072969 + 3 ^ 40 * 3780846 * 2
def baseEnd_3780846 : Nat := 1294260852419346437558141

theorem tailTrace_3780846 : CollatzResearch.WordTrace tailWord_3780846 prefixEnd_3780846 1294260852419346437558141 := by
  unfold tailWord_3780846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17237347807581016741718299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91932521640432089289164261 17237347807581016741718299)
  ·
    refine ⟨25856021711371525112577449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17237347807581016741718299 25856021711371525112577449)
    ·
      refine ⟨19392016283528643834433087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25856021711371525112577449 19392016283528643834433087)
      ·
        refine ⟨29088024425292965751649631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19392016283528643834433087 29088024425292965751649631)
        ·
          refine ⟨43632036637939448627474447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29088024425292965751649631 43632036637939448627474447)
          ·
            refine ⟨65448054956909172941211671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43632036637939448627474447 65448054956909172941211671)
            ·
              refine ⟨98172082435363759411817507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65448054956909172941211671 98172082435363759411817507)
              ·
                refine ⟨147258123653045639117726261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98172082435363759411817507 147258123653045639117726261)
                ·
                  refine ⟨13805449092473028667286837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147258123653045639117726261 13805449092473028667286837)
                  ·
                    refine ⟨1294260852419346437558141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13805449092473028667286837 1294260852419346437558141)
                    ·
                      rfl

theorem cell22_3780846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3780846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780846 prefixEnd_3780846 := by exact prefixLift 3780846
  have htrace : WordTrace (prefixWord ++ tailWord_3780846) baseStart_3780846 baseEnd_3780846 := by
    simpa [prefixWord, tailWord_3780846, baseEnd_3780846] using wordTrace_append hprefix tailTrace_3780846
  have hstable : (prefixWord ++ tailWord_3780846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780846).length < 2 ^ (prefixWord ++ tailWord_3780846).sum := by decide
  have hdescent : baseEnd_3780846 < baseStart_3780846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780861 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3780861 : Nat := 118140960795 + 3780861 * 2 ^ 59
def prefixEnd_3780861 : Nat := 4983230072969 + 3 ^ 40 * 3780861 * 2
def baseEnd_3780861 : Nat := 1294265987225891398433095

theorem tailTrace_3780861 : CollatzResearch.WordTrace tailWord_3780861 prefixEnd_3780861 1294265987225891398433095 := by
  unfold tailWord_3780861
  simp only [CollatzResearch.WordTrace]
  refine ⟨137899329555593791495542437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91932886370395860997028291 137899329555593791495542437)
  ·
    refine ⟨25856124291673835905414207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137899329555593791495542437 25856124291673835905414207)
    ·
      refine ⟨38784186437510753858121311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25856124291673835905414207 38784186437510753858121311)
      ·
        refine ⟨58176279656266130787181967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38784186437510753858121311 58176279656266130787181967)
        ·
          refine ⟨87264419484399196180772951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58176279656266130787181967 87264419484399196180772951)
          ·
            refine ⟨130896629226598794271159427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87264419484399196180772951 130896629226598794271159427)
            ·
              refine ⟨196344943839898191406739141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130896629226598794271159427 196344943839898191406739141)
              ·
                refine ⟨36814676969980910888763589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196344943839898191406739141 36814676969980910888763589)
                ·
                  refine ⟨6902751931871420791643173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36814676969980910888763589 6902751931871420791643173)
                  ·
                    refine ⟨1294265987225891398433095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6902751931871420791643173 1294265987225891398433095)
                    ·
                      rfl

theorem cell22_3780861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3780861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780861 prefixEnd_3780861 := by exact prefixLift 3780861
  have htrace : WordTrace (prefixWord ++ tailWord_3780861) baseStart_3780861 baseEnd_3780861 := by
    simpa [prefixWord, tailWord_3780861, baseEnd_3780861] using wordTrace_append hprefix tailTrace_3780861
  have hstable : (prefixWord ++ tailWord_3780861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780861).length < 2 ^ (prefixWord ++ tailWord_3780861).sum := by decide
  have hdescent : baseEnd_3780861 < baseStart_3780861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780863 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 2, 3]
def baseStart_3780863 : Nat := 118140960795 + 3780863 * 2 ^ 59
def prefixEnd_3780863 : Nat := 4983230072969 + 3 ^ 40 * 3780863 * 2
def baseEnd_3780863 : Nat := 1294266671866764059883089

theorem tailTrace_3780863 : CollatzResearch.WordTrace tailWord_3780863 prefixEnd_3780863 1294266671866764059883089 := by
  unfold tailWord_3780863
  simp only [CollatzResearch.WordTrace]
  refine ⟨137899402501586545837115243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91932935001057697224743495 137899402501586545837115243)
  ·
    refine ⟨206849103752379818755672865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137899402501586545837115243 206849103752379818755672865)
    ·
      refine ⟨155136827814284864066754649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206849103752379818755672865 155136827814284864066754649)
      ·
        refine ⟨116352620860713648050065987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155136827814284864066754649 116352620860713648050065987)
        ·
          refine ⟨174528931291070472075098981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116352620860713648050065987 174528931291070472075098981)
          ·
            refine ⟨32724174617075713514081059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174528931291070472075098981 32724174617075713514081059)
            ·
              refine ⟨49086261925613570271121589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32724174617075713514081059 49086261925613570271121589)
              ·
                refine ⟨4601837055526272212917649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49086261925613570271121589 4601837055526272212917649)
                ·
                  refine ⟨3451377791644704159688237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4601837055526272212917649 3451377791644704159688237)
                  ·
                    refine ⟨1294266671866764059883089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451377791644704159688237 1294266671866764059883089)
                    ·
                      rfl

theorem cell22_3780863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_3780863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780863 prefixEnd_3780863 := by exact prefixLift 3780863
  have htrace : WordTrace (prefixWord ++ tailWord_3780863) baseStart_3780863 baseEnd_3780863 := by
    simpa [prefixWord, tailWord_3780863, baseEnd_3780863] using wordTrace_append hprefix tailTrace_3780863
  have hstable : (prefixWord ++ tailWord_3780863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780863).length < 2 ^ (prefixWord ++ tailWord_3780863).sum := by decide
  have hdescent : baseEnd_3780863 < baseStart_3780863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780893 : List Nat := [1, 4, 2, 3, 2, 1, 9]
def baseStart_3780893 : Nat := 118140960795 + 3780893 * 2 ^ 59
def prefixEnd_3780893 : Nat := 4983230072969 + 3 ^ 40 * 3780893 * 2
def baseEnd_3780893 : Nat := 47936183017772369690111

theorem tailTrace_3780893 : CollatzResearch.WordTrace tailWord_3780893 prefixEnd_3780893 47936183017772369690111 := by
  unfold tailWord_3780893
  simp only [CollatzResearch.WordTrace]
  refine ⟨137900496691477860960707333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91933664460985240640471555 137900496691477860960707333)
  ·
    refine ⟨25856343129652098930132625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137900496691477860960707333 25856343129652098930132625)
    ·
      refine ⟨19392257347239074197599469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25856343129652098930132625 19392257347239074197599469)
      ·
        refine ⟨7272096505214652824099801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19392257347239074197599469 7272096505214652824099801)
        ·
          refine ⟨5454072378910989618074851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7272096505214652824099801 5454072378910989618074851)
          ·
            refine ⟨8181108568366484427112277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454072378910989618074851 8181108568366484427112277)
            ·
              refine ⟨47936183017772369690111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8181108568366484427112277 47936183017772369690111)
              ·
                rfl

theorem cell22_3780893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 9].length) (baseStart_3780893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780893 prefixEnd_3780893 := by exact prefixLift 3780893
  have htrace : WordTrace (prefixWord ++ tailWord_3780893) baseStart_3780893 baseEnd_3780893 := by
    simpa [prefixWord, tailWord_3780893, baseEnd_3780893] using wordTrace_append hprefix tailTrace_3780893
  have hstable : (prefixWord ++ tailWord_3780893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780893).length < 2 ^ (prefixWord ++ tailWord_3780893).sum := by decide
  have hdescent : baseEnd_3780893 < baseStart_3780893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780908 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_3780908 : Nat := 118140960795 + 3780908 * 2 ^ 59
def prefixEnd_3780908 : Nat := 4983230072969 + 3 ^ 40 * 3780908 * 2
def baseEnd_3780908 : Nat := 1294282076286398942507951

theorem tailTrace_3780908 : CollatzResearch.WordTrace tailWord_3780908 prefixEnd_3780908 1294282076286398942507951 := by
  unfold tailWord_3780908
  simp only [CollatzResearch.WordTrace]
  refine ⟨68950521893211759261251689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91934029190949012348335585 68950521893211759261251689)
  ·
    refine ⟨51712891419908819445938767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68950521893211759261251689 51712891419908819445938767)
    ·
      refine ⟨77569337129863229168908151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51712891419908819445938767 77569337129863229168908151)
      ·
        refine ⟨116354005694794843753362227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77569337129863229168908151 116354005694794843753362227)
        ·
          refine ⟨174531008542192265630043341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116354005694794843753362227 174531008542192265630043341)
          ·
            refine ⟨65449128203322099611266253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174531008542192265630043341 65449128203322099611266253)
            ·
              refine ⟨24543423076245787354224845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65449128203322099611266253 24543423076245787354224845)
              ·
                refine ⟨9203783653592170257834317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24543423076245787354224845 9203783653592170257834317)
                ·
                  refine ⟨3451418870097063846687869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9203783653592170257834317 3451418870097063846687869)
                  ·
                    refine ⟨1294282076286398942507951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451418870097063846687869 1294282076286398942507951)
                    ·
                      rfl

theorem cell22_3780908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_3780908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780908 prefixEnd_3780908 := by exact prefixLift 3780908
  have htrace : WordTrace (prefixWord ++ tailWord_3780908) baseStart_3780908 baseEnd_3780908 := by
    simpa [prefixWord, tailWord_3780908, baseEnd_3780908] using wordTrace_append hprefix tailTrace_3780908
  have hstable : (prefixWord ++ tailWord_3780908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780908).length < 2 ^ (prefixWord ++ tailWord_3780908).sum := by decide
  have hdescent : baseEnd_3780908 < baseStart_3780908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780936 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3780936 : Nat := 118140960795 + 3780936 * 2 ^ 59
def prefixEnd_3780936 : Nat := 4983230072969 + 3 ^ 40 * 3780936 * 2
def baseEnd_3780936 : Nat := 1294291661258616202807865

theorem tailTrace_3780936 : CollatzResearch.WordTrace tailWord_3780936 prefixEnd_3780936 1294291661258616202807865 := by
  unfold tailWord_3780936
  simp only [CollatzResearch.WordTrace]
  refine ⟨68951032515161039652261331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91934710020214719536348441 68951032515161039652261331)
  ·
    refine ⟨103426548772741559478391997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68951032515161039652261331 103426548772741559478391997)
    ·
      refine ⟨38784955789778084804396999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103426548772741559478391997 38784955789778084804396999)
      ·
        refine ⟨58177433684667127206595499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38784955789778084804396999 58177433684667127206595499)
        ·
          refine ⟨87266150527000690809893249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58177433684667127206595499 87266150527000690809893249)
          ·
            refine ⟨65449612895250518107419937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87266150527000690809893249 65449612895250518107419937)
            ·
              refine ⟨49087209671437888580564953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65449612895250518107419937 49087209671437888580564953)
              ·
                refine ⟨36815407253578416435423715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49087209671437888580564953 36815407253578416435423715)
                ·
                  refine ⟨55223110880367624653135573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36815407253578416435423715 55223110880367624653135573)
                  ·
                    refine ⟨1294291661258616202807865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55223110880367624653135573 1294291661258616202807865)
                    ·
                      rfl

theorem cell22_3780936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3780936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780936 prefixEnd_3780936 := by exact prefixLift 3780936
  have htrace : WordTrace (prefixWord ++ tailWord_3780936) baseStart_3780936 baseEnd_3780936 := by
    simpa [prefixWord, tailWord_3780936, baseEnd_3780936] using wordTrace_append hprefix tailTrace_3780936
  have hstable : (prefixWord ++ tailWord_3780936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780936).length < 2 ^ (prefixWord ++ tailWord_3780936).sum := by decide
  have hdescent : baseEnd_3780936 < baseStart_3780936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3780972 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 5]
def baseStart_3780972 : Nat := 118140960795 + 3780972 * 2 ^ 59
def prefixEnd_3780972 : Nat := 4983230072969 + 3 ^ 40 * 3780972 * 2
def baseEnd_3780972 : Nat := 431434661598108036302585

theorem tailTrace_3780972 : CollatzResearch.WordTrace tailWord_3780972 prefixEnd_3780972 431434661598108036302585 := by
  unfold tailWord_3780972
  simp only [CollatzResearch.WordTrace]
  refine ⟨68951689029095828726416585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91935585372127771635222113 68951689029095828726416585)
  ·
    refine ⟨51713766771821871544812439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68951689029095828726416585 51713766771821871544812439)
    ·
      refine ⟨77570650157732807317218659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51713766771821871544812439 77570650157732807317218659)
      ·
        refine ⟨116355975236599210975827989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77570650157732807317218659 116355975236599210975827989)
        ·
          refine ⟨5454186339215588014491937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116355975236599210975827989 5454186339215588014491937)
          ·
            refine ⟨4090639754411691010868953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5454186339215588014491937 4090639754411691010868953)
            ·
              refine ⟨3067979815808768258151715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090639754411691010868953 3067979815808768258151715)
              ·
                refine ⟨4601969723713152387227573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067979815808768258151715 4601969723713152387227573)
                ·
                  refine ⟨431434661598108036302585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601969723713152387227573 431434661598108036302585)
                  ·
                    rfl

theorem cell22_3780972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_3780972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3780972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3780972 prefixEnd_3780972 := by exact prefixLift 3780972
  have htrace : WordTrace (prefixWord ++ tailWord_3780972) baseStart_3780972 baseEnd_3780972 := by
    simpa [prefixWord, tailWord_3780972, baseEnd_3780972] using wordTrace_append hprefix tailTrace_3780972
  have hstable : (prefixWord ++ tailWord_3780972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3780972).length < 2 ^ (prefixWord ++ tailWord_3780972).sum := by decide
  have hdescent : baseEnd_3780972 < baseStart_3780972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3780972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781000 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 4]
def baseStart_3781000 : Nat := 118140960795 + 3781000 * 2 ^ 59
def prefixEnd_3781000 : Nat := 4983230072969 + 3 ^ 40 * 3781000 * 2
def baseEnd_3781000 : Nat := 431437856588847123069223

theorem tailTrace_3781000 : CollatzResearch.WordTrace tailWord_3781000 prefixEnd_3781000 431437856588847123069223 := by
  unfold tailWord_3781000
  simp only [CollatzResearch.WordTrace]
  refine ⟨68952199651045109117426227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91936266201393478823234969 68952199651045109117426227)
  ·
    refine ⟨103428299476567663676139341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68952199651045109117426227 103428299476567663676139341)
    ·
      refine ⟨38785612303712873878552253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103428299476567663676139341 38785612303712873878552253)
      ·
        refine ⟨14544604613892327704457095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38785612303712873878552253 14544604613892327704457095)
        ·
          refine ⟨21816906920838491556685643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14544604613892327704457095 21816906920838491556685643)
          ·
            refine ⟨32725360381257737335028465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21816906920838491556685643 32725360381257737335028465)
            ·
              refine ⟨24544020285943303001271349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32725360381257737335028465 24544020285943303001271349)
              ·
                refine ⟨2301001901807184656369189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24544020285943303001271349 2301001901807184656369189)
                ·
                  refine ⟨431437856588847123069223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301001901807184656369189 431437856588847123069223)
                  ·
                    rfl

theorem cell22_3781000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_3781000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781000 prefixEnd_3781000 := by exact prefixLift 3781000
  have htrace : WordTrace (prefixWord ++ tailWord_3781000) baseStart_3781000 baseEnd_3781000 := by
    simpa [prefixWord, tailWord_3781000, baseEnd_3781000] using wordTrace_append hprefix tailTrace_3781000
  have hstable : (prefixWord ++ tailWord_3781000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781000).length < 2 ^ (prefixWord ++ tailWord_3781000).sum := by decide
  have hdescent : baseEnd_3781000 < baseStart_3781000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781015 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 2, 3]
def baseStart_3781015 : Nat := 118140960795 + 3781015 * 2 ^ 59
def prefixEnd_3781015 : Nat := 4983230072969 + 3 ^ 40 * 3781015 * 2
def baseEnd_3781015 : Nat := 1294318704573086330082623

theorem tailTrace_3781015 : CollatzResearch.WordTrace tailWord_3781015 prefixEnd_3781015 1294318704573086330082623 := by
  unfold tailWord_3781015
  simp only [CollatzResearch.WordTrace]
  refine ⟨137904946397035875796648499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91936630931357250531098999 137904946397035875796648499)
  ·
    refine ⟨206857419595553813694972749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137904946397035875796648499 206857419595553813694972749)
    ·
      refine ⟨77571532348332680135614781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206857419595553813694972749 77571532348332680135614781)
      ·
        refine ⟨29089324630624755050855543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77571532348332680135614781 29089324630624755050855543)
        ·
          refine ⟨43633986945937132576283315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29089324630624755050855543 43633986945937132576283315)
          ·
            refine ⟨65450980418905698864424973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43633986945937132576283315 65450980418905698864424973)
            ·
              refine ⟨24544117657089637074159365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65450980418905698864424973 24544117657089637074159365)
              ·
                refine ⟨4602022060704306951404881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24544117657089637074159365 4602022060704306951404881)
                ·
                  refine ⟨3451516545528230213553661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4602022060704306951404881 3451516545528230213553661)
                  ·
                    refine ⟨1294318704573086330082623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451516545528230213553661 1294318704573086330082623)
                    ·
                      rfl

theorem cell22_3781015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_3781015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781015 prefixEnd_3781015 := by exact prefixLift 3781015
  have htrace : WordTrace (prefixWord ++ tailWord_3781015) baseStart_3781015 baseEnd_3781015 := by
    simpa [prefixWord, tailWord_3781015, baseEnd_3781015] using wordTrace_append hprefix tailTrace_3781015
  have hstable : (prefixWord ++ tailWord_3781015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781015).length < 2 ^ (prefixWord ++ tailWord_3781015).sum := by decide
  have hdescent : baseEnd_3781015 < baseStart_3781015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781028 : List Nat := [2, 3, 1, 2, 1, 1, 5, 7]
def baseStart_3781028 : Nat := 118140960795 + 3781028 * 2 ^ 59
def prefixEnd_3781028 : Nat := 4983230072969 + 3 ^ 40 * 3781028 * 2
def baseEnd_3781028 : Nat := 143813683859862069945287

theorem tailTrace_3781028 : CollatzResearch.WordTrace tailWord_3781028 prefixEnd_3781028 143813683859862069945287 := by
  unfold tailWord_3781028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68952710272994389508435869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91936947030659186011247825 68952710272994389508435869)
  ·
    refine ⟨25857266352372896065663451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68952710272994389508435869 25857266352372896065663451)
    ·
      refine ⟨38785899528559344098495177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25857266352372896065663451 38785899528559344098495177)
      ·
        refine ⟨29089424646419508073871383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38785899528559344098495177 29089424646419508073871383)
        ·
          refine ⟨43634136969629262110807075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29089424646419508073871383 43634136969629262110807075)
          ·
            refine ⟨65451205454443893166210613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43634136969629262110807075 65451205454443893166210613)
            ·
              refine ⟨6136050511354114984332245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65451205454443893166210613 6136050511354114984332245)
              ·
                refine ⟨143813683859862069945287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6136050511354114984332245 143813683859862069945287)
                ·
                  rfl

theorem cell22_3781028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_3781028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781028 prefixEnd_3781028 := by exact prefixLift 3781028
  have htrace : WordTrace (prefixWord ++ tailWord_3781028) baseStart_3781028 baseEnd_3781028 := by
    simpa [prefixWord, tailWord_3781028, baseEnd_3781028] using wordTrace_append hprefix tailTrace_3781028
  have hstable : (prefixWord ++ tailWord_3781028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781028).length < 2 ^ (prefixWord ++ tailWord_3781028).sum := by decide
  have hdescent : baseEnd_3781028 < baseStart_3781028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781032 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3781032 : Nat := 118140960795 + 3781032 * 2 ^ 59
def prefixEnd_3781032 : Nat := 4983230072969 + 3 ^ 40 * 3781032 * 2
def baseEnd_3781032 : Nat := 1294324524020503952407571

theorem tailTrace_3781032 : CollatzResearch.WordTrace tailWord_3781032 prefixEnd_3781032 1294324524020503952407571 := by
  unfold tailWord_3781032
  simp only [CollatzResearch.WordTrace]
  refine ⟨68952783218987143850008675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91937044291982858466678233 68952783218987143850008675)
  ·
    refine ⟨103429174828480715775013013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68952783218987143850008675 103429174828480715775013013)
    ·
      refine ⟨4848242570085033551953735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103429174828480715775013013 4848242570085033551953735)
      ·
        refine ⟨7272363855127550327930603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4848242570085033551953735 7272363855127550327930603)
        ·
          refine ⟨10908545782691325491895905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7272363855127550327930603 10908545782691325491895905)
          ·
            refine ⟨8181409337018494118921929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10908545782691325491895905 8181409337018494118921929)
            ·
              refine ⟨6136057002763870589191447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8181409337018494118921929 6136057002763870589191447)
              ·
                refine ⟨9204085504145805883787171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136057002763870589191447 9204085504145805883787171)
                ·
                  refine ⟨13806128256218708825680757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9204085504145805883787171 13806128256218708825680757)
                  ·
                    refine ⟨1294324524020503952407571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13806128256218708825680757 1294324524020503952407571)
                    ·
                      rfl

theorem cell22_3781032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3781032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781032 prefixEnd_3781032 := by exact prefixLift 3781032
  have htrace : WordTrace (prefixWord ++ tailWord_3781032) baseStart_3781032 baseEnd_3781032 := by
    simpa [prefixWord, tailWord_3781032, baseEnd_3781032] using wordTrace_append hprefix tailTrace_3781032
  have hstable : (prefixWord ++ tailWord_3781032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781032).length < 2 ^ (prefixWord ++ tailWord_3781032).sum := by decide
  have hdescent : baseEnd_3781032 < baseStart_3781032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781034 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_3781034 : Nat := 118140960795 + 3781034 * 2 ^ 59
def prefixEnd_3781034 : Nat := 4983230072969 + 3 ^ 40 * 3781034 * 2
def baseEnd_3781034 : Nat := 431441736220458871285855

theorem tailTrace_3781034 : CollatzResearch.WordTrace tailWord_3781034 prefixEnd_3781034 431441736220458871285855 := by
  unfold tailWord_3781034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34476409845991760510397539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91937092922644694694393437 34476409845991760510397539)
  ·
    refine ⟨51714614768987640765596309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34476409845991760510397539 51714614768987640765596309)
    ·
      refine ⟨2424122567296295660887327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51714614768987640765596309 2424122567296295660887327)
      ·
        refine ⟨3636183850944443491330991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424122567296295660887327 3636183850944443491330991)
        ·
          refine ⟨5454275776416665236996487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636183850944443491330991 5454275776416665236996487)
          ·
            refine ⟨8181413664624997855494731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454275776416665236996487 8181413664624997855494731)
            ·
              refine ⟨12272120496937496783242097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8181413664624997855494731 12272120496937496783242097)
              ·
                refine ⟨9204090372703122587431573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12272120496937496783242097 9204090372703122587431573)
                ·
                  refine ⟨431441736220458871285855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9204090372703122587431573 431441736220458871285855)
                  ·
                    rfl

theorem cell22_3781034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_3781034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781034 prefixEnd_3781034 := by exact prefixLift 3781034
  have htrace : WordTrace (prefixWord ++ tailWord_3781034) baseStart_3781034 baseEnd_3781034 := by
    simpa [prefixWord, tailWord_3781034, baseEnd_3781034] using wordTrace_append hprefix tailTrace_3781034
  have hstable : (prefixWord ++ tailWord_3781034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781034).length < 2 ^ (prefixWord ++ tailWord_3781034).sum := by decide
  have hdescent : baseEnd_3781034 < baseStart_3781034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781077 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_3781077 : Nat := 118140960795 + 3781077 * 2 ^ 59
def prefixEnd_3781077 : Nat := 4983230072969 + 3 ^ 40 * 3781077 * 2
def baseEnd_3781077 : Nat := 1294339928440138835032433

theorem tailTrace_3781077 : CollatzResearch.WordTrace tailWord_3781077 prefixEnd_3781077 1294339928440138835032433 := by
  unfold tailWord_3781077
  simp only [CollatzResearch.WordTrace]
  refine ⟨137907207722811260385405485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91938138481874173590270323 137907207722811260385405485)
  ·
    refine ⟨51715202896054222644527057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137907207722811260385405485 51715202896054222644527057)
    ·
      refine ⟨38786402172040666983395293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51715202896054222644527057 38786402172040666983395293)
      ·
        refine ⟨14544900814515250118773235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38786402172040666983395293 14544900814515250118773235)
        ·
          refine ⟨21817351221772875178159853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14544900814515250118773235 21817351221772875178159853)
          ·
            refine ⟨8181506708164828191809945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21817351221772875178159853 8181506708164828191809945)
            ·
              refine ⟨6136130031123621143857459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8181506708164828191809945 6136130031123621143857459)
              ·
                refine ⟨9204195046685431715786189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136130031123621143857459 9204195046685431715786189)
                ·
                  refine ⟨3451573142507036893419821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9204195046685431715786189 3451573142507036893419821)
                  ·
                    refine ⟨1294339928440138835032433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451573142507036893419821 1294339928440138835032433)
                    ·
                      rfl

theorem cell22_3781077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_3781077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781077 prefixEnd_3781077 := by exact prefixLift 3781077
  have htrace : WordTrace (prefixWord ++ tailWord_3781077) baseStart_3781077 baseEnd_3781077 := by
    simpa [prefixWord, tailWord_3781077, baseEnd_3781077] using wordTrace_append hprefix tailTrace_3781077
  have hstable : (prefixWord ++ tailWord_3781077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781077).length < 2 ^ (prefixWord ++ tailWord_3781077).sum := by decide
  have hdescent : baseEnd_3781077 < baseStart_3781077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781088 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_3781088 : Nat := 118140960795 + 3781088 * 2 ^ 59
def prefixEnd_3781088 : Nat := 4983230072969 + 3 ^ 40 * 3781088 * 2
def baseEnd_3781088 : Nat := 1294343693964938473007399

theorem tailTrace_3781088 : CollatzResearch.WordTrace tailWord_3781088 prefixEnd_3781088 1294343693964938473007399 := by
  unfold tailWord_3781088
  simp only [CollatzResearch.WordTrace]
  refine ⟨68953804462885704632027959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91938405950514272842703945 68953804462885704632027959)
  ·
    refine ⟨103430706694328556948041939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68953804462885704632027959 103430706694328556948041939)
    ·
      refine ⟨155146060041492835422062909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103430706694328556948041939 155146060041492835422062909)
      ·
        refine ⟨58179772515559813283273591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155146060041492835422062909 58179772515559813283273591)
        ·
          refine ⟨87269658773339719924910387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58179772515559813283273591 87269658773339719924910387)
          ·
            refine ⟨130904488160009579887365581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87269658773339719924910387 130904488160009579887365581)
            ·
              refine ⟨49089183060003592457762093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130904488160009579887365581 49089183060003592457762093)
              ·
                refine ⟨18408443647501347171660785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49089183060003592457762093 18408443647501347171660785)
                ·
                  refine ⟨13806332735626010378745589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18408443647501347171660785 13806332735626010378745589)
                  ·
                    refine ⟨1294343693964938473007399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13806332735626010378745589 1294343693964938473007399)
                    ·
                      rfl

theorem cell22_3781088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_3781088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781088 prefixEnd_3781088 := by exact prefixLift 3781088
  have htrace : WordTrace (prefixWord ++ tailWord_3781088) baseStart_3781088 baseEnd_3781088 := by
    simpa [prefixWord, tailWord_3781088, baseEnd_3781088] using wordTrace_append hprefix tailTrace_3781088
  have hstable : (prefixWord ++ tailWord_3781088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781088).length < 2 ^ (prefixWord ++ tailWord_3781088).sum := by decide
  have hdescent : baseEnd_3781088 < baseStart_3781088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781197 : List Nat := [1, 6, 1, 1, 2, 1, 3, 7]
def baseStart_3781197 : Nat := 118140960795 + 3781197 * 2 ^ 59
def prefixEnd_3781197 : Nat := 4983230072969 + 3 ^ 40 * 3781197 * 2
def baseEnd_3781197 : Nat := 143820111876944280225785

theorem tailTrace_3781197 : CollatzResearch.WordTrace tailWord_3781197 prefixEnd_3781197 143820111876944280225785 := by
  unfold tailWord_3781197
  simp only [CollatzResearch.WordTrace]
  refine ⟨137911584482376520879773845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91941056321584347253182563 137911584482376520879773845)
  ·
    refine ⟨6464605522611399416239399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137911584482376520879773845 6464605522611399416239399)
    ·
      refine ⟨9696908283917099124359099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6464605522611399416239399 9696908283917099124359099)
      ·
        refine ⟨14545362425875648686538649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9696908283917099124359099 14545362425875648686538649)
        ·
          refine ⟨10909021819406736514903987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14545362425875648686538649 10909021819406736514903987)
          ·
            refine ⟨16363532729110104772355981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10909021819406736514903987 16363532729110104772355981)
            ·
              refine ⟨6136324773416289289633493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16363532729110104772355981 6136324773416289289633493)
              ·
                refine ⟨143820111876944280225785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6136324773416289289633493 143820111876944280225785)
                ·
                  rfl

theorem cell22_3781197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 7].length) (baseStart_3781197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781197 prefixEnd_3781197 := by exact prefixLift 3781197
  have htrace : WordTrace (prefixWord ++ tailWord_3781197) baseStart_3781197 baseEnd_3781197 := by
    simpa [prefixWord, tailWord_3781197, baseEnd_3781197] using wordTrace_append hprefix tailTrace_3781197
  have hstable : (prefixWord ++ tailWord_3781197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781197).length < 2 ^ (prefixWord ++ tailWord_3781197).sum := by decide
  have hdescent : baseEnd_3781197 < baseStart_3781197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781285 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3781285 : Nat := 118140960795 + 3781285 * 2 ^ 59
def prefixEnd_3781285 : Nat := 4983230072969 + 3 ^ 40 * 3781285 * 2
def baseEnd_3781285 : Nat := 1294411131090895625831795

theorem tailTrace_3781285 : CollatzResearch.WordTrace tailWord_3781285 prefixEnd_3781285 1294411131090895625831795 := by
  unfold tailWord_3781285
  simp only [CollatzResearch.WordTrace]
  refine ⟨137914794106057711908977309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91943196070705141272651539 137914794106057711908977309)
  ·
    refine ⟨51718047789771641965866491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137914794106057711908977309 51718047789771641965866491)
    ·
      refine ⟨77577071684657462948799737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51718047789771641965866491 77577071684657462948799737)
      ·
        refine ⟨58182803763493097211599803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77577071684657462948799737 58182803763493097211599803)
        ·
          refine ⟨87274205645239645817399705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58182803763493097211599803 87274205645239645817399705)
          ·
            refine ⟨65455654233929734363049779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87274205645239645817399705 65455654233929734363049779)
            ·
              refine ⟨98183481350894601544574669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65455654233929734363049779 98183481350894601544574669)
              ·
                refine ⟨36818805506585475579215501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98183481350894601544574669 36818805506585475579215501)
                ·
                  refine ⟨13807052064969553342205813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36818805506585475579215501 13807052064969553342205813)
                  ·
                    refine ⟨1294411131090895625831795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13807052064969553342205813 1294411131090895625831795)
                    ·
                      rfl

theorem cell22_3781285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3781285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781285 prefixEnd_3781285 := by exact prefixLift 3781285
  have htrace : WordTrace (prefixWord ++ tailWord_3781285) baseStart_3781285 baseEnd_3781285 := by
    simpa [prefixWord, tailWord_3781285, baseEnd_3781285] using wordTrace_append hprefix tailTrace_3781285
  have hstable : (prefixWord ++ tailWord_3781285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781285).length < 2 ^ (prefixWord ++ tailWord_3781285).sum := by decide
  have hdescent : baseEnd_3781285 < baseStart_3781285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781362 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_3781362 : Nat := 118140960795 + 3781362 * 2 ^ 59
def prefixEnd_3781362 : Nat := 4983230072969 + 3 ^ 40 * 3781362 * 2
def baseEnd_3781362 : Nat := 1294437489764493091656559

theorem tailTrace_3781362 : CollatzResearch.WordTrace tailWord_3781362 prefixEnd_3781362 1294437489764493091656559 := by
  unfold tailWord_3781362
  simp only [CollatzResearch.WordTrace]
  refine ⟨34479400631694688514882585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91945068351185836039686893 34479400631694688514882585)
  ·
    refine ⟨25859550473771016386161939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34479400631694688514882585 25859550473771016386161939)
    ·
      refine ⟨38789325710656524579242909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25859550473771016386161939 38789325710656524579242909)
      ·
        refine ⟨14545997141496196717216091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38789325710656524579242909 14545997141496196717216091)
        ·
          refine ⟨21818995712244295075824137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14545997141496196717216091 21818995712244295075824137)
          ·
            refine ⟨16364246784183221306868103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21818995712244295075824137 16364246784183221306868103)
            ·
              refine ⟨24546370176274831960302155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16364246784183221306868103 24546370176274831960302155)
              ·
                refine ⟨36819555264412247940453233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24546370176274831960302155 36819555264412247940453233)
                ·
                  refine ⟨27614666448309185955339925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36819555264412247940453233 27614666448309185955339925)
                  ·
                    refine ⟨1294437489764493091656559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27614666448309185955339925 1294437489764493091656559)
                    ·
                      rfl

theorem cell22_3781362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_3781362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781362 prefixEnd_3781362 := by exact prefixLift 3781362
  have htrace : WordTrace (prefixWord ++ tailWord_3781362) baseStart_3781362 baseEnd_3781362 := by
    simpa [prefixWord, tailWord_3781362, baseEnd_3781362] using wordTrace_append hprefix tailTrace_3781362
  have hstable : (prefixWord ++ tailWord_3781362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781362).length < 2 ^ (prefixWord ++ tailWord_3781362).sum := by decide
  have hdescent : baseEnd_3781362 < baseStart_3781362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781428 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3781428 : Nat := 118140960795 + 3781428 * 2 ^ 59
def prefixEnd_3781428 : Nat := 4983230072969 + 3 ^ 40 * 3781428 * 2
def baseEnd_3781428 : Nat := 431486694304430306502119

theorem tailTrace_3781428 : CollatzResearch.WordTrace tailWord_3781428 prefixEnd_3781428 431486694304430306502119 := by
  unfold tailWord_3781428
  simp only [CollatzResearch.WordTrace]
  refine ⟨68960004872269823665716469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91946673163026431554288625 68960004872269823665716469)
  ·
    refine ⟨6465000456775295968660919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68960004872269823665716469 6465000456775295968660919)
    ·
      refine ⟨9697500685162943952991379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6465000456775295968660919 9697500685162943952991379)
      ·
        refine ⟨14546251027744415929487069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9697500685162943952991379 14546251027744415929487069)
        ·
          refine ⟨5454844135404155973557651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14546251027744415929487069 5454844135404155973557651)
          ·
            refine ⟨8182266203106233960336477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454844135404155973557651 8182266203106233960336477)
            ·
              refine ⟨3068349826164837735126179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8182266203106233960336477 3068349826164837735126179)
              ·
                refine ⟨4602524739247256602689269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068349826164837735126179 4602524739247256602689269)
                ·
                  refine ⟨431486694304430306502119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4602524739247256602689269 431486694304430306502119)
                  ·
                    rfl

theorem cell22_3781428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3781428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781428 prefixEnd_3781428 := by exact prefixLift 3781428
  have htrace : WordTrace (prefixWord ++ tailWord_3781428) baseStart_3781428 baseEnd_3781428 := by
    simpa [prefixWord, tailWord_3781428, baseEnd_3781428] using wordTrace_append hprefix tailTrace_3781428
  have hstable : (prefixWord ++ tailWord_3781428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781428).length < 2 ^ (prefixWord ++ tailWord_3781428).sum := by decide
  have hdescent : baseEnd_3781428 < baseStart_3781428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781499 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 3, 3]
def baseStart_3781499 : Nat := 118140960795 + 3781499 * 2 ^ 59
def prefixEnd_3781499 : Nat := 4983230072969 + 3 ^ 40 * 3781499 * 2
def baseEnd_3781499 : Nat := 1294484387664270400981139

theorem tailTrace_3781499 : CollatzResearch.WordTrace tailWord_3781499 prefixEnd_3781499 1294484387664270400981139 := by
  unfold tailWord_3781499
  simp only [CollatzResearch.WordTrace]
  refine ⟨137922599327282426457267551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91948399551521617638178367 137922599327282426457267551)
  ·
    refine ⟨206883898990923639685901327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137922599327282426457267551 206883898990923639685901327)
    ·
      refine ⟨310325848486385459528851991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206883898990923639685901327 310325848486385459528851991)
      ·
        refine ⟨465488772729578189293277987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310325848486385459528851991 465488772729578189293277987)
        ·
          refine ⟨698233159094367283939916981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465488772729578189293277987 698233159094367283939916981)
          ·
            refine ⟨65459358665096932869367217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 698233159094367283939916981 65459358665096932869367217)
            ·
              refine ⟨49094518998822699652025413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65459358665096932869367217 49094518998822699652025413)
              ·
                refine ⟨9205222312279256184754765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49094518998822699652025413 9205222312279256184754765)
                ·
                  refine ⟨3451958367104721069283037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9205222312279256184754765 3451958367104721069283037)
                  ·
                    refine ⟨1294484387664270400981139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451958367104721069283037 1294484387664270400981139)
                    ·
                      rfl

theorem cell22_3781499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 3].length) (baseStart_3781499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781499 prefixEnd_3781499 := by exact prefixLift 3781499
  have htrace : WordTrace (prefixWord ++ tailWord_3781499) baseStart_3781499 baseEnd_3781499 := by
    simpa [prefixWord, tailWord_3781499, baseEnd_3781499] using wordTrace_append hprefix tailTrace_3781499
  have hstable : (prefixWord ++ tailWord_3781499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781499).length < 2 ^ (prefixWord ++ tailWord_3781499).sum := by decide
  have hdescent : baseEnd_3781499 < baseStart_3781499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781533 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3781533 : Nat := 118140960795 + 3781533 * 2 ^ 59
def prefixEnd_3781533 : Nat := 4983230072969 + 3 ^ 40 * 3781533 * 2
def baseEnd_3781533 : Nat := 1294496026559105645631035

theorem tailTrace_3781533 : CollatzResearch.WordTrace tailWord_3781533 prefixEnd_3781533 1294496026559105645631035 := by
  unfold tailWord_3781533
  simp only [CollatzResearch.WordTrace]
  refine ⟨137923839409159250264005253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91949226272772833509336835 137923839409159250264005253)
  ·
    refine ⟨25860719889217359424500985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137923839409159250264005253 25860719889217359424500985)
    ·
      refine ⟨19395539916913019568375739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25860719889217359424500985 19395539916913019568375739)
      ·
        refine ⟨29093309875369529352563609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19395539916913019568375739 29093309875369529352563609)
        ·
          refine ⟨21819982406527147014422707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29093309875369529352563609 21819982406527147014422707)
          ·
            refine ⟨32729973609790720521634061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21819982406527147014422707 32729973609790720521634061)
            ·
              refine ⟨12273740103671520195612773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32729973609790720521634061 12273740103671520195612773)
              ·
                refine ⟨2301326269438410036677395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12273740103671520195612773 2301326269438410036677395)
                ·
                  refine ⟨3451989404157615055016093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301326269438410036677395 3451989404157615055016093)
                  ·
                    refine ⟨1294496026559105645631035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3451989404157615055016093 1294496026559105645631035)
                    ·
                      rfl

theorem cell22_3781533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3781533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781533 prefixEnd_3781533 := by exact prefixLift 3781533
  have htrace : WordTrace (prefixWord ++ tailWord_3781533) baseStart_3781533 baseEnd_3781533 := by
    simpa [prefixWord, tailWord_3781533, baseEnd_3781533] using wordTrace_append hprefix tailTrace_3781533
  have hstable : (prefixWord ++ tailWord_3781533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781533).length < 2 ^ (prefixWord ++ tailWord_3781533).sum := by decide
  have hdescent : baseEnd_3781533 < baseStart_3781533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781559 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 3, 4]
def baseStart_3781559 : Nat := 118140960795 + 3781559 * 2 ^ 59
def prefixEnd_3781559 : Nat := 4983230072969 + 3 ^ 40 * 3781559 * 2
def baseEnd_3781559 : Nat := 1294504926890450244480955

theorem tailTrace_3781559 : CollatzResearch.WordTrace tailWord_3781559 prefixEnd_3781559 1294504926890450244480955 := by
  unfold tailWord_3781559
  simp only [CollatzResearch.WordTrace]
  refine ⟨137924787707065056704451731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91949858471376704469634487 137924787707065056704451731)
  ·
    refine ⟨206887181560597585056677597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137924787707065056704451731 206887181560597585056677597)
    ·
      refine ⟨77582693085224094396254099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206887181560597585056677597 77582693085224094396254099)
      ·
        refine ⟨116374039627836141594381149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77582693085224094396254099 116374039627836141594381149)
        ·
          refine ⟨43640264860438553097892931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116374039627836141594381149 43640264860438553097892931)
          ·
            refine ⟨65460397290657829646839397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43640264860438553097892931 65460397290657829646839397)
            ·
              refine ⟨12273824491998343058782387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65460397290657829646839397 12273824491998343058782387)
              ·
                refine ⟨18410736737997514588173581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12273824491998343058782387 18410736737997514588173581)
                ·
                  refine ⟨6904026276749067970565093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18410736737997514588173581 6904026276749067970565093)
                  ·
                    refine ⟨1294504926890450244480955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6904026276749067970565093 1294504926890450244480955)
                    ·
                      rfl

theorem cell22_3781559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_3781559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781559 prefixEnd_3781559 := by exact prefixLift 3781559
  have htrace : WordTrace (prefixWord ++ tailWord_3781559) baseStart_3781559 baseEnd_3781559 := by
    simpa [prefixWord, tailWord_3781559, baseEnd_3781559] using wordTrace_append hprefix tailTrace_3781559
  have hstable : (prefixWord ++ tailWord_3781559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781559).length < 2 ^ (prefixWord ++ tailWord_3781559).sum := by decide
  have hdescent : baseEnd_3781559 < baseStart_3781559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781604 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3781604 : Nat := 118140960795 + 3781604 * 2 ^ 59
def prefixEnd_3781604 : Nat := 4983230072969 + 3 ^ 40 * 3781604 * 2
def baseEnd_3781604 : Nat := 1294520331310085127105817

theorem tailTrace_3781604 : CollatzResearch.WordTrace tailWord_3781604 prefixEnd_3781604 1294520331310085127105817 := by
  unfold tailWord_3781604
  simp only [CollatzResearch.WordTrace]
  refine ⟨68963214495951014694919933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91950952661268019593226577 68963214495951014694919933)
  ·
    refine ⟨25861205435981630510594975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68963214495951014694919933 25861205435981630510594975)
    ·
      refine ⟨38791808153972445765892463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25861205435981630510594975 38791808153972445765892463)
      ·
        refine ⟨58187712230958668648838695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38791808153972445765892463 58187712230958668648838695)
        ·
          refine ⟨87281568346438002973258043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58187712230958668648838695 87281568346438002973258043)
          ·
            refine ⟨130922352519657004459887065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87281568346438002973258043 130922352519657004459887065)
            ·
              refine ⟨98191764389742753344915299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130922352519657004459887065 98191764389742753344915299)
              ·
                refine ⟨147287646584614130017372949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98191764389742753344915299 147287646584614130017372949)
                ·
                  refine ⟨6904108433653787344564357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147287646584614130017372949 6904108433653787344564357)
                  ·
                    refine ⟨1294520331310085127105817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6904108433653787344564357 1294520331310085127105817)
                    ·
                      rfl

theorem cell22_3781604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3781604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781604 prefixEnd_3781604 := by exact prefixLift 3781604
  have htrace : WordTrace (prefixWord ++ tailWord_3781604) baseStart_3781604 baseEnd_3781604 := by
    simpa [prefixWord, tailWord_3781604, baseEnd_3781604] using wordTrace_append hprefix tailTrace_3781604
  have hstable : (prefixWord ++ tailWord_3781604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781604).length < 2 ^ (prefixWord ++ tailWord_3781604).sum := by decide
  have hdescent : baseEnd_3781604 < baseStart_3781604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781743 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 4]
def baseStart_3781743 : Nat := 118140960795 + 3781743 * 2 ^ 59
def prefixEnd_3781743 : Nat := 4983230072969 + 3 ^ 40 * 3781743 * 2
def baseEnd_3781743 : Nat := 431522637950245032626797

theorem tailTrace_3781743 : CollatzResearch.WordTrace tailWord_3781743 prefixEnd_3781743 431522637950245032626797 := by
  unfold tailWord_3781743
  simp only [CollatzResearch.WordTrace]
  refine ⟨137931498738398456129149883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91954332492265637419433255 137931498738398456129149883)
  ·
    refine ⟨206897248107597684193724825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137931498738398456129149883 206897248107597684193724825)
    ·
      refine ⟨155172936080698263145293619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206897248107597684193724825 155172936080698263145293619)
      ·
        refine ⟨232759404121047394717940429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155172936080698263145293619 232759404121047394717940429)
        ·
          refine ⟨87284776545392773019227661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232759404121047394717940429 87284776545392773019227661)
          ·
            refine ⟨32731791204522289882210373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87284776545392773019227661 32731791204522289882210373)
            ·
              refine ⟨6137210850847929352914445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32731791204522289882210373 6137210850847929352914445)
              ·
                refine ⟨2301454069067973507342917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6137210850847929352914445 2301454069067973507342917)
                ·
                  refine ⟨431522637950245032626797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301454069067973507342917 431522637950245032626797)
                  ·
                    rfl

theorem cell22_3781743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 4].length) (baseStart_3781743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781743 prefixEnd_3781743 := by exact prefixLift 3781743
  have htrace : WordTrace (prefixWord ++ tailWord_3781743) baseStart_3781743 baseEnd_3781743 := by
    simpa [prefixWord, tailWord_3781743, baseEnd_3781743] using wordTrace_append hprefix tailTrace_3781743
  have hstable : (prefixWord ++ tailWord_3781743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781743).length < 2 ^ (prefixWord ++ tailWord_3781743).sum := by decide
  have hdescent : baseEnd_3781743 < baseStart_3781743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781756 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_3781756 : Nat := 118140960795 + 3781756 * 2 ^ 59
def prefixEnd_3781756 : Nat := 4983230072969 + 3 ^ 40 * 3781756 * 2
def baseEnd_3781756 : Nat := 1294572364016407397305351

theorem tailTrace_3781756 : CollatzResearch.WordTrace tailWord_3781756 prefixEnd_3781756 1294572364016407397305351 := by
  unfold tailWord_3781756
  simp only [CollatzResearch.WordTrace]
  refine ⟨68965986443675679674686561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91954648591567572899582081 68965986443675679674686561)
  ·
    refine ⟨51724489832756759756014921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68965986443675679674686561 51724489832756759756014921)
    ·
      refine ⟨38793367374567569817011191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51724489832756759756014921 38793367374567569817011191)
      ·
        refine ⟨58190051061851354725516787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38793367374567569817011191 58190051061851354725516787)
        ·
          refine ⟨87285076592777032088275181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58190051061851354725516787 87285076592777032088275181)
          ·
            refine ⟨32731903722291387033103193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87285076592777032088275181 32731903722291387033103193)
            ·
              refine ⟨24548927791718540274827395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32731903722291387033103193 24548927791718540274827395)
              ·
                refine ⟨36823391687577810412241093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24548927791718540274827395 36823391687577810412241093)
                ·
                  refine ⟨6904385941420839452295205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36823391687577810412241093 6904385941420839452295205)
                  ·
                    refine ⟨1294572364016407397305351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6904385941420839452295205 1294572364016407397305351)
                    ·
                      rfl

theorem cell22_3781756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_3781756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781756 prefixEnd_3781756 := by exact prefixLift 3781756
  have htrace : WordTrace (prefixWord ++ tailWord_3781756) baseStart_3781756 baseEnd_3781756 := by
    simpa [prefixWord, tailWord_3781756, baseEnd_3781756] using wordTrace_append hprefix tailTrace_3781756
  have hstable : (prefixWord ++ tailWord_3781756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781756).length < 2 ^ (prefixWord ++ tailWord_3781756).sum := by decide
  have hdescent : baseEnd_3781756 < baseStart_3781756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781788 : List Nat := [2, 2, 3, 2, 1, 2, 4, 6]
def baseStart_3781788 : Nat := 118140960795 + 3781788 * 2 ^ 59
def prefixEnd_3781788 : Nat := 4983230072969 + 3 ^ 40 * 3781788 * 2
def baseEnd_3781788 : Nat := 143842590918929997833917

theorem tailTrace_3781788 : CollatzResearch.WordTrace tailWord_3781788 prefixEnd_3781788 143842590918929997833917 := by
  unfold tailWord_3781788
  simp only [CollatzResearch.WordTrace]
  refine ⟨68966570011617714407269009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91955426682156952543025345 68966570011617714407269009)
  ·
    refine ⟨51724927508713285805451757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68966570011617714407269009 51724927508713285805451757)
    ·
      refine ⟨19396847815767482177044409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51724927508713285805451757 19396847815767482177044409)
      ·
        refine ⟨14547635861825611632783307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19396847815767482177044409 14547635861825611632783307)
        ·
          refine ⟨21821453792738417449174961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14547635861825611632783307 21821453792738417449174961)
          ·
            refine ⟨16366090344553813086881221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21821453792738417449174961 16366090344553813086881221)
            ·
              refine ⟨3068641939603839953790229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16366090344553813086881221 3068641939603839953790229)
              ·
                refine ⟨143842590918929997833917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3068641939603839953790229 143842590918929997833917)
                ·
                  rfl

theorem cell22_3781788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 6].length) (baseStart_3781788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781788 prefixEnd_3781788 := by exact prefixLift 3781788
  have htrace : WordTrace (prefixWord ++ tailWord_3781788) baseStart_3781788 baseEnd_3781788 := by
    simpa [prefixWord, tailWord_3781788, baseEnd_3781788] using wordTrace_append hprefix tailTrace_3781788
  have hstable : (prefixWord ++ tailWord_3781788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781788).length < 2 ^ (prefixWord ++ tailWord_3781788).sum := by decide
  have hdescent : baseEnd_3781788 < baseStart_3781788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781794 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3781794 : Nat := 118140960795 + 3781794 * 2 ^ 59
def prefixEnd_3781794 : Nat := 4983230072969 + 3 ^ 40 * 3781794 * 2
def baseEnd_3781794 : Nat := 431528457397662654951745

theorem tailTrace_3781794 : CollatzResearch.WordTrace tailWord_3781794 prefixEnd_3781794 431528457397662654951745 := by
  unfold tailWord_3781794
  simp only [CollatzResearch.WordTrace]
  refine ⟨34483339715303422959814109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91955572574142461226170957 34483339715303422959814109)
  ·
    refine ⟨12931252393238783609930291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34483339715303422959814109 12931252393238783609930291)
    ·
      refine ⟨19396878589858175414895437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12931252393238783609930291 19396878589858175414895437)
      ·
        refine ⟨7273829471196815780585789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19396878589858175414895437 7273829471196815780585789)
        ·
          refine ⟨2727686051698805917719671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7273829471196815780585789 2727686051698805917719671)
          ·
            refine ⟨4091529077548208876579507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727686051698805917719671 4091529077548208876579507)
            ·
              refine ⟨6137293616322313314869261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091529077548208876579507 6137293616322313314869261)
              ·
                refine ⟨2301485106120867493075973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6137293616322313314869261 2301485106120867493075973)
                ·
                  refine ⟨431528457397662654951745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301485106120867493075973 431528457397662654951745)
                  ·
                    rfl

theorem cell22_3781794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3781794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781794 prefixEnd_3781794 := by exact prefixLift 3781794
  have htrace : WordTrace (prefixWord ++ tailWord_3781794) baseStart_3781794 baseEnd_3781794 := by
    simpa [prefixWord, tailWord_3781794, baseEnd_3781794] using wordTrace_append hprefix tailTrace_3781794
  have hstable : (prefixWord ++ tailWord_3781794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781794).length < 2 ^ (prefixWord ++ tailWord_3781794).sum := by decide
  have hdescent : baseEnd_3781794 < baseStart_3781794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781805 : List Nat := [1, 5, 2, 1, 4, 1, 8]
def baseStart_3781805 : Nat := 118140960795 + 3781805 * 2 ^ 59
def prefixEnd_3781805 : Nat := 4983230072969 + 3 ^ 40 * 3781805 * 2
def baseEnd_3781805 : Nat := 47947745841399540845563

theorem tailTrace_3781805 : CollatzResearch.WordTrace tailWord_3781805 prefixEnd_3781805 47947745841399540845563 := by
  unfold tailWord_3781805
  simp only [CollatzResearch.WordTrace]
  refine ⟨137933760064173840717906869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91955840042782560478604579 137933760064173840717906869)
  ·
    refine ⟨12931290006016297567303769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137933760064173840717906869 12931290006016297567303769)
    ·
      refine ⟨9698467504512223175477827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12931290006016297567303769 9698467504512223175477827)
      ·
        refine ⟨14547701256768334763216741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9698467504512223175477827 14547701256768334763216741)
        ·
          refine ⟨2727693985644062768103139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14547701256768334763216741 2727693985644062768103139)
          ·
            refine ⟨4091540978466094152154709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727693985644062768103139 4091540978466094152154709)
            ·
              refine ⟨47947745841399540845563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4091540978466094152154709 47947745841399540845563)
              ·
                rfl

theorem cell22_3781805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 8].length) (baseStart_3781805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781805 prefixEnd_3781805 := by exact prefixLift 3781805
  have htrace : WordTrace (prefixWord ++ tailWord_3781805) baseStart_3781805 baseEnd_3781805 := by
    simpa [prefixWord, tailWord_3781805, baseEnd_3781805] using wordTrace_append hprefix tailTrace_3781805
  have hstable : (prefixWord ++ tailWord_3781805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781805).length < 2 ^ (prefixWord ++ tailWord_3781805).sum := by decide
  have hdescent : baseEnd_3781805 < baseStart_3781805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781820 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_3781820 : Nat := 118140960795 + 3781820 * 2 ^ 59
def prefixEnd_3781820 : Nat := 4983230072969 + 3 ^ 40 * 3781820 * 2
def baseEnd_3781820 : Nat := 1294594272524332563705155

theorem tailTrace_3781820 : CollatzResearch.WordTrace tailWord_3781820 prefixEnd_3781820 1294594272524332563705155 := by
  unfold tailWord_3781820
  simp only [CollatzResearch.WordTrace]
  refine ⟨68967153579559749139851457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91956204772746332186468609 68967153579559749139851457)
  ·
    refine ⟨51725365184669811854888593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68967153579559749139851457 51725365184669811854888593)
    ·
      refine ⟨38794023888502358891166445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51725365184669811854888593 38794023888502358891166445)
      ·
        refine ⟨14547758958188384584187417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38794023888502358891166445 14547758958188384584187417)
        ·
          refine ⟨10910819218641288438140563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14547758958188384584187417 10910819218641288438140563)
          ·
            refine ⟨16366228827961932657210845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10910819218641288438140563 16366228827961932657210845)
            ·
              refine ⟨6137335810485724746454067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16366228827961932657210845 6137335810485724746454067)
              ·
                refine ⟨9206003715728587119681101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137335810485724746454067 9206003715728587119681101)
                ·
                  refine ⟨3452251393398220169880413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9206003715728587119681101 3452251393398220169880413)
                  ·
                    refine ⟨1294594272524332563705155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452251393398220169880413 1294594272524332563705155)
                    ·
                      rfl

theorem cell22_3781820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_3781820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781820 prefixEnd_3781820 := by exact prefixLift 3781820
  have htrace : WordTrace (prefixWord ++ tailWord_3781820) baseStart_3781820 baseEnd_3781820 := by
    simpa [prefixWord, tailWord_3781820, baseEnd_3781820] using wordTrace_append hprefix tailTrace_3781820
  have hstable : (prefixWord ++ tailWord_3781820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781820).length < 2 ^ (prefixWord ++ tailWord_3781820).sum := by decide
  have hdescent : baseEnd_3781820 < baseStart_3781820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781831 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3781831 : Nat := 118140960795 + 3781831 * 2 ^ 59
def prefixEnd_3781831 : Nat := 4983230072969 + 3 ^ 40 * 3781831 * 2
def baseEnd_3781831 : Nat := 1294598038049132201680121

theorem tailTrace_3781831 : CollatzResearch.WordTrace tailWord_3781831 prefixEnd_3781831 1294598038049132201680121 := by
  unfold tailWord_3781831
  simp only [CollatzResearch.WordTrace]
  refine ⟨137934708362079647158353347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91956472241386431438902231 137934708362079647158353347)
  ·
    refine ⟨206902062543119470737530021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137934708362079647158353347 206902062543119470737530021)
    ·
      refine ⟨38794136726834900763286879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206902062543119470737530021 38794136726834900763286879)
      ·
        refine ⟨58191205090252351144930319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38794136726834900763286879 58191205090252351144930319)
        ·
          refine ⟨87286807635378526717395479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58191205090252351144930319 87286807635378526717395479)
          ·
            refine ⟨130930211453067790076093219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87286807635378526717395479 130930211453067790076093219)
            ·
              refine ⟨196395317179601685114139829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130930211453067790076093219 196395317179601685114139829)
              ·
                refine ⟨18412060985587657979450609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196395317179601685114139829 18412060985587657979450609)
                ·
                  refine ⟨13809045739190743484587957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18412060985587657979450609 13809045739190743484587957)
                  ·
                    refine ⟨1294598038049132201680121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13809045739190743484587957 1294598038049132201680121)
                    ·
                      rfl

theorem cell22_3781831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3781831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781831 prefixEnd_3781831 := by exact prefixLift 3781831
  have htrace : WordTrace (prefixWord ++ tailWord_3781831) baseStart_3781831 baseEnd_3781831 := by
    simpa [prefixWord, tailWord_3781831, baseEnd_3781831] using wordTrace_append hprefix tailTrace_3781831
  have hstable : (prefixWord ++ tailWord_3781831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781831).length < 2 ^ (prefixWord ++ tailWord_3781831).sum := by decide
  have hdescent : baseEnd_3781831 < baseStart_3781831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781871 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 1, 3]
def baseStart_3781871 : Nat := 118140960795 + 3781871 * 2 ^ 59
def prefixEnd_3781871 : Nat := 4983230072969 + 3 ^ 40 * 3781871 * 2
def baseEnd_3781871 : Nat := 1294611730866585430679999

theorem tailTrace_3781871 : CollatzResearch.WordTrace tailWord_3781871 prefixEnd_3781871 1294611730866585430679999 := by
  unfold tailWord_3781871
  simp only [CollatzResearch.WordTrace]
  refine ⟨137936167281934733989809467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91957444854623155993206311 137936167281934733989809467)
  ·
    refine ⟨206904250922902100984714201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137936167281934733989809467 206904250922902100984714201)
    ·
      refine ⟨155178188192176575738535651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206904250922902100984714201 155178188192176575738535651)
      ·
        refine ⟨232767282288264863607803477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155178188192176575738535651 232767282288264863607803477)
        ·
          refine ⟨2727741589315603870403947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 232767282288264863607803477 2727741589315603870403947)
          ·
            refine ⟨4091612383973405805605921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727741589315603870403947 4091612383973405805605921)
            ·
              refine ⟨3068709287980054354204441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091612383973405805605921 3068709287980054354204441)
              ·
                refine ⟨2301531965985040765653331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068709287980054354204441 2301531965985040765653331)
                ·
                  refine ⟨3452297948977561148479997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301531965985040765653331 3452297948977561148479997)
                  ·
                    refine ⟨1294611730866585430679999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452297948977561148479997 1294611730866585430679999)
                    ·
                      rfl

theorem cell22_3781871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_3781871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781871 prefixEnd_3781871 := by exact prefixLift 3781871
  have htrace : WordTrace (prefixWord ++ tailWord_3781871) baseStart_3781871 baseEnd_3781871 := by
    simpa [prefixWord, tailWord_3781871, baseEnd_3781871] using wordTrace_append hprefix tailTrace_3781871
  have hstable : (prefixWord ++ tailWord_3781871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781871).length < 2 ^ (prefixWord ++ tailWord_3781871).sum := by decide
  have hdescent : baseEnd_3781871 < baseStart_3781871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781878 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_3781878 : Nat := 118140960795 + 3781878 * 2 ^ 59
def prefixEnd_3781878 : Nat := 4983230072969 + 3 ^ 40 * 3781878 * 2
def baseEnd_3781878 : Nat := 431538042369879915251659

theorem tailTrace_3781878 : CollatzResearch.WordTrace tailWord_3781878 prefixEnd_3781878 431538042369879915251659 := by
  unfold tailWord_3781878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621026412056835886582143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91957615061939582790209525 8621026412056835886582143)
  ·
    refine ⟨12931539618085253829873215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8621026412056835886582143 12931539618085253829873215)
    ·
      refine ⟨19397309427127880744809823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12931539618085253829873215 19397309427127880744809823)
      ·
        refine ⟨29095964140691821117214735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19397309427127880744809823 29095964140691821117214735)
        ·
          refine ⟨43643946211037731675822103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29095964140691821117214735 43643946211037731675822103)
          ·
            refine ⟨65465919316556597513733155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43643946211037731675822103 65465919316556597513733155)
            ·
              refine ⟨98198878974834896270599733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65465919316556597513733155 98198878974834896270599733)
              ·
                refine ⟨9206144903890771525368725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98198878974834896270599733 9206144903890771525368725)
                ·
                  refine ⟨431538042369879915251659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9206144903890771525368725 431538042369879915251659)
                  ·
                    rfl

theorem cell22_3781878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_3781878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781878 prefixEnd_3781878 := by exact prefixLift 3781878
  have htrace : WordTrace (prefixWord ++ tailWord_3781878) baseStart_3781878 baseEnd_3781878 := by
    simpa [prefixWord, tailWord_3781878, baseEnd_3781878] using wordTrace_append hprefix tailTrace_3781878
  have hstable : (prefixWord ++ tailWord_3781878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781878).length < 2 ^ (prefixWord ++ tailWord_3781878).sum := by decide
  have hdescent : baseEnd_3781878 < baseStart_3781878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781893 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_3781893 : Nat := 118140960795 + 3781893 * 2 ^ 59
def prefixEnd_3781893 : Nat := 4983230072969 + 3 ^ 40 * 3781893 * 2
def baseEnd_3781893 : Nat := 1294619261916184706629931

theorem tailTrace_3781893 : CollatzResearch.WordTrace tailWord_3781893 prefixEnd_3781893 1294619261916184706629931 := by
  unfold tailWord_3781893
  simp only [CollatzResearch.WordTrace]
  refine ⟨137936969687855031747110333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91957979791903354498073555 137936969687855031747110333)
  ·
    refine ⟨51726363632945636905166375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137936969687855031747110333 51726363632945636905166375)
    ·
      refine ⟨77589545449418455357749563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51726363632945636905166375 77589545449418455357749563)
      ·
        refine ⟨116384318174127683036624345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77589545449418455357749563 116384318174127683036624345)
        ·
          refine ⟨87288238630595762277468259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116384318174127683036624345 87288238630595762277468259)
          ·
            refine ⟨130932357945893643416202389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87288238630595762277468259 130932357945893643416202389)
            ·
              refine ⟨6137454278713764535134487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130932357945893643416202389 6137454278713764535134487)
              ·
                refine ⟨9206181418070646802701731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137454278713764535134487 9206181418070646802701731)
                ·
                  refine ⟨13809272127105970204052597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206181418070646802701731 13809272127105970204052597)
                  ·
                    refine ⟨1294619261916184706629931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13809272127105970204052597 1294619261916184706629931)
                    ·
                      rfl

theorem cell22_3781893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_3781893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781893 prefixEnd_3781893 := by exact prefixLift 3781893
  have htrace : WordTrace (prefixWord ++ tailWord_3781893) baseStart_3781893 baseEnd_3781893 := by
    simpa [prefixWord, tailWord_3781893, baseEnd_3781893] using wordTrace_append hprefix tailTrace_3781893
  have hstable : (prefixWord ++ tailWord_3781893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781893).length < 2 ^ (prefixWord ++ tailWord_3781893).sum := by decide
  have hdescent : baseEnd_3781893 < baseStart_3781893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3781989 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_3781989 : Nat := 118140960795 + 3781989 * 2 ^ 59
def prefixEnd_3781989 : Nat := 4983230072969 + 3 ^ 40 * 3781989 * 2
def baseEnd_3781989 : Nat := 1294652124678072456229637

theorem tailTrace_3781989 : CollatzResearch.WordTrace tailWord_3781989 prefixEnd_3781989 1294652124678072456229637 := by
  unfold tailWord_3781989
  simp only [CollatzResearch.WordTrace]
  refine ⟨137940471095507240142605021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91960314063671493428403347 137940471095507240142605021)
  ·
    refine ⟨51727676660815215053476883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137940471095507240142605021 51727676660815215053476883)
    ·
      refine ⟨77591514991222822580215325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51727676660815215053476883 77591514991222822580215325)
      ·
        refine ⟨29096818121708558467580747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77591514991222822580215325 29096818121708558467580747)
        ·
          refine ⟨43645227182562837701371121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29096818121708558467580747 43645227182562837701371121)
          ·
            refine ⟨32733920386922128276028341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43645227182562837701371121 32733920386922128276028341)
            ·
              refine ⟨3068805036273949525877657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32733920386922128276028341 3068805036273949525877657)
              ·
                refine ⟨2301603777205462144408243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068805036273949525877657 2301603777205462144408243)
                ·
                  refine ⟨3452405665808193216612365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301603777205462144408243 3452405665808193216612365)
                  ·
                    refine ⟨1294652124678072456229637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452405665808193216612365 1294652124678072456229637)
                    ·
                      rfl

theorem cell22_3781989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_3781989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3781989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3781989 prefixEnd_3781989 := by exact prefixLift 3781989
  have htrace : WordTrace (prefixWord ++ tailWord_3781989) baseStart_3781989 baseEnd_3781989 := by
    simpa [prefixWord, tailWord_3781989, baseEnd_3781989] using wordTrace_append hprefix tailTrace_3781989
  have hstable : (prefixWord ++ tailWord_3781989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3781989).length < 2 ^ (prefixWord ++ tailWord_3781989).sum := by decide
  have hdescent : baseEnd_3781989 < baseStart_3781989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3781989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782013 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3782013 : Nat := 118140960795 + 3782013 * 2 ^ 59
def prefixEnd_3782013 : Nat := 4983230072969 + 3 ^ 40 * 3782013 * 2
def baseEnd_3782013 : Nat := 431553446789514797876521

theorem tailTrace_3782013 : CollatzResearch.WordTrace tailWord_3782013 prefixEnd_3782013 431553446789514797876521 := by
  unfold tailWord_3782013
  simp only [CollatzResearch.WordTrace]
  refine ⟨137941346447420292241478693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91960897631613528160985795 137941346447420292241478693)
  ·
    refine ⟨25864002458891304795277255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137941346447420292241478693 25864002458891304795277255)
    ·
      refine ⟨38796003688336957192915883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864002458891304795277255 38796003688336957192915883)
      ·
        refine ⟨58194005532505435789373825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38796003688336957192915883 58194005532505435789373825)
        ·
          refine ⟨43645504149379076842030369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58194005532505435789373825 43645504149379076842030369)
          ·
            refine ⟨32734128112034307631522777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43645504149379076842030369 32734128112034307631522777)
            ·
              refine ⟨24550596084025730723642083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32734128112034307631522777 24550596084025730723642083)
              ·
                refine ⟨36825894126038596085463125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24550596084025730723642083 36825894126038596085463125)
                ·
                  refine ⟨431553446789514797876521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36825894126038596085463125 431553446789514797876521)
                  ·
                    rfl

theorem cell22_3782013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3782013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782013 prefixEnd_3782013 := by exact prefixLift 3782013
  have htrace : WordTrace (prefixWord ++ tailWord_3782013) baseStart_3782013 baseEnd_3782013 := by
    simpa [prefixWord, tailWord_3782013, baseEnd_3782013] using wordTrace_append hprefix tailTrace_3782013
  have hstable : (prefixWord ++ tailWord_3782013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782013).length < 2 ^ (prefixWord ++ tailWord_3782013).sum := by decide
  have hdescent : baseEnd_3782013 < baseStart_3782013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782047 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 4]
def baseStart_3782047 : Nat := 118140960795 + 3782047 * 2 ^ 59
def prefixEnd_3782047 : Nat := 4983230072969 + 3 ^ 40 * 3782047 * 2
def baseEnd_3782047 : Nat := 431557326421126546093153

theorem tailTrace_3782047 : CollatzResearch.WordTrace tailWord_3782047 prefixEnd_3782047 431557326421126546093153 := by
  unfold tailWord_3782047
  simp only [CollatzResearch.WordTrace]
  refine ⟨137942586529297116048216395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91961724352864744032144263 137942586529297116048216395)
  ·
    refine ⟨206913879793945674072324593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137942586529297116048216395 206913879793945674072324593)
    ·
      refine ⟨155185409845459255554243445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206913879793945674072324593 155185409845459255554243445)
      ·
        refine ⟨14548632173011805208210323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155185409845459255554243445 14548632173011805208210323)
        ·
          refine ⟨21822948259517707812315485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14548632173011805208210323 21822948259517707812315485)
          ·
            refine ⟨8183605597319140429618307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21822948259517707812315485 8183605597319140429618307)
            ·
              refine ⟨12275408395978710644427461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183605597319140429618307 12275408395978710644427461)
              ·
                refine ⟨2301639074246008245830149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12275408395978710644427461 2301639074246008245830149)
                ·
                  refine ⟨431557326421126546093153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301639074246008245830149 431557326421126546093153)
                  ·
                    rfl

theorem cell22_3782047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 4].length) (baseStart_3782047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782047 prefixEnd_3782047 := by exact prefixLift 3782047
  have htrace : WordTrace (prefixWord ++ tailWord_3782047) baseStart_3782047 baseEnd_3782047 := by
    simpa [prefixWord, tailWord_3782047, baseEnd_3782047] using wordTrace_append hprefix tailTrace_3782047
  have hstable : (prefixWord ++ tailWord_3782047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782047).length < 2 ^ (prefixWord ++ tailWord_3782047).sum := by decide
  have hdescent : baseEnd_3782047 < baseStart_3782047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782141 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_3782141 : Nat := 118140960795 + 3782141 * 2 ^ 59
def prefixEnd_3782141 : Nat := 4983230072969 + 3 ^ 40 * 3782141 * 2
def baseEnd_3782141 : Nat := 1294704157384394726429171

theorem tailTrace_3782141 : CollatzResearch.WordTrace tailWord_3782141 prefixEnd_3782141 1294704157384394726429171 := by
  unfold tailWord_3782141
  simp only [CollatzResearch.WordTrace]
  refine ⟨137946014990956570102138277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91964009993971046734758851 137946014990956570102138277)
  ·
    refine ⟨25864877810804356894150927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137946014990956570102138277 25864877810804356894150927)
    ·
      refine ⟨38797316716206535341226391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864877810804356894150927 38797316716206535341226391)
      ·
        refine ⟨58195975074309803011839587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38797316716206535341226391 58195975074309803011839587)
        ·
          refine ⟨87293962611464704517759381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58195975074309803011839587 87293962611464704517759381)
          ·
            refine ⟨4091904497412408024269971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87293962611464704517759381 4091904497412408024269971)
            ·
              refine ⟨6137856746118612036404957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091904497412408024269971 6137856746118612036404957)
              ·
                refine ⟨2301696279794479513651859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6137856746118612036404957 2301696279794479513651859)
                ·
                  refine ⟨3452544419691719270477789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301696279794479513651859 3452544419691719270477789)
                  ·
                    refine ⟨1294704157384394726429171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452544419691719270477789 1294704157384394726429171)
                    ·
                      rfl

theorem cell22_3782141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_3782141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782141 prefixEnd_3782141 := by exact prefixLift 3782141
  have htrace : WordTrace (prefixWord ++ tailWord_3782141) baseStart_3782141 baseEnd_3782141 := by
    simpa [prefixWord, tailWord_3782141, baseEnd_3782141] using wordTrace_append hprefix tailTrace_3782141
  have hstable : (prefixWord ++ tailWord_3782141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782141).length < 2 ^ (prefixWord ++ tailWord_3782141).sum := by decide
  have hdescent : baseEnd_3782141 < baseStart_3782141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782158 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3782158 : Nat := 118140960795 + 3782158 * 2 ^ 59
def prefixEnd_3782158 : Nat := 4983230072969 + 3 ^ 40 * 3782158 * 2
def baseEnd_3782158 : Nat := 1294709976831812348754119

theorem tailTrace_3782158 : CollatzResearch.WordTrace tailWord_3782158 prefixEnd_3782158 1294709976831812348754119 := by
  unfold tailWord_3782158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17243329378986872750688391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91964423354596654670338085 17243329378986872750688391)
  ·
    refine ⟨25864994068480309126032587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17243329378986872750688391 25864994068480309126032587)
    ·
      refine ⟨38797491102720463689048881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25864994068480309126032587 38797491102720463689048881)
      ·
        refine ⟨29098118327040347766786661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38797491102720463689048881 29098118327040347766786661)
        ·
          refine ⟨5455897186320065206272499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29098118327040347766786661 5455897186320065206272499)
          ·
            refine ⟨8183845779480097809408749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455897186320065206272499 8183845779480097809408749)
            ·
              refine ⟨3068942167305036678528281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8183845779480097809408749 3068942167305036678528281)
              ·
                refine ⟨2301706625478777508896211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068942167305036678528281 2301706625478777508896211)
                ·
                  refine ⟨3452559938218166263344317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301706625478777508896211 3452559938218166263344317)
                  ·
                    refine ⟨1294709976831812348754119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452559938218166263344317 1294709976831812348754119)
                    ·
                      rfl

theorem cell22_3782158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3782158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782158 prefixEnd_3782158 := by exact prefixLift 3782158
  have htrace : WordTrace (prefixWord ++ tailWord_3782158) baseStart_3782158 baseEnd_3782158 := by
    simpa [prefixWord, tailWord_3782158, baseEnd_3782158] using wordTrace_append hprefix tailTrace_3782158
  have hstable : (prefixWord ++ tailWord_3782158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782158).length < 2 ^ (prefixWord ++ tailWord_3782158).sum := by decide
  have hdescent : baseEnd_3782158 < baseStart_3782158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782184 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3782184 : Nat := 118140960795 + 3782184 * 2 ^ 59
def prefixEnd_3782184 : Nat := 4983230072969 + 3 ^ 40 * 3782184 * 2
def baseEnd_3782184 : Nat := 1294718877163156947604039

theorem tailTrace_3782184 : CollatzResearch.WordTrace tailWord_3782184 prefixEnd_3782184 1294718877163156947604039 := by
  unfold tailWord_3782184
  simp only [CollatzResearch.WordTrace]
  refine ⟨68973791664900394222976803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91965055553200525630635737 68973791664900394222976803)
  ·
    refine ⟨103460687497350591334465205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68973791664900394222976803 103460687497350591334465205)
    ·
      refine ⟨9699439452876617937606113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103460687497350591334465205 9699439452876617937606113)
      ·
        refine ⟨7274579589657463453204585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9699439452876617937606113 7274579589657463453204585)
        ·
          refine ⟨5455934692243097589903439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7274579589657463453204585 5455934692243097589903439)
          ·
            refine ⟨8183902038364646384855159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5455934692243097589903439 8183902038364646384855159)
            ·
              refine ⟨12275853057546969577282739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183902038364646384855159 12275853057546969577282739)
              ·
                refine ⟨18413779586320454365924109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12275853057546969577282739 18413779586320454365924109)
                ·
                  refine ⟨6905167344870170387221541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18413779586320454365924109 6905167344870170387221541)
                  ·
                    refine ⟨1294718877163156947604039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6905167344870170387221541 1294718877163156947604039)
                    ·
                      rfl

theorem cell22_3782184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3782184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782184 prefixEnd_3782184 := by exact prefixLift 3782184
  have htrace : WordTrace (prefixWord ++ tailWord_3782184) baseStart_3782184 baseEnd_3782184 := by
    simpa [prefixWord, tailWord_3782184, baseEnd_3782184] using wordTrace_append hprefix tailTrace_3782184
  have hstable : (prefixWord ++ tailWord_3782184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782184).length < 2 ^ (prefixWord ++ tailWord_3782184).sum := by decide
  have hdescent : baseEnd_3782184 < baseStart_3782184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782197 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3782197 : Nat := 118140960795 + 3782197 * 2 ^ 59
def prefixEnd_3782197 : Nat := 4983230072969 + 3 ^ 40 * 3782197 * 2
def baseEnd_3782197 : Nat := 1294723327328829247028999

theorem tailTrace_3782197 : CollatzResearch.WordTrace tailWord_3782197 prefixEnd_3782197 1294723327328829247028999 := by
  unfold tailWord_3782197
  simp only [CollatzResearch.WordTrace]
  refine ⟨137948057478753691666176845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91965371652502461110784563 137948057478753691666176845)
  ·
    refine ⟨51730521554532634374816317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137948057478753691666176845 51730521554532634374816317)
    ·
      refine ⟨19398945582949737890556119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51730521554532634374816317 19398945582949737890556119)
      ·
        refine ⟨29098418374424606835834179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19398945582949737890556119 29098418374424606835834179)
        ·
          refine ⟨43647627561636910253751269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29098418374424606835834179 43647627561636910253751269)
          ·
            refine ⟨8183930167806920672578363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43647627561636910253751269 8183930167806920672578363)
            ·
              refine ⟨12275895251710381008867545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8183930167806920672578363 12275895251710381008867545)
              ·
                refine ⟨9206921438782785756650659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12275895251710381008867545 9206921438782785756650659)
                ·
                  refine ⟨13810382158174178634975989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9206921438782785756650659 13810382158174178634975989)
                  ·
                    refine ⟨1294723327328829247028999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13810382158174178634975989 1294723327328829247028999)
                    ·
                      rfl

theorem cell22_3782197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3782197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782197 prefixEnd_3782197 := by exact prefixLift 3782197
  have htrace : WordTrace (prefixWord ++ tailWord_3782197) baseStart_3782197 baseEnd_3782197 := by
    simpa [prefixWord, tailWord_3782197, baseEnd_3782197] using wordTrace_append hprefix tailTrace_3782197
  have hstable : (prefixWord ++ tailWord_3782197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782197).length < 2 ^ (prefixWord ++ tailWord_3782197).sum := by decide
  have hdescent : baseEnd_3782197 < baseStart_3782197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782240 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_3782240 : Nat := 118140960795 + 3782240 * 2 ^ 59
def prefixEnd_3782240 : Nat := 4983230072969 + 3 ^ 40 * 3782240 * 2
def baseEnd_3782240 : Nat := 1294738047107591468203867

theorem tailTrace_3782240 : CollatzResearch.WordTrace tailWord_3782240 prefixEnd_3782240 1294738047107591468203867 := by
  unfold tailWord_3782240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68974812908798955004996087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91966417211731940006661449 68974812908798955004996087)
  ·
    refine ⟨103462219363198432507494131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68974812908798955004996087 103462219363198432507494131)
    ·
      refine ⟨155193329044797648761241197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103462219363198432507494131 155193329044797648761241197)
      ·
        refine ⟨58197498391799118285465449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155193329044797648761241197 58197498391799118285465449)
        ·
          refine ⟨43648123793849338714099087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58197498391799118285465449 43648123793849338714099087)
          ·
            refine ⟨65472185690774008071148631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43648123793849338714099087 65472185690774008071148631)
            ·
              refine ⟨98208278536161012106722947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65472185690774008071148631 98208278536161012106722947)
              ·
                refine ⟨147312417804241518160084421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98208278536161012106722947 147312417804241518160084421)
                ·
                  refine ⟨27621078338295284655015829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147312417804241518160084421 27621078338295284655015829)
                  ·
                    refine ⟨1294738047107591468203867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27621078338295284655015829 1294738047107591468203867)
                    ·
                      rfl

theorem cell22_3782240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_3782240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782240 prefixEnd_3782240 := by exact prefixLift 3782240
  have htrace : WordTrace (prefixWord ++ tailWord_3782240) baseStart_3782240 baseEnd_3782240 := by
    simpa [prefixWord, tailWord_3782240, baseEnd_3782240] using wordTrace_append hprefix tailTrace_3782240
  have hstable : (prefixWord ++ tailWord_3782240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782240).length < 2 ^ (prefixWord ++ tailWord_3782240).sum := by decide
  have hdescent : baseEnd_3782240 < baseStart_3782240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782255 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 7]
def baseStart_3782255 : Nat := 118140960795 + 3782255 * 2 ^ 59
def prefixEnd_3782255 : Nat := 4983230072969 + 3 ^ 40 * 3782255 * 2
def baseEnd_3782255 : Nat := 431581060638045476359607

theorem tailTrace_3782255 : CollatzResearch.WordTrace tailWord_3782255 prefixEnd_3782255 431581060638045476359607 := by
  unfold tailWord_3782255
  simp only [CollatzResearch.WordTrace]
  refine ⟨137950172912543567571788219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91966781941695711714525479 137950172912543567571788219)
  ·
    refine ⟨206925259368815351357682329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137950172912543567571788219 206925259368815351357682329)
    ·
      refine ⟨155193944526611513518261747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206925259368815351357682329 155193944526611513518261747)
      ·
        refine ⟨232790916789917270277392621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155193944526611513518261747 232790916789917270277392621)
        ·
          refine ⟨87296593796218976354022233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232790916789917270277392621 87296593796218976354022233)
          ·
            refine ⟨65472445347164232265516675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87296593796218976354022233 65472445347164232265516675)
            ·
              refine ⟨98208668020746348398275013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65472445347164232265516675 98208668020746348398275013)
              ·
                refine ⟨18414125253889940324676565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98208668020746348398275013 18414125253889940324676565)
                ·
                  refine ⟨431581060638045476359607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18414125253889940324676565 431581060638045476359607)
                  ·
                    rfl

theorem cell22_3782255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_3782255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782255 prefixEnd_3782255 := by exact prefixLift 3782255
  have htrace : WordTrace (prefixWord ++ tailWord_3782255) baseStart_3782255 baseEnd_3782255 := by
    simpa [prefixWord, tailWord_3782255, baseEnd_3782255] using wordTrace_append hprefix tailTrace_3782255
  have hstable : (prefixWord ++ tailWord_3782255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782255).length < 2 ^ (prefixWord ++ tailWord_3782255).sum := by decide
  have hdescent : baseEnd_3782255 < baseStart_3782255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782276 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3782276 : Nat := 118140960795 + 3782276 * 2 ^ 59
def prefixEnd_3782276 : Nat := 4983230072969 + 3 ^ 40 * 3782276 * 2
def baseEnd_3782276 : Nat := 1294750370643299374303757

theorem tailTrace_3782276 : CollatzResearch.WordTrace tailWord_3782276 prefixEnd_3782276 1294750370643299374303757 := by
  unfold tailWord_3782276
  simp only [CollatzResearch.WordTrace]
  refine ⟨68975469422733744079151341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91967292563644992105535121 68975469422733744079151341)
  ·
    refine ⟨25865801033525154029681753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68975469422733744079151341 25865801033525154029681753)
    ·
      refine ⟨19399350775143865522261315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25865801033525154029681753 19399350775143865522261315)
      ·
        refine ⟨29099026162715798283391973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19399350775143865522261315 29099026162715798283391973)
        ·
          refine ⟨5456067405509212178135995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29099026162715798283391973 5456067405509212178135995)
          ·
            refine ⟨8184101108263818267203993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456067405509212178135995 8184101108263818267203993)
            ·
              refine ⟨6138075831197863700402995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8184101108263818267203993 6138075831197863700402995)
              ·
                refine ⟨9207113746796795550604493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138075831197863700402995 9207113746796795550604493)
                ·
                  refine ⟨3452667655048798331476685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9207113746796795550604493 3452667655048798331476685)
                  ·
                    refine ⟨1294750370643299374303757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452667655048798331476685 1294750370643299374303757)
                    ·
                      rfl

theorem cell22_3782276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3782276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782276 prefixEnd_3782276 := by exact prefixLift 3782276
  have htrace : WordTrace (prefixWord ++ tailWord_3782276) baseStart_3782276 baseEnd_3782276 := by
    simpa [prefixWord, tailWord_3782276, baseEnd_3782276] using wordTrace_append hprefix tailTrace_3782276
  have hstable : (prefixWord ++ tailWord_3782276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782276).length < 2 ^ (prefixWord ++ tailWord_3782276).sum := by decide
  have hdescent : baseEnd_3782276 < baseStart_3782276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782334 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3782334 : Nat := 118140960795 + 3782334 * 2 ^ 59
def prefixEnd_3782334 : Nat := 4983230072969 + 3 ^ 40 * 3782334 * 2
def baseEnd_3782334 : Nat := 431590075076202185451193

theorem tailTrace_3782334 : CollatzResearch.WordTrace tailWord_3782334 prefixEnd_3782334 431590075076202185451193 := by
  unfold tailWord_3782334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244131784907170507989257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91968702852838242709276037 17244131784907170507989257)
  ·
    refine ⟨12933098838680377880991943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17244131784907170507989257 12933098838680377880991943)
    ·
      refine ⟨19399648258020566821487915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12933098838680377880991943 19399648258020566821487915)
      ·
        refine ⟨29099472387030850232231873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19399648258020566821487915 29099472387030850232231873)
        ·
          refine ⟨21824604290273137674173905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29099472387030850232231873 21824604290273137674173905)
          ·
            refine ⟨16368453217704853255630429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21824604290273137674173905 16368453217704853255630429)
            ·
              refine ⟨6138169956639319970861411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16368453217704853255630429 6138169956639319970861411)
              ·
                refine ⟨9207254934958979956292117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6138169956639319970861411 9207254934958979956292117)
                ·
                  refine ⟨431590075076202185451193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9207254934958979956292117 431590075076202185451193)
                  ·
                    rfl

theorem cell22_3782334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3782334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782334 prefixEnd_3782334 := by exact prefixLift 3782334
  have htrace : WordTrace (prefixWord ++ tailWord_3782334) baseStart_3782334 baseEnd_3782334 := by
    simpa [prefixWord, tailWord_3782334, baseEnd_3782334] using wordTrace_append hprefix tailTrace_3782334
  have hstable : (prefixWord ++ tailWord_3782334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782334).length < 2 ^ (prefixWord ++ tailWord_3782334).sum := by decide
  have hdescent : baseEnd_3782334 < baseStart_3782334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782362 : List Nat := [3, 1, 1, 2, 2, 3, 2, 8]
def baseStart_3782362 : Nat := 118140960795 + 3782362 * 2 ^ 59
def prefixEnd_3782362 : Nat := 4983230072969 + 3 ^ 40 * 3782362 * 2
def baseEnd_3782362 : Nat := 143864423355647090739277

theorem tailTrace_3782362 : CollatzResearch.WordTrace tailWord_3782362 prefixEnd_3782362 143864423355647090739277 := by
  unfold tailWord_3782362
  simp only [CollatzResearch.WordTrace]
  refine ⟨34488518880788981211483335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91969383682103949897288893 34488518880788981211483335)
  ·
    refine ⟨51732778321183471817225003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34488518880788981211483335 51732778321183471817225003)
    ·
      refine ⟨77599167481775207725837505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51732778321183471817225003 77599167481775207725837505)
      ·
        refine ⟨58199375611331405794378129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77599167481775207725837505 58199375611331405794378129)
        ·
          refine ⟨43649531708498554345783597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58199375611331405794378129 43649531708498554345783597)
          ·
            refine ⟨16368574390686957879668849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43649531708498554345783597 16368574390686957879668849)
            ·
              refine ⟨12276430793015218409751637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16368574390686957879668849 12276430793015218409751637)
              ·
                refine ⟨143864423355647090739277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12276430793015218409751637 143864423355647090739277)
                ·
                  rfl

theorem cell22_3782362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_3782362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782362 prefixEnd_3782362 := by exact prefixLift 3782362
  have htrace : WordTrace (prefixWord ++ tailWord_3782362) baseStart_3782362 baseEnd_3782362 := by
    simpa [prefixWord, tailWord_3782362, baseEnd_3782362] using wordTrace_append hprefix tailTrace_3782362
  have hstable : (prefixWord ++ tailWord_3782362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782362).length < 2 ^ (prefixWord ++ tailWord_3782362).sum := by decide
  have hdescent : baseEnd_3782362 < baseStart_3782362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782394 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_3782394 : Nat := 118140960795 + 3782394 * 2 ^ 59
def prefixEnd_3782394 : Nat := 4983230072969 + 3 ^ 40 * 3782394 * 2
def baseEnd_3782394 : Nat := 1294790764454786399853395

theorem tailTrace_3782394 : CollatzResearch.WordTrace tailWord_3782394 prefixEnd_3782394 1294790764454786399853395 := by
  unfold tailWord_3782394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34488810664759998577774559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91970161772693329540732157 34488810664759998577774559)
  ·
    refine ⟨51733215997139997866661839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34488810664759998577774559 51733215997139997866661839)
    ·
      refine ⟨77599823995709996799992759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51733215997139997866661839 77599823995709996799992759)
      ·
        refine ⟨116399735993564995199989139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77599823995709996799992759 116399735993564995199989139)
        ·
          refine ⟨174599603990347492799983709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116399735993564995199989139 174599603990347492799983709)
          ·
            refine ⟨65474851496380309799993891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174599603990347492799983709 65474851496380309799993891)
            ·
              refine ⟨98212277244570464699990837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65474851496380309799993891 98212277244570464699990837)
              ·
                refine ⟨9207400991678481065624141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98212277244570464699990837 9207400991678481065624141)
                ·
                  refine ⟨3452775371879430399609053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9207400991678481065624141 3452775371879430399609053)
                  ·
                    refine ⟨1294790764454786399853395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452775371879430399609053 1294790764454786399853395)
                    ·
                      rfl

theorem cell22_3782394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_3782394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782394 prefixEnd_3782394 := by exact prefixLift 3782394
  have htrace : WordTrace (prefixWord ++ tailWord_3782394) baseStart_3782394 baseEnd_3782394 := by
    simpa [prefixWord, tailWord_3782394, baseEnd_3782394] using wordTrace_append hprefix tailTrace_3782394
  have hstable : (prefixWord ++ tailWord_3782394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782394).length < 2 ^ (prefixWord ++ tailWord_3782394).sum := by decide
  have hdescent : baseEnd_3782394 < baseStart_3782394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782428 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_3782428 : Nat := 118140960795 + 3782428 * 2 ^ 59
def prefixEnd_3782428 : Nat := 4983230072969 + 3 ^ 40 * 3782428 * 2
def baseEnd_3782428 : Nat := 1294802403349621644503291

theorem tailTrace_3782428 : CollatzResearch.WordTrace tailWord_3782428 prefixEnd_3782428 1294802403349621644503291 := by
  unfold tailWord_3782428
  simp only [CollatzResearch.WordTrace]
  refine ⟨68978241370458409058917969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91970988493944545411890625 68978241370458409058917969)
  ·
    refine ⟨51733681027843806794188477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68978241370458409058917969 51733681027843806794188477)
    ·
      refine ⟨19400130385441427547820679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51733681027843806794188477 19400130385441427547820679)
      ·
        refine ⟨29100195578162141321731019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19400130385441427547820679 29100195578162141321731019)
        ·
          refine ⟨43650293367243211982596529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29100195578162141321731019 43650293367243211982596529)
          ·
            refine ⟨32737720025432408986947397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43650293367243211982596529 32737720025432408986947397)
            ·
              refine ⟨6138322504768576685052637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32737720025432408986947397 6138322504768576685052637)
              ·
                refine ⟨2301870939288216256894739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6138322504768576685052637 2301870939288216256894739)
                ·
                  refine ⟨3452806408932324385342109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301870939288216256894739 3452806408932324385342109)
                  ·
                    refine ⟨1294802403349621644503291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452806408932324385342109 1294802403349621644503291)
                    ·
                      rfl

theorem cell22_3782428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_3782428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782428 prefixEnd_3782428 := by exact prefixLift 3782428
  have htrace : WordTrace (prefixWord ++ tailWord_3782428) baseStart_3782428 baseEnd_3782428 := by
    simpa [prefixWord, tailWord_3782428, baseEnd_3782428] using wordTrace_append hprefix tailTrace_3782428
  have hstable : (prefixWord ++ tailWord_3782428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782428).length < 2 ^ (prefixWord ++ tailWord_3782428).sum := by decide
  have hdescent : baseEnd_3782428 < baseStart_3782428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782501 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_3782501 : Nat := 118140960795 + 3782501 * 2 ^ 59
def prefixEnd_3782501 : Nat := 4983230072969 + 3 ^ 40 * 3782501 * 2
def baseEnd_3782501 : Nat := 1294827392741473787428067

theorem tailTrace_3782501 : CollatzResearch.WordTrace tailWord_3782501 prefixEnd_3782501 1294827392741473787428067 := by
  unfold tailWord_3782501
  simp only [CollatzResearch.WordTrace]
  refine ⟨137959145269652351585243357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91972763513101567723495571 137959145269652351585243357)
  ·
    refine ⟨51734679476119631844466259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137959145269652351585243357 51734679476119631844466259)
    ·
      refine ⟨77602019214179447766699389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51734679476119631844466259 77602019214179447766699389)
      ·
        refine ⟨29100757205317292912512271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77602019214179447766699389 29100757205317292912512271)
        ·
          refine ⟨43651135807975939368768407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29100757205317292912512271 43651135807975939368768407)
          ·
            refine ⟨65476703711963909053152611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43651135807975939368768407 65476703711963909053152611)
            ·
              refine ⟨98215055567945863579728917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65476703711963909053152611 98215055567945863579728917)
              ·
                refine ⟨4603830729747462355299793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98215055567945863579728917 4603830729747462355299793)
                ·
                  refine ⟨3452873047310596766474845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4603830729747462355299793 3452873047310596766474845)
                  ·
                    refine ⟨1294827392741473787428067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3452873047310596766474845 1294827392741473787428067)
                    ·
                      rfl

theorem cell22_3782501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_3782501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782501 prefixEnd_3782501 := by exact prefixLift 3782501
  have htrace : WordTrace (prefixWord ++ tailWord_3782501) baseStart_3782501 baseEnd_3782501 := by
    simpa [prefixWord, tailWord_3782501, baseEnd_3782501] using wordTrace_append hprefix tailTrace_3782501
  have hstable : (prefixWord ++ tailWord_3782501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782501).length < 2 ^ (prefixWord ++ tailWord_3782501).sum := by decide
  have hdescent : baseEnd_3782501 < baseStart_3782501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782503 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 4]
def baseStart_3782503 : Nat := 118140960795 + 3782503 * 2 ^ 59
def prefixEnd_3782503 : Nat := 4983230072969 + 3 ^ 40 * 3782503 * 2
def baseEnd_3782503 : Nat := 431609359127448816292687

theorem tailTrace_3782503 : CollatzResearch.WordTrace tailWord_3782503 prefixEnd_3782503 431609359127448816292687 := by
  unfold tailWord_3782503
  simp only [CollatzResearch.WordTrace]
  refine ⟨137959218215645105926816163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91972812143763403951210775 137959218215645105926816163)
  ·
    refine ⟨206938827323467658890224245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137959218215645105926816163 206938827323467658890224245)
    ·
      refine ⟨19400515061575093020958523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206938827323467658890224245 19400515061575093020958523)
      ·
        refine ⟨29100772592362639531437785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19400515061575093020958523 29100772592362639531437785)
        ·
          refine ⟨21825579444271979648578339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29100772592362639531437785 21825579444271979648578339)
          ·
            refine ⟨32738369166407969472867509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21825579444271979648578339 32738369166407969472867509)
            ·
              refine ⟨3069222109350747138081329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32738369166407969472867509 3069222109350747138081329)
              ·
                refine ⟨2301916582013060353560997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069222109350747138081329 2301916582013060353560997)
                ·
                  refine ⟨431609359127448816292687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301916582013060353560997 431609359127448816292687)
                  ·
                    rfl

theorem cell22_3782503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 4].length) (baseStart_3782503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782503 prefixEnd_3782503 := by exact prefixLift 3782503
  have htrace : WordTrace (prefixWord ++ tailWord_3782503) baseStart_3782503 baseEnd_3782503 := by
    simpa [prefixWord, tailWord_3782503, baseEnd_3782503] using wordTrace_append hprefix tailTrace_3782503
  have hstable : (prefixWord ++ tailWord_3782503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782503).length < 2 ^ (prefixWord ++ tailWord_3782503).sum := by decide
  have hdescent : baseEnd_3782503 < baseStart_3782503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782610 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_3782610 : Nat := 118140960795 + 3782610 * 2 ^ 59
def prefixEnd_3782610 : Nat := 4983230072969 + 3 ^ 40 * 3782610 * 2
def baseEnd_3782610 : Nat := 431621568556344612150911

theorem tailTrace_3782610 : CollatzResearch.WordTrace tailWord_3782610 prefixEnd_3782610 431621568556344612150911 := by
  unfold tailWord_3782610
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490780206564365800240321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91975413884171642133974189 34490780206564365800240321)
  ·
    refine ⟨25868085154923274350180241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34490780206564365800240321 25868085154923274350180241)
    ·
      refine ⟨19401063866192455762635181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25868085154923274350180241 19401063866192455762635181)
      ·
        refine ⟨7275398949822170910988193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19401063866192455762635181 7275398949822170910988193)
        ·
          refine ⟨5456549212366628183241145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7275398949822170910988193 5456549212366628183241145)
          ·
            refine ⟨4092411909274971137430859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5456549212366628183241145 4092411909274971137430859)
            ·
              refine ⟨6138617863912456706146289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092411909274971137430859 6138617863912456706146289)
              ·
                refine ⟨4603963397934342529609717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6138617863912456706146289 4603963397934342529609717)
                ·
                  refine ⟨431621568556344612150911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4603963397934342529609717 431621568556344612150911)
                  ·
                    rfl

theorem cell22_3782610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_3782610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782610 prefixEnd_3782610 := by exact prefixLift 3782610
  have htrace : WordTrace (prefixWord ++ tailWord_3782610) baseStart_3782610 baseEnd_3782610 := by
    simpa [prefixWord, tailWord_3782610, baseEnd_3782610] using wordTrace_append hprefix tailTrace_3782610
  have hstable : (prefixWord ++ tailWord_3782610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782610).length < 2 ^ (prefixWord ++ tailWord_3782610).sum := by decide
  have hdescent : baseEnd_3782610 < baseStart_3782610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782732 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_3782732 : Nat := 118140960795 + 3782732 * 2 ^ 59
def prefixEnd_3782732 : Nat := 4983230072969 + 3 ^ 40 * 3782732 * 2
def baseEnd_3782732 : Nat := 1294906468762266184902359

theorem tailTrace_3782732 : CollatzResearch.WordTrace tailWord_3782732 prefixEnd_3782732 1294906468762266184902359 := by
  unfold tailWord_3782732
  simp only [CollatzResearch.WordTrace]
  refine ⟨68983785265907739018451225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91978380354543652024601633 68983785265907739018451225)
  ·
    refine ⟨51737838949430804263838419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68983785265907739018451225 51737838949430804263838419)
    ·
      refine ⟨77606758424146206395757629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51737838949430804263838419 77606758424146206395757629)
      ·
        refine ⟨29102534409054827398409111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77606758424146206395757629 29102534409054827398409111)
        ·
          refine ⟨43653801613582241097613667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29102534409054827398409111 43653801613582241097613667)
          ·
            refine ⟨65480702420373361646420501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43653801613582241097613667 65480702420373361646420501)
            ·
              refine ⟨3069407925955001327175961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65480702420373361646420501 3069407925955001327175961)
              ·
                refine ⟨2302055944466250995381971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069407925955001327175961 2302055944466250995381971)
                ·
                  refine ⟨3453083916699376493072957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302055944466250995381971 3453083916699376493072957)
                  ·
                    refine ⟨1294906468762266184902359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453083916699376493072957 1294906468762266184902359)
                    ·
                      rfl

theorem cell22_3782732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_3782732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782732 prefixEnd_3782732 := by exact prefixLift 3782732
  have htrace : WordTrace (prefixWord ++ tailWord_3782732) baseStart_3782732 baseEnd_3782732 := by
    simpa [prefixWord, tailWord_3782732, baseEnd_3782732] using wordTrace_append hprefix tailTrace_3782732
  have hstable : (prefixWord ++ tailWord_3782732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782732).length < 2 ^ (prefixWord ++ tailWord_3782732).sum := by decide
  have hdescent : baseEnd_3782732 < baseStart_3782732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782756 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_3782756 : Nat := 118140960795 + 3782756 * 2 ^ 59
def prefixEnd_3782756 : Nat := 4983230072969 + 3 ^ 40 * 3782756 * 2
def baseEnd_3782756 : Nat := 431638228150912707434095

theorem tailTrace_3782756 : CollatzResearch.WordTrace tailWord_3782756 prefixEnd_3782756 431638228150912707434095 := by
  unfold tailWord_3782756
  simp only [CollatzResearch.WordTrace]
  refine ⟨68984222941864265067888061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91978963922485686757184081 68984222941864265067888061)
  ·
    refine ⟨25869083603199099400458023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68984222941864265067888061 25869083603199099400458023)
    ·
      refine ⟨38803625404798649100687035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25869083603199099400458023 38803625404798649100687035)
      ·
        refine ⟨58205438107197973651030553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38803625404798649100687035 58205438107197973651030553)
        ·
          refine ⟨43654078580398480238272915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58205438107197973651030553 43654078580398480238272915)
          ·
            refine ⟨65481117870597720357409373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43654078580398480238272915 65481117870597720357409373)
            ·
              refine ⟨24555419201474145134028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65481117870597720357409373 24555419201474145134028515)
              ·
                refine ⟨36833128802211217701042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24555419201474145134028515 36833128802211217701042773)
                ·
                  refine ⟨431638228150912707434095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36833128802211217701042773 431638228150912707434095)
                  ·
                    rfl

theorem cell22_3782756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_3782756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782756 prefixEnd_3782756 := by exact prefixLift 3782756
  have htrace : WordTrace (prefixWord ++ tailWord_3782756) baseStart_3782756 baseEnd_3782756 := by
    simpa [prefixWord, tailWord_3782756, baseEnd_3782756] using wordTrace_append hprefix tailTrace_3782756
  have hstable : (prefixWord ++ tailWord_3782756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782756).length < 2 ^ (prefixWord ++ tailWord_3782756).sum := by decide
  have hdescent : baseEnd_3782756 < baseStart_3782756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782775 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 1, 4]
def baseStart_3782775 : Nat := 118140960795 + 3782775 * 2 ^ 59
def prefixEnd_3782775 : Nat := 4983230072969 + 3 ^ 40 * 3782775 * 2
def baseEnd_3782775 : Nat := 1294921188541028406077227

theorem tailTrace_3782775 : CollatzResearch.WordTrace tailWord_3782775 prefixEnd_3782775 1294921188541028406077227 := by
  unfold tailWord_3782775
  simp only [CollatzResearch.WordTrace]
  refine ⟨137969138870659696380717779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91979425913773130920478519 137969138870659696380717779)
  ·
    refine ⟨206953708305989544571076669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137969138870659696380717779 206953708305989544571076669)
    ·
      refine ⟨77607640614746079214153751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206953708305989544571076669 77607640614746079214153751)
      ·
        refine ⟨116411460922119118821230627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77607640614746079214153751 116411460922119118821230627)
        ·
          refine ⟨174617191383178678231845941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116411460922119118821230627 174617191383178678231845941)
          ·
            refine ⟨16370361692173001084235557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174617191383178678231845941 16370361692173001084235557)
            ·
              refine ⟨3069442817282437703294167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16370361692173001084235557 3069442817282437703294167)
              ·
                refine ⟨4604164225923656554941251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069442817282437703294167 4604164225923656554941251)
                ·
                  refine ⟨6906246338885484832411877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604164225923656554941251 6906246338885484832411877)
                  ·
                    refine ⟨1294921188541028406077227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6906246338885484832411877 1294921188541028406077227)
                    ·
                      rfl

theorem cell22_3782775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_3782775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782775 prefixEnd_3782775 := by exact prefixLift 3782775
  have htrace : WordTrace (prefixWord ++ tailWord_3782775) baseStart_3782775 baseEnd_3782775 := by
    simpa [prefixWord, tailWord_3782775, baseEnd_3782775] using wordTrace_append hprefix tailTrace_3782775
  have hstable : (prefixWord ++ tailWord_3782775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782775).length < 2 ^ (prefixWord ++ tailWord_3782775).sum := by decide
  have hdescent : baseEnd_3782775 < baseStart_3782775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782831 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_3782831 : Nat := 118140960795 + 3782831 * 2 ^ 59
def prefixEnd_3782831 : Nat := 4983230072969 + 3 ^ 40 * 3782831 * 2
def baseEnd_3782831 : Nat := 1294940358485462926677055

theorem tailTrace_3782831 : CollatzResearch.WordTrace tailWord_3782831 prefixEnd_3782831 1294940358485462926677055 := by
  unfold tailWord_3782831
  simp only [CollatzResearch.WordTrace]
  refine ⟨137971181358456817944756347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91980787572304545296504231 137971181358456817944756347)
  ·
    refine ⟨206956772037685226917134521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137971181358456817944756347 206956772037685226917134521)
    ·
      refine ⟨155217579028263920187850891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206956772037685226917134521 155217579028263920187850891)
      ·
        refine ⟨232826368542395880281776337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155217579028263920187850891 232826368542395880281776337)
        ·
          refine ⟨174619776406796910211332253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232826368542395880281776337 174619776406796910211332253)
          ·
            refine ⟨65482416152548841329249595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174619776406796910211332253 65482416152548841329249595)
            ·
              refine ⟨98223624228823261993874393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65482416152548841329249595 98223624228823261993874393)
              ·
                refine ⟨73667718171617446495405795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98223624228823261993874393 73667718171617446495405795)
                ·
                  refine ⟨110501577257426169743108693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73667718171617446495405795 110501577257426169743108693)
                  ·
                    refine ⟨1294940358485462926677055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110501577257426169743108693 1294940358485462926677055)
                    ·
                      rfl

theorem cell22_3782831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_3782831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782831 prefixEnd_3782831 := by exact prefixLift 3782831
  have htrace : WordTrace (prefixWord ++ tailWord_3782831) baseStart_3782831 baseEnd_3782831 := by
    simpa [prefixWord, tailWord_3782831, baseEnd_3782831] using wordTrace_append hprefix tailTrace_3782831
  have hstable : (prefixWord ++ tailWord_3782831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782831).length < 2 ^ (prefixWord ++ tailWord_3782831).sum := by decide
  have hdescent : baseEnd_3782831 < baseStart_3782831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782837 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3782837 : Nat := 118140960795 + 3782837 * 2 ^ 59
def prefixEnd_3782837 : Nat := 4983230072969 + 3 ^ 40 * 3782837 * 2
def baseEnd_3782837 : Nat := 1294942412408080911027037

theorem tailTrace_3782837 : CollatzResearch.WordTrace tailWord_3782837 prefixEnd_3782837 1294942412408080911027037 := by
  unfold tailWord_3782837
  simp only [CollatzResearch.WordTrace]
  refine ⟨137971400196435080969474765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91980933464290053979649843 137971400196435080969474765)
  ·
    refine ⟨51739275073663155363553037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137971400196435080969474765 51739275073663155363553037)
    ·
      refine ⟨19402228152623683261332389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51739275073663155363553037 19402228152623683261332389)
      ·
        refine ⟨3637917778616940611499823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19402228152623683261332389 3637917778616940611499823)
        ·
          refine ⟨5456876667925410917249735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637917778616940611499823 5456876667925410917249735)
          ·
            refine ⟨8185315001888116375874603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5456876667925410917249735 8185315001888116375874603)
            ·
              refine ⟨12277972502832174563811905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8185315001888116375874603 12277972502832174563811905)
              ·
                refine ⟨9208479377124130922858929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12277972502832174563811905 9208479377124130922858929)
                ·
                  refine ⟨6906359532843098192144197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9208479377124130922858929 6906359532843098192144197)
                  ·
                    refine ⟨1294942412408080911027037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6906359532843098192144197 1294942412408080911027037)
                    ·
                      rfl

theorem cell22_3782837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3782837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782837 prefixEnd_3782837 := by exact prefixLift 3782837
  have htrace : WordTrace (prefixWord ++ tailWord_3782837) baseStart_3782837 baseEnd_3782837 := by
    simpa [prefixWord, tailWord_3782837, baseEnd_3782837] using wordTrace_append hprefix tailTrace_3782837
  have hstable : (prefixWord ++ tailWord_3782837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782837).length < 2 ^ (prefixWord ++ tailWord_3782837).sum := by decide
  have hdescent : baseEnd_3782837 < baseStart_3782837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782863 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 5]
def baseStart_3782863 : Nat := 118140960795 + 3782863 * 2 ^ 59
def prefixEnd_3782863 : Nat := 4983230072969 + 3 ^ 40 * 3782863 * 2
def baseEnd_3782863 : Nat := 431650437579808503292319

theorem tailTrace_3782863 : CollatzResearch.WordTrace tailWord_3782863 prefixEnd_3782863 431650437579808503292319 := by
  unfold tailWord_3782863
  simp only [CollatzResearch.WordTrace]
  refine ⟨137972348494340887409921243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91981565662893924939947495 137972348494340887409921243)
  ·
    refine ⟨206958522741511331114881865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137972348494340887409921243 206958522741511331114881865)
    ·
      refine ⟨155218892056133498336161399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206958522741511331114881865 155218892056133498336161399)
      ·
        refine ⟨232828338084200247504242099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155218892056133498336161399 232828338084200247504242099)
        ·
          refine ⟨349242507126300371256363149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232828338084200247504242099 349242507126300371256363149)
          ·
            refine ⟨130965940172362639221136181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349242507126300371256363149 130965940172362639221136181)
            ·
              refine ⟨12278056891158997426981517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130965940172362639221136181 12278056891158997426981517)
              ·
                refine ⟨4604271334184624035118069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12278056891158997426981517 4604271334184624035118069)
                ·
                  refine ⟨431650437579808503292319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604271334184624035118069 431650437579808503292319)
                  ·
                    rfl

theorem cell22_3782863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 5].length) (baseStart_3782863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782863 prefixEnd_3782863 := by exact prefixLift 3782863
  have htrace : WordTrace (prefixWord ++ tailWord_3782863) baseStart_3782863 baseEnd_3782863 := by
    simpa [prefixWord, tailWord_3782863, baseEnd_3782863] using wordTrace_append hprefix tailTrace_3782863
  have hstable : (prefixWord ++ tailWord_3782863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782863).length < 2 ^ (prefixWord ++ tailWord_3782863).sum := by decide
  have hdescent : baseEnd_3782863 < baseStart_3782863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782910 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3782910 : Nat := 118140960795 + 3782910 * 2 ^ 59
def prefixEnd_3782910 : Nat := 4983230072969 + 3 ^ 40 * 3782910 * 2
def baseEnd_3782910 : Nat := 1294967401799933053951813

theorem tailTrace_3782910 : CollatzResearch.WordTrace tailWord_3782910 prefixEnd_3782910 1294967401799933053951813 := by
  unfold tailWord_3782910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246757840646326804610273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91982708483447076291254789 17246757840646326804610273)
  ·
    refine ⟨12935068380484745103457705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17246757840646326804610273 12935068380484745103457705)
    ·
      refine ⟨9701301285363558827593279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12935068380484745103457705 9701301285363558827593279)
      ·
        refine ⟨14551951928045338241389919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701301285363558827593279 14551951928045338241389919)
        ·
          refine ⟨21827927892068007362084879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14551951928045338241389919 21827927892068007362084879)
          ·
            refine ⟨32741891838102011043127319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21827927892068007362084879 32741891838102011043127319)
            ·
              refine ⟨49112837757153016564690979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32741891838102011043127319 49112837757153016564690979)
              ·
                refine ⟨73669256635729524847036469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49112837757153016564690979 73669256635729524847036469)
                ·
                  refine ⟨6906492809599642954409669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73669256635729524847036469 6906492809599642954409669)
                  ·
                    refine ⟨1294967401799933053951813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6906492809599642954409669 1294967401799933053951813)
                    ·
                      rfl

theorem cell22_3782910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3782910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782910 prefixEnd_3782910 := by exact prefixLift 3782910
  have htrace : WordTrace (prefixWord ++ tailWord_3782910) baseStart_3782910 baseEnd_3782910 := by
    simpa [prefixWord, tailWord_3782910, baseEnd_3782910] using wordTrace_append hprefix tailTrace_3782910
  have hstable : (prefixWord ++ tailWord_3782910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782910).length < 2 ^ (prefixWord ++ tailWord_3782910).sum := by decide
  have hdescent : baseEnd_3782910 < baseStart_3782910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782940 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3782940 : Nat := 118140960795 + 3782940 * 2 ^ 59
def prefixEnd_3782940 : Nat := 4983230072969 + 3 ^ 40 * 3782940 * 2
def baseEnd_3782940 : Nat := 1294977671413022975701721

theorem tailTrace_3782940 : CollatzResearch.WordTrace tailWord_3782940 prefixEnd_3782940 1294977671413022975701721 := by
  unfold tailWord_3782940
  simp only [CollatzResearch.WordTrace]
  refine ⟨68987578457530964780237137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91983437943374619706982849 68987578457530964780237137)
  ·
    refine ⟨51740683843148223585177853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68987578457530964780237137 51740683843148223585177853)
    ·
      refine ⟨19402756441180583844441695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51740683843148223585177853 19402756441180583844441695)
      ·
        refine ⟨29104134661770875766662543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19402756441180583844441695 29104134661770875766662543)
        ·
          refine ⟨43656201992656313649993815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29104134661770875766662543 43656201992656313649993815)
          ·
            refine ⟨65484302988984470474990723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43656201992656313649993815 65484302988984470474990723)
            ·
              refine ⟨98226454483476705712486085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65484302988984470474990723 98226454483476705712486085)
              ·
                refine ⟨18417460215651882321091141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98226454483476705712486085 18417460215651882321091141)
                ·
                  refine ⟨3453273790434727935204589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18417460215651882321091141 3453273790434727935204589)
                  ·
                    refine ⟨1294977671413022975701721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453273790434727935204589 1294977671413022975701721)
                    ·
                      rfl

theorem cell22_3782940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3782940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782940 prefixEnd_3782940 := by exact prefixLift 3782940
  have htrace : WordTrace (prefixWord ++ tailWord_3782940) baseStart_3782940 baseEnd_3782940 := by
    simpa [prefixWord, tailWord_3782940, baseEnd_3782940] using wordTrace_append hprefix tailTrace_3782940
  have hstable : (prefixWord ++ tailWord_3782940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782940).length < 2 ^ (prefixWord ++ tailWord_3782940).sum := by decide
  have hdescent : baseEnd_3782940 < baseStart_3782940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3782944 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 1, 4]
def baseStart_3782944 : Nat := 118140960795 + 3782944 * 2 ^ 59
def prefixEnd_3782944 : Nat := 4983230072969 + 3 ^ 40 * 3782944 * 2
def baseEnd_3782944 : Nat := 1294979040694768298601709

theorem tailTrace_3782944 : CollatzResearch.WordTrace tailWord_3782944 prefixEnd_3782944 1294979040694768298601709 := by
  unfold tailWord_3782944
  simp only [CollatzResearch.WordTrace]
  refine ⟨68987651403523719121809943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91983535204698292162413257 68987651403523719121809943)
  ·
    refine ⟨103481477105285578682714915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68987651403523719121809943 103481477105285578682714915)
    ·
      refine ⟨155222215657928368024072373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103481477105285578682714915 155222215657928368024072373)
      ·
        refine ⟨14552082717930784502256785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155222215657928368024072373 14552082717930784502256785)
        ·
          refine ⟨10914062038448088376692589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14552082717930784502256785 10914062038448088376692589)
          ·
            refine ⟨4092773264418033141259721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10914062038448088376692589 4092773264418033141259721)
            ·
              refine ⟨3069579948313524855944791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092773264418033141259721 3069579948313524855944791)
              ·
                refine ⟨4604369922470287283917187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069579948313524855944791 4604369922470287283917187)
                ·
                  refine ⟨6906554883705430925875781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604369922470287283917187 6906554883705430925875781)
                  ·
                    refine ⟨1294979040694768298601709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6906554883705430925875781 1294979040694768298601709)
                    ·
                      rfl

theorem cell22_3782944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_3782944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3782944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3782944 prefixEnd_3782944 := by exact prefixLift 3782944
  have htrace : WordTrace (prefixWord ++ tailWord_3782944) baseStart_3782944 baseEnd_3782944 := by
    simpa [prefixWord, tailWord_3782944, baseEnd_3782944] using wordTrace_append hprefix tailTrace_3782944
  have hstable : (prefixWord ++ tailWord_3782944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3782944).length < 2 ^ (prefixWord ++ tailWord_3782944).sum := by decide
  have hdescent : baseEnd_3782944 < baseStart_3782944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3782944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783004 : List Nat := [2, 2, 4, 3, 2, 1, 8]
def baseStart_3783004 : Nat := 118140960795 + 3783004 * 2 ^ 59
def prefixEnd_3783004 : Nat := 4983230072969 + 3 ^ 40 * 3783004 * 2
def baseEnd_3783004 : Nat := 47962947404479560818575

theorem tailTrace_3783004 : CollatzResearch.WordTrace tailWord_3783004 prefixEnd_3783004 47962947404479560818575 := by
  unfold tailWord_3783004
  simp only [CollatzResearch.WordTrace]
  refine ⟨68988745593415034245402033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91984994124553378993869377 68988745593415034245402033)
  ·
    refine ⟨51741559195061275684051525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68988745593415034245402033 51741559195061275684051525)
    ·
      refine ⟨9701542349073989190759661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51741559195061275684051525 9701542349073989190759661)
      ·
        refine ⟨3638078380902745946534873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9701542349073989190759661 3638078380902745946534873)
        ·
          refine ⟨2728558785677059459901155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638078380902745946534873 2728558785677059459901155)
          ·
            refine ⟨4092838178515589189851733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728558785677059459901155 4092838178515589189851733)
            ·
              refine ⟨47962947404479560818575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4092838178515589189851733 47962947404479560818575)
              ·
                rfl

theorem cell22_3783004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 8].length) (baseStart_3783004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783004 prefixEnd_3783004 := by exact prefixLift 3783004
  have htrace : WordTrace (prefixWord ++ tailWord_3783004) baseStart_3783004 baseEnd_3783004 := by
    simpa [prefixWord, tailWord_3783004, baseEnd_3783004] using wordTrace_append hprefix tailTrace_3783004
  have hstable : (prefixWord ++ tailWord_3783004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783004).length < 2 ^ (prefixWord ++ tailWord_3783004).sum := by decide
  have hdescent : baseEnd_3783004 < baseStart_3783004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783015 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 7]
def baseStart_3783015 : Nat := 118140960795 + 3783015 * 2 ^ 59
def prefixEnd_3783015 : Nat := 4983230072969 + 3 ^ 40 * 3783015 * 2
def baseEnd_3783015 : Nat := 431667781815249260025497

theorem tailTrace_3783015 : CollatzResearch.WordTrace tailWord_3783015 prefixEnd_3783015 431667781815249260025497 := by
  unfold tailWord_3783015
  simp only [CollatzResearch.WordTrace]
  refine ⟨137977892389790217369454499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91985261593193478246302999 137977892389790217369454499)
  ·
    refine ⟨206966838584685326054181749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137977892389790217369454499 206966838584685326054181749)
    ·
      refine ⟨19403141117314249317579539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206966838584685326054181749 19403141117314249317579539)
      ·
        refine ⟨29104711675971373976369309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19403141117314249317579539 29104711675971373976369309)
        ·
          refine ⟨10914266878489265241138491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29104711675971373976369309 10914266878489265241138491)
          ·
            refine ⟨16371400317733897861707737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10914266878489265241138491 16371400317733897861707737)
            ·
              refine ⟨12278550238300423396280803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16371400317733897861707737 12278550238300423396280803)
              ·
                refine ⟨18417825357450635094421205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12278550238300423396280803 18417825357450635094421205)
                ·
                  refine ⟨431667781815249260025497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18417825357450635094421205 431667781815249260025497)
                  ·
                    rfl

theorem cell22_3783015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 7].length) (baseStart_3783015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783015 prefixEnd_3783015 := by exact prefixLift 3783015
  have htrace : WordTrace (prefixWord ++ tailWord_3783015) baseStart_3783015 baseEnd_3783015 := by
    simpa [prefixWord, tailWord_3783015, baseEnd_3783015] using wordTrace_append hprefix tailTrace_3783015
  have hstable : (prefixWord ++ tailWord_3783015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783015).length < 2 ^ (prefixWord ++ tailWord_3783015).sum := by decide
  have hdescent : baseEnd_3783015 < baseStart_3783015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783070 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3783070 : Nat := 118140960795 + 3783070 * 2 ^ 59
def prefixEnd_3783070 : Nat := 4983230072969 + 3 ^ 40 * 3783070 * 2
def baseEnd_3783070 : Nat := 1295022173069745969951323

theorem tailTrace_3783070 : CollatzResearch.WordTrace tailWord_3783070 prefixEnd_3783070 1295022173069745969951323 := by
  unfold tailWord_3783070
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247487300573870220338333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91986598936393974508471109 17247487300573870220338333)
  ·
    refine ⟨6467807737715201332626875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17247487300573870220338333 6467807737715201332626875)
    ·
      refine ⟨9701711606572801998940313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467807737715201332626875 9701711606572801998940313)
      ·
        refine ⟨7276283704929601499205235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9701711606572801998940313 7276283704929601499205235)
        ·
          refine ⟨10914425557394402248807853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276283704929601499205235 10914425557394402248807853)
          ·
            refine ⟨4092909584022900843302945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10914425557394402248807853 4092909584022900843302945)
            ·
              refine ⟨3069682188017175632477209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092909584022900843302945 3069682188017175632477209)
              ·
                refine ⟨2302261641012881724357907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069682188017175632477209 2302261641012881724357907)
                ·
                  refine ⟨3453392461519322586536861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302261641012881724357907 3453392461519322586536861)
                  ·
                    refine ⟨1295022173069745969951323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453392461519322586536861 1295022173069745969951323)
                    ·
                      rfl

theorem cell22_3783070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3783070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783070 prefixEnd_3783070 := by exact prefixLift 3783070
  have htrace : WordTrace (prefixWord ++ tailWord_3783070) baseStart_3783070 baseEnd_3783070 := by
    simpa [prefixWord, tailWord_3783070, baseEnd_3783070] using wordTrace_append hprefix tailTrace_3783070
  have hstable : (prefixWord ++ tailWord_3783070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783070).length < 2 ^ (prefixWord ++ tailWord_3783070).sum := by decide
  have hdescent : baseEnd_3783070 < baseStart_3783070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783077 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 4]
def baseStart_3783077 : Nat := 118140960795 + 3783077 * 2 ^ 59
def prefixEnd_3783077 : Nat := 4983230072969 + 3 ^ 40 * 3783077 * 2
def baseEnd_3783077 : Nat := 431674856437600095008767

theorem tailTrace_3783077 : CollatzResearch.WordTrace tailWord_3783077 prefixEnd_3783077 431674856437600095008767 := by
  unfold tailWord_3783077
  simp only [CollatzResearch.WordTrace]
  refine ⟨137980153715565601958211485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91986769143710401305474323 137980153715565601958211485)
  ·
    refine ⟨51742557643337100734329307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137980153715565601958211485 51742557643337100734329307)
    ·
      refine ⟨77613836465005651101493961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51742557643337100734329307 77613836465005651101493961)
      ·
        refine ⟨58210377348754238326120471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77613836465005651101493961 58210377348754238326120471)
        ·
          refine ⟨87315566023131357489180707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58210377348754238326120471 87315566023131357489180707)
          ·
            refine ⟨130973349034697036233771061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87315566023131357489180707 130973349034697036233771061)
            ·
              refine ⟨12278751472002847146916037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130973349034697036233771061 12278751472002847146916037)
              ·
                refine ⟨2302265901000533840046757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12278751472002847146916037 2302265901000533840046757)
                ·
                  refine ⟨431674856437600095008767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302265901000533840046757 431674856437600095008767)
                  ·
                    rfl

theorem cell22_3783077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_3783077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783077 prefixEnd_3783077 := by exact prefixLift 3783077
  have htrace : WordTrace (prefixWord ++ tailWord_3783077) baseStart_3783077 baseEnd_3783077 := by
    simpa [prefixWord, tailWord_3783077, baseEnd_3783077] using wordTrace_append hprefix tailTrace_3783077
  have hstable : (prefixWord ++ tailWord_3783077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783077).length < 2 ^ (prefixWord ++ tailWord_3783077).sum := by decide
  have hdescent : baseEnd_3783077 < baseStart_3783077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783090 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_3783090 : Nat := 118140960795 + 3783090 * 2 ^ 59
def prefixEnd_3783090 : Nat := 4983230072969 + 3 ^ 40 * 3783090 * 2
def baseEnd_3783090 : Nat := 1295029019478472584451261

theorem tailTrace_3783090 : CollatzResearch.WordTrace tailWord_3783090 prefixEnd_3783090 1295029019478472584451261 := by
  unfold tailWord_3783090
  simp only [CollatzResearch.WordTrace]
  refine ⟨34495156966129626294608681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91987085243012336785623149 34495156966129626294608681)
  ·
    refine ⟨25871367724597219720956511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34495156966129626294608681 25871367724597219720956511)
    ·
      refine ⟨38807051586895829581434767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25871367724597219720956511 38807051586895829581434767)
      ·
        refine ⟨58210577380343744372152151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38807051586895829581434767 58210577380343744372152151)
        ·
          refine ⟨87315866070515616558228227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58210577380343744372152151 87315866070515616558228227)
          ·
            refine ⟨130973799105773424837342341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87315866070515616558228227 130973799105773424837342341)
            ·
              refine ⟨24557587332332517157001689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130973799105773424837342341 24557587332332517157001689)
              ·
                refine ⟨18418190499249387867751267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24557587332332517157001689 18418190499249387867751267)
                ·
                  refine ⟨27627285748874081801626901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18418190499249387867751267 27627285748874081801626901)
                  ·
                    refine ⟨1295029019478472584451261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27627285748874081801626901 1295029019478472584451261)
                    ·
                      rfl

theorem cell22_3783090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_3783090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783090 prefixEnd_3783090 := by exact prefixLift 3783090
  have htrace : WordTrace (prefixWord ++ tailWord_3783090) baseStart_3783090 baseEnd_3783090 := by
    simpa [prefixWord, tailWord_3783090, baseEnd_3783090] using wordTrace_append hprefix tailTrace_3783090
  have hstable : (prefixWord ++ tailWord_3783090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783090).length < 2 ^ (prefixWord ++ tailWord_3783090).sum := by decide
  have hdescent : baseEnd_3783090 < baseStart_3783090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783188 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3783188 : Nat := 118140960795 + 3783188 * 2 ^ 59
def prefixEnd_3783188 : Nat := 4983230072969 + 3 ^ 40 * 3783188 * 2
def baseEnd_3783188 : Nat := 1295062566881232995500961

theorem tailTrace_3783188 : CollatzResearch.WordTrace tailWord_3783188 prefixEnd_3783188 1295062566881232995500961 := by
  unfold tailWord_3783188
  simp only [CollatzResearch.WordTrace]
  refine ⟨68992101109081733957751109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91989468145442311943668145 68992101109081733957751109)
  ·
    refine ⟨12936018957952825117078333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68992101109081733957751109 12936018957952825117078333)
    ·
      refine ⟨4851007109232309418904375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12936018957952825117078333 4851007109232309418904375)
      ·
        refine ⟨7276510663848464128356563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851007109232309418904375 7276510663848464128356563)
        ·
          refine ⟨10914765995772696192534845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276510663848464128356563 10914765995772696192534845)
          ·
            refine ⟨4093037248414761072200567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10914765995772696192534845 4093037248414761072200567)
            ·
              refine ⟨6139555872622141608300851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093037248414761072200567 6139555872622141608300851)
              ·
                refine ⟨9209333808933212412451277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139555872622141608300851 9209333808933212412451277)
                ·
                  refine ⟨3453500178349954654669229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9209333808933212412451277 3453500178349954654669229)
                  ·
                    refine ⟨1295062566881232995500961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453500178349954654669229 1295062566881232995500961)
                    ·
                      rfl

theorem cell22_3783188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3783188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783188 prefixEnd_3783188 := by exact prefixLift 3783188
  have htrace : WordTrace (prefixWord ++ tailWord_3783188) baseStart_3783188 baseEnd_3783188 := by
    simpa [prefixWord, tailWord_3783188, baseEnd_3783188] using wordTrace_append hprefix tailTrace_3783188
  have hstable : (prefixWord ++ tailWord_3783188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783188).length < 2 ^ (prefixWord ++ tailWord_3783188).sum := by decide
  have hdescent : baseEnd_3783188 < baseStart_3783188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783246 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 4]
def baseStart_3783246 : Nat := 118140960795 + 3783246 * 2 ^ 59
def prefixEnd_3783246 : Nat := 4983230072969 + 3 ^ 40 * 3783246 * 2
def baseEnd_3783246 : Nat := 431694140488846725850261

theorem tailTrace_3783246 : CollatzResearch.WordTrace tailWord_3783246 prefixEnd_3783246 431694140488846725850261 := by
  unfold tailWord_3783246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17248289706494167977639199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91990878434635562547409061 17248289706494167977639199)
  ·
    refine ⟨25872434559741251966458799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17248289706494167977639199 25872434559741251966458799)
    ·
      refine ⟨38808651839611877949688199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25872434559741251966458799 38808651839611877949688199)
      ·
        refine ⟨58212977759417816924532299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38808651839611877949688199 58212977759417816924532299)
        ·
          refine ⟨87319466639126725386798449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58212977759417816924532299 87319466639126725386798449)
          ·
            refine ⟨65489599979345044040098837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87319466639126725386798449 65489599979345044040098837)
            ·
              refine ⟨3069824999031798939379633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65489599979345044040098837 3069824999031798939379633)
              ·
                refine ⟨2302368749273849204534725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069824999031798939379633 2302368749273849204534725)
                ·
                  refine ⟨431694140488846725850261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302368749273849204534725 431694140488846725850261)
                  ·
                    rfl

theorem cell22_3783246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_3783246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783246 prefixEnd_3783246 := by exact prefixLift 3783246
  have htrace : WordTrace (prefixWord ++ tailWord_3783246) baseStart_3783246 baseEnd_3783246 := by
    simpa [prefixWord, tailWord_3783246, baseEnd_3783246] using wordTrace_append hprefix tailTrace_3783246
  have hstable : (prefixWord ++ tailWord_3783246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783246).length < 2 ^ (prefixWord ++ tailWord_3783246).sum := by decide
  have hdescent : baseEnd_3783246 < baseStart_3783246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783274 : List Nat := [3, 1, 3, 2, 1, 1, 5, 6]
def baseStart_3783274 : Nat := 118140960795 + 3783274 * 2 ^ 59
def prefixEnd_3783274 : Nat := 4983230072969 + 3 ^ 40 * 3783274 * 2
def baseEnd_3783274 : Nat := 143899111826528604205633

theorem tailTrace_3783274 : CollatzResearch.WordTrace tailWord_3783274 prefixEnd_3783274 143899111826528604205633 := by
  unfold tailWord_3783274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34496834723962976150783219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91991559263901269735421917 34496834723962976150783219)
  ·
    refine ⟨51745252085944464226174829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34496834723962976150783219 51745252085944464226174829)
    ·
      refine ⟨19404469532229174084815561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51745252085944464226174829 19404469532229174084815561)
      ·
        refine ⟨14553352149171880563611671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19404469532229174084815561 14553352149171880563611671)
        ·
          refine ⟨21830028223757820845417507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14553352149171880563611671 21830028223757820845417507)
          ·
            refine ⟨32745042335636731268126261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21830028223757820845417507 32745042335636731268126261)
            ·
              refine ⟨3069847718965943556386837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32745042335636731268126261 3069847718965943556386837)
              ·
                refine ⟨143899111826528604205633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3069847718965943556386837 143899111826528604205633)
                ·
                  rfl

theorem cell22_3783274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_3783274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783274 prefixEnd_3783274 := by exact prefixLift 3783274
  have htrace : WordTrace (prefixWord ++ tailWord_3783274) baseStart_3783274 baseEnd_3783274 := by
    simpa [prefixWord, tailWord_3783274, baseEnd_3783274] using wordTrace_append hprefix tailTrace_3783274
  have hstable : (prefixWord ++ tailWord_3783274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783274).length < 2 ^ (prefixWord ++ tailWord_3783274).sum := by decide
  have hdescent : baseEnd_3783274 < baseStart_3783274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783426 : List Nat := [3, 4, 1, 1, 1, 2, 3, 7]
def baseStart_3783426 : Nat := 118140960795 + 3783426 * 2 ^ 59
def prefixEnd_3783426 : Nat := 4983230072969 + 3 ^ 40 * 3783426 * 2
def baseEnd_3783426 : Nat := 143904893238342189783359

theorem tailTrace_3783426 : CollatzResearch.WordTrace tailWord_3783426 prefixEnd_3783426 143904893238342189783359 := by
  unfold tailWord_3783426
  simp only [CollatzResearch.WordTrace]
  refine ⟨34498220697825308640666533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91995255194200823041777421 34498220697825308640666533)
  ·
    refine ⟨6468416380842245370124975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34498220697825308640666533 6468416380842245370124975)
    ·
      refine ⟨9702624571263368055187463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468416380842245370124975 9702624571263368055187463)
      ·
        refine ⟨14553936856895052082781195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9702624571263368055187463 14553936856895052082781195)
        ·
          refine ⟨21830905285342578124171793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14553936856895052082781195 21830905285342578124171793)
          ·
            refine ⟨16373178964006933593128845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21830905285342578124171793 16373178964006933593128845)
            ·
              refine ⟨6139942111502600097423317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16373178964006933593128845 6139942111502600097423317)
              ·
                refine ⟨143904893238342189783359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6139942111502600097423317 143904893238342189783359)
                ·
                  rfl

theorem cell22_3783426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 7].length) (baseStart_3783426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783426 prefixEnd_3783426 := by exact prefixLift 3783426
  have htrace : WordTrace (prefixWord ++ tailWord_3783426) baseStart_3783426 baseEnd_3783426 := by
    simpa [prefixWord, tailWord_3783426, baseEnd_3783426] using wordTrace_append hprefix tailTrace_3783426
  have hstable : (prefixWord ++ tailWord_3783426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783426).length < 2 ^ (prefixWord ++ tailWord_3783426).sum := by decide
  have hdescent : baseEnd_3783426 < baseStart_3783426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783531 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 4, 3]
def baseStart_3783531 : Nat := 118140960795 + 3783531 * 2 ^ 59
def prefixEnd_3783531 : Nat := 4983230072969 + 3 ^ 40 * 3783531 * 2
def baseEnd_3783531 : Nat := 1295179982790894434174909

theorem tailTrace_3783531 : CollatzResearch.WordTrace tailWord_3783531 prefixEnd_3783531 1295179982790894434174909 := by
  unfold tailWord_3783531
  simp only [CollatzResearch.WordTrace]
  refine ⟨137996712455920837495238447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91997808303947224996825631 137996712455920837495238447)
  ·
    refine ⟨206995068683881256242857671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137996712455920837495238447 206995068683881256242857671)
    ·
      refine ⟨310492603025821884364286507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206995068683881256242857671 310492603025821884364286507)
      ·
        refine ⟨465738904538732826546429761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310492603025821884364286507 465738904538732826546429761)
        ·
          refine ⟨349304178404049619909822321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465738904538732826546429761 349304178404049619909822321)
          ·
            refine ⟨261978133803037214932366741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349304178404049619909822321 261978133803037214932366741)
            ·
              refine ⟨12280225022017369449954691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 261978133803037214932366741 12280225022017369449954691)
              ·
                refine ⟨18420337533026054174932037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12280225022017369449954691 18420337533026054174932037)
                ·
                  refine ⟨3453813287442385157799757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18420337533026054174932037 3453813287442385157799757)
                  ·
                    refine ⟨1295179982790894434174909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453813287442385157799757 1295179982790894434174909)
                    ·
                      rfl

theorem cell22_3783531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 3].length) (baseStart_3783531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783531 prefixEnd_3783531 := by exact prefixLift 3783531
  have htrace : WordTrace (prefixWord ++ tailWord_3783531) baseStart_3783531 baseEnd_3783531 := by
    simpa [prefixWord, tailWord_3783531, baseEnd_3783531] using wordTrace_append hprefix tailTrace_3783531
  have hstable : (prefixWord ++ tailWord_3783531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783531).length < 2 ^ (prefixWord ++ tailWord_3783531).sum := by decide
  have hdescent : baseEnd_3783531 < baseStart_3783531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783670 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3783670 : Nat := 118140960795 + 3783670 * 2 ^ 59
def prefixEnd_3783670 : Nat := 4983230072969 + 3 ^ 40 * 3783670 * 2
def baseEnd_3783670 : Nat := 1295227565331544404949483

theorem tailTrace_3783670 : CollatzResearch.WordTrace tailWord_3783670 prefixEnd_3783670 1295227565331544404949483 := by
  unfold tailWord_3783670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8625111387651079014659279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92001188134944842823032309 8625111387651079014659279)
  ·
    refine ⟨12937667081476618521988919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8625111387651079014659279 12937667081476618521988919)
    ·
      refine ⟨19406500622214927782983379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12937667081476618521988919 19406500622214927782983379)
      ·
        refine ⟨29109750933322391674475069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19406500622214927782983379 29109750933322391674475069)
        ·
          refine ⟨10916156599995896877928151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29109750933322391674475069 10916156599995896877928151)
          ·
            refine ⟨16374234899993845316892227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916156599995896877928151 16374234899993845316892227)
            ·
              refine ⟨24561352349990767975338341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16374234899993845316892227 24561352349990767975338341)
              ·
                refine ⟨4605253565623268995375939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24561352349990767975338341 4605253565623268995375939)
                ·
                  refine ⟨6907880348434903493063909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605253565623268995375939 6907880348434903493063909)
                  ·
                    refine ⟨1295227565331544404949483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907880348434903493063909 1295227565331544404949483)
                    ·
                      rfl

theorem cell22_3783670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3783670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783670 prefixEnd_3783670 := by exact prefixLift 3783670
  have htrace : WordTrace (prefixWord ++ tailWord_3783670) baseStart_3783670 baseEnd_3783670 := by
    simpa [prefixWord, tailWord_3783670, baseEnd_3783670] using wordTrace_append hprefix tailTrace_3783670
  have hstable : (prefixWord ++ tailWord_3783670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783670).length < 2 ^ (prefixWord ++ tailWord_3783670).sum := by decide
  have hdescent : baseEnd_3783670 < baseStart_3783670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783713 : List Nat := [1, 2, 3, 2, 3, 2, 2, 7]
def baseStart_3783713 : Nat := 118140960795 + 3783713 * 2 ^ 59
def prefixEnd_3783713 : Nat := 4983230072969 + 3 ^ 40 * 3783713 * 2
def baseEnd_3783713 : Nat := 143915809456700736236039

theorem tailTrace_3783713 : CollatzResearch.WordTrace tailWord_3783713 prefixEnd_3783713 143915809456700736236039 := by
  unfold tailWord_3783713
  simp only [CollatzResearch.WordTrace]
  refine ⟨138003350541261482578363793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92002233694174321718909195 138003350541261482578363793)
  ·
    refine ⟨103502512905946111933772845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138003350541261482578363793 103502512905946111933772845)
    ·
      refine ⟨38813442339729791975164817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103502512905946111933772845 38813442339729791975164817)
      ·
        refine ⟨29110081754797343981373613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38813442339729791975164817 29110081754797343981373613)
        ·
          refine ⟨10916280658049003993015105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29110081754797343981373613 10916280658049003993015105)
          ·
            refine ⟨8187210493536752994761329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10916280658049003993015105 8187210493536752994761329)
            ·
              refine ⟨6140407870152564746070997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8187210493536752994761329 6140407870152564746070997)
              ·
                refine ⟨143915809456700736236039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6140407870152564746070997 143915809456700736236039)
                ·
                  rfl

theorem cell22_3783713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 7].length) (baseStart_3783713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783713 prefixEnd_3783713 := by exact prefixLift 3783713
  have htrace : WordTrace (prefixWord ++ tailWord_3783713) baseStart_3783713 baseEnd_3783713 := by
    simpa [prefixWord, tailWord_3783713, baseEnd_3783713] using wordTrace_append hprefix tailTrace_3783713
  have hstable : (prefixWord ++ tailWord_3783713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783713).length < 2 ^ (prefixWord ++ tailWord_3783713).sum := by decide
  have hdescent : baseEnd_3783713 < baseStart_3783713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783728 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_3783728 : Nat := 118140960795 + 3783728 * 2 ^ 59
def prefixEnd_3783728 : Nat := 4983230072969 + 3 ^ 40 * 3783728 * 2
def baseEnd_3783728 : Nat := 1295247419916851586999305

theorem tailTrace_3783728 : CollatzResearch.WordTrace tailWord_3783728 prefixEnd_3783728 1295247419916851586999305 := by
  unfold tailWord_3783728
  simp only [CollatzResearch.WordTrace]
  refine ⟨69001948818103570070079919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92002598424138093426773225 69001948818103570070079919)
  ·
    refine ⟨103502923227155355105119879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69001948818103570070079919 103502923227155355105119879)
    ·
      refine ⟨155254384840733032657679819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103502923227155355105119879 155254384840733032657679819)
      ·
        refine ⟨232881577261099548986519729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155254384840733032657679819 232881577261099548986519729)
        ·
          refine ⟨174661182945824661739889797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232881577261099548986519729 174661182945824661739889797)
          ·
            refine ⟨32748971802342124076229337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174661182945824661739889797 32748971802342124076229337)
            ·
              refine ⟨24561728851756593057172003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32748971802342124076229337 24561728851756593057172003)
              ·
                refine ⟨36842593277634889585758005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24561728851756593057172003 36842593277634889585758005)
                ·
                  refine ⟨3453993119778270898664813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36842593277634889585758005 3453993119778270898664813)
                  ·
                    refine ⟨1295247419916851586999305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3453993119778270898664813 1295247419916851586999305)
                    ·
                      rfl

theorem cell22_3783728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_3783728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783728 prefixEnd_3783728 := by exact prefixLift 3783728
  have htrace : WordTrace (prefixWord ++ tailWord_3783728) baseStart_3783728 baseEnd_3783728 := by
    simpa [prefixWord, tailWord_3783728, baseEnd_3783728] using wordTrace_append hprefix tailTrace_3783728
  have hstable : (prefixWord ++ tailWord_3783728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783728).length < 2 ^ (prefixWord ++ tailWord_3783728).sum := by decide
  have hdescent : baseEnd_3783728 < baseStart_3783728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783732 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3783732 : Nat := 118140960795 + 3783732 * 2 ^ 59
def prefixEnd_3783732 : Nat := 4983230072969 + 3 ^ 40 * 3783732 * 2
def baseEnd_3783732 : Nat := 1295248789198596909899293

theorem tailTrace_3783732 : CollatzResearch.WordTrace tailWord_3783732 prefixEnd_3783732 1295248789198596909899293 := by
  unfold tailWord_3783732
  simp only [CollatzResearch.WordTrace]
  refine ⟨69002021764096324411652725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92002695685461765882203633 69002021764096324411652725)
  ·
    refine ⟨6468939540384030413592443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69002021764096324411652725 6468939540384030413592443)
    ·
      refine ⟨9703409310576045620388665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468939540384030413592443 9703409310576045620388665)
      ·
        refine ⟨7277556982932034215291499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703409310576045620388665 7277556982932034215291499)
        ·
          refine ⟨10916335474398051322937249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277556982932034215291499 10916335474398051322937249)
          ·
            refine ⟨8187251605798538492202937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10916335474398051322937249 8187251605798538492202937)
            ·
              refine ⟨6140438704348903869152203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8187251605798538492202937 6140438704348903869152203)
              ·
                refine ⟨9210658056523355803728305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140438704348903869152203 9210658056523355803728305)
                ·
                  refine ⟨6907993542392516852796229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9210658056523355803728305 6907993542392516852796229)
                  ·
                    refine ⟨1295248789198596909899293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6907993542392516852796229 1295248789198596909899293)
                    ·
                      rfl

theorem cell22_3783732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3783732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783732 prefixEnd_3783732 := by exact prefixLift 3783732
  have htrace : WordTrace (prefixWord ++ tailWord_3783732) baseStart_3783732 baseEnd_3783732 := by
    simpa [prefixWord, tailWord_3783732, baseEnd_3783732] using wordTrace_append hprefix tailTrace_3783732
  have hstable : (prefixWord ++ tailWord_3783732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783732).length < 2 ^ (prefixWord ++ tailWord_3783732).sum := by decide
  have hdescent : baseEnd_3783732 < baseStart_3783732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783788 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_3783788 : Nat := 118140960795 + 3783788 * 2 ^ 59
def prefixEnd_3783788 : Nat := 4983230072969 + 3 ^ 40 * 3783788 * 2
def baseEnd_3783788 : Nat := 1295267959143031430499121

theorem tailTrace_3783788 : CollatzResearch.WordTrace tailWord_3783788 prefixEnd_3783788 1295267959143031430499121 := by
  unfold tailWord_3783788
  simp only [CollatzResearch.WordTrace]
  refine ⟨69003043007994885193672009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92004057343993180258229345 69003043007994885193672009)
  ·
    refine ⟨51752282255996163895254007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69003043007994885193672009 51752282255996163895254007)
    ·
      refine ⟨77628423383994245842881011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51752282255996163895254007 77628423383994245842881011)
      ·
        refine ⟨116442635075991368764321517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77628423383994245842881011 116442635075991368764321517)
        ·
          refine ⟨43665988153496763286620569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116442635075991368764321517 43665988153496763286620569)
          ·
            refine ⟨32749491115122572464965427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43665988153496763286620569 32749491115122572464965427)
            ·
              refine ⟨49124236672683858697448141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32749491115122572464965427 49124236672683858697448141)
              ·
                refine ⟨18421588752256447011543053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49124236672683858697448141 18421588752256447011543053)
                ·
                  refine ⟨6908095782096167629328645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18421588752256447011543053 6908095782096167629328645)
                  ·
                    refine ⟨1295267959143031430499121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6908095782096167629328645 1295267959143031430499121)
                    ·
                      rfl

theorem cell22_3783788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_3783788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783788 prefixEnd_3783788 := by exact prefixLift 3783788
  have htrace : WordTrace (prefixWord ++ tailWord_3783788) baseStart_3783788 baseEnd_3783788 := by
    simpa [prefixWord, tailWord_3783788, baseEnd_3783788] using wordTrace_append hprefix tailTrace_3783788
  have hstable : (prefixWord ++ tailWord_3783788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783788).length < 2 ^ (prefixWord ++ tailWord_3783788).sum := by decide
  have hdescent : baseEnd_3783788 < baseStart_3783788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783805 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3783805 : Nat := 118140960795 + 3783805 * 2 ^ 59
def prefixEnd_3783805 : Nat := 4983230072969 + 3 ^ 40 * 3783805 * 2
def baseEnd_3783805 : Nat := 1295273778590449052824069

theorem tailTrace_3783805 : CollatzResearch.WordTrace tailWord_3783805 prefixEnd_3783805 1295273778590449052824069 := by
  unfold tailWord_3783805
  simp only [CollatzResearch.WordTrace]
  refine ⟨138006706056928182290712869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92004470704618788193808579 138006706056928182290712869)
  ·
    refine ⟨25876257385674034179508663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138006706056928182290712869 25876257385674034179508663)
    ·
      refine ⟨38814386078511051269262995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25876257385674034179508663 38814386078511051269262995)
      ·
        refine ⟨58221579117766576903894493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38814386078511051269262995 58221579117766576903894493)
        ·
          refine ⟨21833092169162466338960435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58221579117766576903894493 21833092169162466338960435)
          ·
            refine ⟨32749638253743699508440653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21833092169162466338960435 32749638253743699508440653)
            ·
              refine ⟨12281114345153887315665245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32749638253743699508440653 12281114345153887315665245)
              ·
                refine ⟨4605417879432707743374467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12281114345153887315665245 4605417879432707743374467)
                ·
                  refine ⟨6908126819149061615061701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605417879432707743374467 6908126819149061615061701)
                  ·
                    refine ⟨1295273778590449052824069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6908126819149061615061701 1295273778590449052824069)
                    ·
                      rfl

theorem cell22_3783805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3783805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783805 prefixEnd_3783805 := by exact prefixLift 3783805
  have htrace : WordTrace (prefixWord ++ tailWord_3783805) baseStart_3783805 baseEnd_3783805 := by
    simpa [prefixWord, tailWord_3783805, baseEnd_3783805] using wordTrace_append hprefix tailTrace_3783805
  have hstable : (prefixWord ++ tailWord_3783805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783805).length < 2 ^ (prefixWord ++ tailWord_3783805).sum := by decide
  have hdescent : baseEnd_3783805 < baseStart_3783805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783886 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3783886 : Nat := 118140960795 + 3783886 * 2 ^ 59
def prefixEnd_3783886 : Nat := 4983230072969 + 3 ^ 40 * 3783886 * 2
def baseEnd_3783886 : Nat := 1295301506545791841548821

theorem tailTrace_3783886 : CollatzResearch.WordTrace tailWord_3783886 prefixEnd_3783886 1295301506545791841548821 := by
  unfold tailWord_3783886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251207546204341640551439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92006440246423155416274341 17251207546204341640551439)
  ·
    refine ⟨25876811319306512460827159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17251207546204341640551439 25876811319306512460827159)
    ·
      refine ⟨38815216978959768691240739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25876811319306512460827159 38815216978959768691240739)
      ·
        refine ⟨58222825468439653036861109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38815216978959768691240739 58222825468439653036861109)
        ·
          refine ⟨5458389887666217472205729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58222825468439653036861109 5458389887666217472205729)
          ·
            refine ⟨4093792415749663104154297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458389887666217472205729 4093792415749663104154297)
            ·
              refine ⟨3070344311812247328115723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4093792415749663104154297 3070344311812247328115723)
              ·
                refine ⟨4605516467718370992173585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070344311812247328115723 4605516467718370992173585)
                ·
                  refine ⟨3454137350788778244130189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4605516467718370992173585 3454137350788778244130189)
                  ·
                    refine ⟨1295301506545791841548821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454137350788778244130189 1295301506545791841548821)
                    ·
                      rfl

theorem cell22_3783886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3783886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783886 prefixEnd_3783886 := by exact prefixLift 3783886
  have htrace : WordTrace (prefixWord ++ tailWord_3783886) baseStart_3783886 baseEnd_3783886 := by
    simpa [prefixWord, tailWord_3783886, baseEnd_3783886] using wordTrace_append hprefix tailTrace_3783886
  have hstable : (prefixWord ++ tailWord_3783886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783886).length < 2 ^ (prefixWord ++ tailWord_3783886).sum := by decide
  have hdescent : baseEnd_3783886 < baseStart_3783886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3783987 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 4, 3]
def baseStart_3783987 : Nat := 118140960795 + 3783987 * 2 ^ 59
def prefixEnd_3783987 : Nat := 4983230072969 + 3 ^ 40 * 3783987 * 2
def baseEnd_3783987 : Nat := 1295336080909861244773511

theorem tailTrace_3783987 : CollatzResearch.WordTrace tailWord_3783987 prefixEnd_3783987 1295336080909861244773511 := by
  unfold tailWord_3783987
  simp only [CollatzResearch.WordTrace]
  refine ⟨138013344142268827373838215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92008896094845884915892143 138013344142268827373838215)
  ·
    refine ⟨207020016213403241060757323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138013344142268827373838215 207020016213403241060757323)
    ·
      refine ⟨310530024320104861591135985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207020016213403241060757323 310530024320104861591135985)
      ·
        refine ⟨232897518240078646193351989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310530024320104861591135985 232897518240078646193351989)
        ·
          refine ⟨21834142335007373080626749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232897518240078646193351989 21834142335007373080626749)
          ·
            refine ⟨8187803375627764905235031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21834142335007373080626749 8187803375627764905235031)
            ·
              refine ⟨12281705063441647357852547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187803375627764905235031 12281705063441647357852547)
              ·
                refine ⟨18422557595162471036778821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12281705063441647357852547 18422557595162471036778821)
                ·
                  refine ⟨3454229549092963319396029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18422557595162471036778821 3454229549092963319396029)
                  ·
                    refine ⟨1295336080909861244773511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454229549092963319396029 1295336080909861244773511)
                    ·
                      rfl

theorem cell22_3783987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 3].length) (baseStart_3783987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3783987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3783987 prefixEnd_3783987 := by exact prefixLift 3783987
  have htrace : WordTrace (prefixWord ++ tailWord_3783987) baseStart_3783987 baseEnd_3783987 := by
    simpa [prefixWord, tailWord_3783987, baseEnd_3783987] using wordTrace_append hprefix tailTrace_3783987
  have hstable : (prefixWord ++ tailWord_3783987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3783987).length < 2 ^ (prefixWord ++ tailWord_3783987).sum := by decide
  have hdescent : baseEnd_3783987 < baseStart_3783987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3783987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784004 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3784004 : Nat := 118140960795 + 3784004 * 2 ^ 59
def prefixEnd_3784004 : Nat := 4983230072969 + 3 ^ 40 * 3784004 * 2
def baseEnd_3784004 : Nat := 1295341900357278867098459

theorem tailTrace_3784004 : CollatzResearch.WordTrace tailWord_3784004 prefixEnd_3784004 1295341900357278867098459 := by
  unfold tailWord_3784004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69006982091603619638603533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92009309455471492851471377 69006982091603619638603533)
  ·
    refine ⟨25877618284351357364476325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69006982091603619638603533 25877618284351357364476325)
    ·
      refine ⟨4852053428315879505839311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25877618284351357364476325 4852053428315879505839311)
      ·
        refine ⟨7278080142473819258758967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4852053428315879505839311 7278080142473819258758967)
        ·
          refine ⟨10917120213710728888138451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278080142473819258758967 10917120213710728888138451)
          ·
            refine ⟨16375680320566093332207677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917120213710728888138451 16375680320566093332207677)
            ·
              refine ⟨6140880120212284999577879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16375680320566093332207677 6140880120212284999577879)
              ·
                refine ⟨9211320180318427499366819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140880120212284999577879 9211320180318427499366819)
                ·
                  refine ⟨13816980270477641249050229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211320180318427499366819 13816980270477641249050229)
                  ·
                    refine ⟨1295341900357278867098459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13816980270477641249050229 1295341900357278867098459)
                    ·
                      rfl

theorem cell22_3784004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3784004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784004 prefixEnd_3784004 := by exact prefixLift 3784004
  have htrace : WordTrace (prefixWord ++ tailWord_3784004) baseStart_3784004 baseEnd_3784004 := by
    simpa [prefixWord, tailWord_3784004, baseEnd_3784004] using wordTrace_append hprefix tailTrace_3784004
  have hstable : (prefixWord ++ tailWord_3784004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784004).length < 2 ^ (prefixWord ++ tailWord_3784004).sum := by decide
  have hdescent : baseEnd_3784004 < baseStart_3784004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784049 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 1, 3]
def baseStart_3784049 : Nat := 118140960795 + 3784049 * 2 ^ 59
def prefixEnd_3784049 : Nat := 4983230072969 + 3 ^ 40 * 3784049 * 2
def baseEnd_3784049 : Nat := 1295357304776913749723321

theorem tailTrace_3784049 : CollatzResearch.WordTrace tailWord_3784049 prefixEnd_3784049 1295357304776913749723321 := by
  unfold tailWord_3784049
  simp only [CollatzResearch.WordTrace]
  refine ⟨138015605468044211962595201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92010403645362807975063467 138015605468044211962595201)
  ·
    refine ⟨103511704101033158971946401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138015605468044211962595201 103511704101033158971946401)
    ·
      refine ⟨77633778075774869228959801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103511704101033158971946401 77633778075774869228959801)
      ·
        refine ⟨58225333556831151921719851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77633778075774869228959801 58225333556831151921719851)
        ·
          refine ⟨87338000335246727882579777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58225333556831151921719851 87338000335246727882579777)
          ·
            refine ⟨65503500251435045911934833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87338000335246727882579777 65503500251435045911934833)
            ·
              refine ⟨49127625188576284433951125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65503500251435045911934833 49127625188576284433951125)
              ·
                refine ⟨2302857430714513332841459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49127625188576284433951125 2302857430714513332841459)
                ·
                  refine ⟨3454286146071769999262189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302857430714513332841459 3454286146071769999262189)
                  ·
                    refine ⟨1295357304776913749723321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454286146071769999262189 1295357304776913749723321)
                    ·
                      rfl

theorem cell22_3784049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_3784049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784049 prefixEnd_3784049 := by exact prefixLift 3784049
  have htrace : WordTrace (prefixWord ++ tailWord_3784049) baseStart_3784049 baseEnd_3784049 := by
    simpa [prefixWord, tailWord_3784049, baseEnd_3784049] using wordTrace_append hprefix tailTrace_3784049
  have hstable : (prefixWord ++ tailWord_3784049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784049).length < 2 ^ (prefixWord ++ tailWord_3784049).sum := by decide
  have hdescent : baseEnd_3784049 < baseStart_3784049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784060 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3784060 : Nat := 118140960795 + 3784060 * 2 ^ 59
def prefixEnd_3784060 : Nat := 4983230072969 + 3 ^ 40 * 3784060 * 2
def baseEnd_3784060 : Nat := 1295361070301713387698287

theorem tailTrace_3784060 : CollatzResearch.WordTrace tailWord_3784060 prefixEnd_3784060 1295361070301713387698287 := by
  unfold tailWord_3784060
  simp only [CollatzResearch.WordTrace]
  refine ⟨69008003335502180420622817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92010671114002907227497089 69008003335502180420622817)
  ·
    refine ⟨51756002501626635315467113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69008003335502180420622817 51756002501626635315467113)
    ·
      refine ⟨38817001876219976486600335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51756002501626635315467113 38817001876219976486600335)
      ·
        refine ⟨58225502814329964729900503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38817001876219976486600335 58225502814329964729900503)
        ·
          refine ⟨87338254221494947094850755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58225502814329964729900503 87338254221494947094850755)
          ·
            refine ⟨131007381332242420642276133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87338254221494947094850755 131007381332242420642276133)
            ·
              refine ⟨24563883999795453870426775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131007381332242420642276133 24563883999795453870426775)
              ·
                refine ⟨36845825999693180805640163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24563883999795453870426775 36845825999693180805640163)
                ·
                  refine ⟨55268738999539771208460245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36845825999693180805640163 55268738999539771208460245)
                  ·
                    refine ⟨1295361070301713387698287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55268738999539771208460245 1295361070301713387698287)
                    ·
                      rfl

theorem cell22_3784060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3784060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784060 prefixEnd_3784060 := by exact prefixLift 3784060
  have htrace : WordTrace (prefixWord ++ tailWord_3784060) baseStart_3784060 baseEnd_3784060 := by
    simpa [prefixWord, tailWord_3784060, baseEnd_3784060] using wordTrace_append hprefix tailTrace_3784060
  have hstable : (prefixWord ++ tailWord_3784060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784060).length < 2 ^ (prefixWord ++ tailWord_3784060).sum := by decide
  have hdescent : baseEnd_3784060 < baseStart_3784060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784109 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3784109 : Nat := 118140960795 + 3784109 * 2 ^ 59
def prefixEnd_3784109 : Nat := 4983230072969 + 3 ^ 40 * 3784109 * 2
def baseEnd_3784109 : Nat := 1295377844003093593223137

theorem tailTrace_3784109 : CollatzResearch.WordTrace tailWord_3784109 prefixEnd_3784109 1295377844003093593223137 := by
  unfold tailWord_3784109
  simp only [CollatzResearch.WordTrace]
  refine ⟨138017793847826842209779381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92011862565217894806519587 138017793847826842209779381)
  ·
    refine ⟨12939168173233766457166817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138017793847826842209779381 12939168173233766457166817)
    ·
      refine ⟨9704376129925324842875113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12939168173233766457166817 9704376129925324842875113)
      ·
        refine ⟨7278282097443993632156335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9704376129925324842875113 7278282097443993632156335)
        ·
          refine ⟨10917423146165990448234503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278282097443993632156335 10917423146165990448234503)
          ·
            refine ⟨16376134719248985672351755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917423146165990448234503 16376134719248985672351755)
            ·
              refine ⟨24564202078873478508527633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16376134719248985672351755 24564202078873478508527633)
              ·
                refine ⟨18423151559155108881395725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24564202078873478508527633 18423151559155108881395725)
                ·
                  refine ⟨6908681834683165830523397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18423151559155108881395725 6908681834683165830523397)
                  ·
                    refine ⟨1295377844003093593223137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6908681834683165830523397 1295377844003093593223137)
                    ·
                      rfl

theorem cell22_3784109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3784109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784109 prefixEnd_3784109 := by exact prefixLift 3784109
  have htrace : WordTrace (prefixWord ++ tailWord_3784109) baseStart_3784109 baseEnd_3784109 := by
    simpa [prefixWord, tailWord_3784109, baseEnd_3784109] using wordTrace_append hprefix tailTrace_3784109
  have hstable : (prefixWord ++ tailWord_3784109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784109).length < 2 ^ (prefixWord ++ tailWord_3784109).sum := by decide
  have hdescent : baseEnd_3784109 < baseStart_3784109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784122 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_3784122 : Nat := 118140960795 + 3784122 * 2 ^ 59
def prefixEnd_3784122 : Nat := 4983230072969 + 3 ^ 40 * 3784122 * 2
def baseEnd_3784122 : Nat := 1295382294168765892648097

theorem tailTrace_3784122 : CollatzResearch.WordTrace tailWord_3784122 prefixEnd_3784122 1295382294168765892648097 := by
  unfold tailWord_3784122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34504566999194936357500655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92012178664519830286668413 34504566999194936357500655)
  ·
    refine ⟨51756850498792404536250983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34504566999194936357500655 51756850498792404536250983)
    ·
      refine ⟨77635275748188606804376475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51756850498792404536250983 77635275748188606804376475)
      ·
        refine ⟨116452913622282910206564713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77635275748188606804376475 116452913622282910206564713)
        ·
          refine ⟨87339685216712182654923535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116452913622282910206564713 87339685216712182654923535)
          ·
            refine ⟨131009527825068273982385303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87339685216712182654923535 131009527825068273982385303)
            ·
              refine ⟨196514291737602410973577955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131009527825068273982385303 196514291737602410973577955)
              ·
                refine ⟨294771437606403616460366933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196514291737602410973577955 294771437606403616460366933)
                ·
                  refine ⟨3454352784450042380394925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 294771437606403616460366933 3454352784450042380394925)
                  ·
                    refine ⟨1295382294168765892648097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454352784450042380394925 1295382294168765892648097)
                    ·
                      rfl

theorem cell22_3784122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_3784122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784122 prefixEnd_3784122 := by exact prefixLift 3784122
  have htrace : WordTrace (prefixWord ++ tailWord_3784122) baseStart_3784122 baseEnd_3784122 := by
    simpa [prefixWord, tailWord_3784122, baseEnd_3784122] using wordTrace_append hprefix tailTrace_3784122
  have hstable : (prefixWord ++ tailWord_3784122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784122).length < 2 ^ (prefixWord ++ tailWord_3784122).sum := by decide
  have hdescent : baseEnd_3784122 < baseStart_3784122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784124 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_3784124 : Nat := 118140960795 + 3784124 * 2 ^ 59
def prefixEnd_3784124 : Nat := 4983230072969 + 3 ^ 40 * 3784124 * 2
def baseEnd_3784124 : Nat := 431794326269879518032697

theorem tailTrace_3784124 : CollatzResearch.WordTrace tailWord_3784124 prefixEnd_3784124 431794326269879518032697 := by
  unfold tailWord_3784124
  simp only [CollatzResearch.WordTrace]
  refine ⟨69009170471386249885787713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92012227295181666514383617 69009170471386249885787713)
  ·
    refine ⟨51756877853539687414340785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69009170471386249885787713 51756877853539687414340785)
    ·
      refine ⟨38817658390154765560755589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51756877853539687414340785 38817658390154765560755589)
      ·
        refine ⟨7278310948154018542641673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38817658390154765560755589 7278310948154018542641673)
        ·
          refine ⟨5458733211115513906981255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7278310948154018542641673 5458733211115513906981255)
          ·
            refine ⟨8188099816673270860471883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458733211115513906981255 8188099816673270860471883)
            ·
              refine ⟨12282149725009906290707825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8188099816673270860471883 12282149725009906290707825)
              ·
                refine ⟨9211612293757429718030869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12282149725009906290707825 9211612293757429718030869)
                ·
                  refine ⟨431794326269879518032697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9211612293757429718030869 431794326269879518032697)
                  ·
                    rfl

theorem cell22_3784124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_3784124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784124 prefixEnd_3784124 := by exact prefixLift 3784124
  have htrace : WordTrace (prefixWord ++ tailWord_3784124) baseStart_3784124 baseEnd_3784124 := by
    simpa [prefixWord, tailWord_3784124, baseEnd_3784124] using wordTrace_append hprefix tailTrace_3784124
  have hstable : (prefixWord ++ tailWord_3784124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784124).length < 2 ^ (prefixWord ++ tailWord_3784124).sum := by decide
  have hdescent : baseEnd_3784124 < baseStart_3784124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784173 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_3784173 : Nat := 118140960795 + 3784173 * 2 ^ 59
def prefixEnd_3784173 : Nat := 4983230072969 + 3 ^ 40 * 3784173 * 2
def baseEnd_3784173 : Nat := 1295399752511018759622941

theorem tailTrace_3784173 : CollatzResearch.WordTrace tailWord_3784173 prefixEnd_3784173 1295399752511018759622941 := by
  unfold tailWord_3784173
  simp only [CollatzResearch.WordTrace]
  refine ⟨138020128119594981140109173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92013418746396654093406115 138020128119594981140109173)
  ·
    refine ⟨12939387011212029481885235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138020128119594981140109173 12939387011212029481885235)
    ·
      refine ⟨19409080516818044222827853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12939387011212029481885235 19409080516818044222827853)
      ·
        refine ⟨7278405193806766583560445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19409080516818044222827853 7278405193806766583560445)
        ·
          refine ⟨2729401947677537468835167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7278405193806766583560445 2729401947677537468835167)
          ·
            refine ⟨4094102921516306203252751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729401947677537468835167 4094102921516306203252751)
            ·
              refine ⟨6141154382274459304879127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094102921516306203252751 6141154382274459304879127)
              ·
                refine ⟨9211731573411688957318691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141154382274459304879127 9211731573411688957318691)
                ·
                  refine ⟨13817597360117533435978037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9211731573411688957318691 13817597360117533435978037)
                  ·
                    refine ⟨1295399752511018759622941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13817597360117533435978037 1295399752511018759622941)
                    ·
                      rfl

theorem cell22_3784173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_3784173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784173 prefixEnd_3784173 := by exact prefixLift 3784173
  have htrace : WordTrace (prefixWord ++ tailWord_3784173) baseStart_3784173 baseEnd_3784173 := by
    simpa [prefixWord, tailWord_3784173, baseEnd_3784173] using wordTrace_append hprefix tailTrace_3784173
  have hstable : (prefixWord ++ tailWord_3784173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784173).length < 2 ^ (prefixWord ++ tailWord_3784173).sum := by decide
  have hdescent : baseEnd_3784173 < baseStart_3784173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784184 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_3784184 : Nat := 118140960795 + 3784184 * 2 ^ 59
def prefixEnd_3784184 : Nat := 4983230072969 + 3 ^ 40 * 3784184 * 2
def baseEnd_3784184 : Nat := 1295403518035818397597907

theorem tailTrace_3784184 : CollatzResearch.WordTrace tailWord_3784184 prefixEnd_3784184 1295403518035818397597907 := by
  unfold tailWord_3784184
  simp only [CollatzResearch.WordTrace]
  refine ⟨69010264661277565009379803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92013686215036753345839737 69010264661277565009379803)
  ·
    refine ⟨103515396991916347514069705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69010264661277565009379803 103515396991916347514069705)
    ·
      refine ⟨77636547743937260635552279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103515396991916347514069705 77636547743937260635552279)
      ·
        refine ⟨116454821615905890953328419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77636547743937260635552279 116454821615905890953328419)
        ·
          refine ⟨174682232423858836429992629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116454821615905890953328419 174682232423858836429992629)
          ·
            refine ⟨16376459289736765915311809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174682232423858836429992629 16376459289736765915311809)
            ·
              refine ⟨12282344467302574436483857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16376459289736765915311809 12282344467302574436483857)
              ·
                refine ⟨9211758350476930827362893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12282344467302574436483857 9211758350476930827362893)
                ·
                  refine ⟨3454409381428849060261085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9211758350476930827362893 3454409381428849060261085)
                  ·
                    refine ⟨1295403518035818397597907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454409381428849060261085 1295403518035818397597907)
                    ·
                      rfl

theorem cell22_3784184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_3784184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784184 prefixEnd_3784184 := by exact prefixLift 3784184
  have htrace : WordTrace (prefixWord ++ tailWord_3784184) baseStart_3784184 baseEnd_3784184 := by
    simpa [prefixWord, tailWord_3784184, baseEnd_3784184] using wordTrace_append hprefix tailTrace_3784184
  have hstable : (prefixWord ++ tailWord_3784184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784184).length < 2 ^ (prefixWord ++ tailWord_3784184).sum := by decide
  have hdescent : baseEnd_3784184 < baseStart_3784184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784242 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_3784242 : Nat := 118140960795 + 3784242 * 2 ^ 59
def prefixEnd_3784242 : Nat := 4983230072969 + 3 ^ 40 * 3784242 * 2
def baseEnd_3784242 : Nat := 431807790873708526549243

theorem tailTrace_3784242 : CollatzResearch.WordTrace tailWord_3784242 prefixEnd_3784242 431807790873708526549243 := by
  unfold tailWord_3784242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505661189086251481092745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92015096504230003949580653 34505661189086251481092745)
  ·
    refine ⟨25879245891814688610819559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34505661189086251481092745 25879245891814688610819559)
    ·
      refine ⟨38818868837722032916229339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25879245891814688610819559 38818868837722032916229339)
      ·
        refine ⟨58228303256583049374344009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38818868837722032916229339 58228303256583049374344009)
        ·
          refine ⟨43671227442437287030758007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58228303256583049374344009 43671227442437287030758007)
          ·
            refine ⟨65506841163655930546137011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43671227442437287030758007 65506841163655930546137011)
            ·
              refine ⟨98260261745483895819205517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65506841163655930546137011 98260261745483895819205517)
              ·
                refine ⟨36847598154556460932202069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98260261745483895819205517 36847598154556460932202069)
                ·
                  refine ⟨431807790873708526549243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36847598154556460932202069 431807790873708526549243)
                  ·
                    rfl

theorem cell22_3784242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_3784242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784242 prefixEnd_3784242 := by exact prefixLift 3784242
  have htrace : WordTrace (prefixWord ++ tailWord_3784242) baseStart_3784242 baseEnd_3784242 := by
    simpa [prefixWord, tailWord_3784242, baseEnd_3784242] using wordTrace_append hprefix tailTrace_3784242
  have hstable : (prefixWord ++ tailWord_3784242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784242).length < 2 ^ (prefixWord ++ tailWord_3784242).sum := by decide
  have hdescent : baseEnd_3784242 < baseStart_3784242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784261 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_3784261 : Nat := 118140960795 + 3784261 * 2 ^ 59
def prefixEnd_3784261 : Nat := 4983230072969 + 3 ^ 40 * 3784261 * 2
def baseEnd_3784261 : Nat := 1295429876709415863422671

theorem tailTrace_3784261 : CollatzResearch.WordTrace tailWord_3784261 prefixEnd_3784261 1295429876709415863422671 := by
  unfold tailWord_3784261
  simp only [CollatzResearch.WordTrace]
  refine ⟨138023337743276172169312637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92015558495517448112875091 138023337743276172169312637)
  ·
    refine ⟨51758751653728564563492239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138023337743276172169312637 51758751653728564563492239)
    ·
      refine ⟨77638127480592846845238359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51758751653728564563492239 77638127480592846845238359)
      ·
        refine ⟨116457191220889270267857539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77638127480592846845238359 116457191220889270267857539)
        ·
          refine ⟨174685786831333905401786309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116457191220889270267857539 174685786831333905401786309)
          ·
            refine ⟨32753585030875107262834933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174685786831333905401786309 32753585030875107262834933)
            ·
              refine ⟨3070648596644541305890775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32753585030875107262834933 3070648596644541305890775)
              ·
                refine ⟨4605972894966811958836163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070648596644541305890775 4605972894966811958836163)
                ·
                  refine ⟨6908959342450217938254245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4605972894966811958836163 6908959342450217938254245)
                  ·
                    refine ⟨1295429876709415863422671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6908959342450217938254245 1295429876709415863422671)
                    ·
                      rfl

theorem cell22_3784261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_3784261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784261 prefixEnd_3784261 := by exact prefixLift 3784261
  have htrace : WordTrace (prefixWord ++ tailWord_3784261) baseStart_3784261 baseEnd_3784261 := by
    simpa [prefixWord, tailWord_3784261, baseEnd_3784261] using wordTrace_append hprefix tailTrace_3784261
  have hstable : (prefixWord ++ tailWord_3784261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784261).length < 2 ^ (prefixWord ++ tailWord_3784261).sum := by decide
  have hdescent : baseEnd_3784261 < baseStart_3784261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784269 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3784269 : Nat := 118140960795 + 3784269 * 2 ^ 59
def prefixEnd_3784269 : Nat := 4983230072969 + 3 ^ 40 * 3784269 * 2
def baseEnd_3784269 : Nat := 1295432615272906509222647

theorem tailTrace_3784269 : CollatzResearch.WordTrace tailWord_3784269 prefixEnd_3784269 1295432615272906509222647 := by
  unfold tailWord_3784269
  simp only [CollatzResearch.WordTrace]
  refine ⟨138023629527247189535603861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92015753018164793023735907 138023629527247189535603861)
  ·
    refine ⟨6469857634089712009481431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138023629527247189535603861 6469857634089712009481431)
    ·
      refine ⟨9704786451134568014222147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469857634089712009481431 9704786451134568014222147)
      ·
        refine ⟨14557179676701852021333221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9704786451134568014222147 14557179676701852021333221)
        ·
          refine ⟨2729471189381597253999979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14557179676701852021333221 2729471189381597253999979)
          ·
            refine ⟨4094206784072395880999969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729471189381597253999979 4094206784072395880999969)
            ·
              refine ⟨3070655088054296910749977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4094206784072395880999969 3070655088054296910749977)
              ·
                refine ⟨2302991316040722683062483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070655088054296910749977 2302991316040722683062483)
                ·
                  refine ⟨3454486974061084024593725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302991316040722683062483 3454486974061084024593725)
                  ·
                    refine ⟨1295432615272906509222647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454486974061084024593725 1295432615272906509222647)
                    ·
                      rfl

theorem cell22_3784269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3784269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784269 prefixEnd_3784269 := by exact prefixLift 3784269
  have htrace : WordTrace (prefixWord ++ tailWord_3784269) baseStart_3784269 baseEnd_3784269 := by
    simpa [prefixWord, tailWord_3784269, baseEnd_3784269] using wordTrace_append hprefix tailTrace_3784269
  have hstable : (prefixWord ++ tailWord_3784269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784269).length < 2 ^ (prefixWord ++ tailWord_3784269).sum := by decide
  have hdescent : baseEnd_3784269 < baseStart_3784269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784276 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 4]
def baseStart_3784276 : Nat := 118140960795 + 3784276 * 2 ^ 59
def prefixEnd_3784276 : Nat := 4983230072969 + 3 ^ 40 * 3784276 * 2
def baseEnd_3784276 : Nat := 431811670505320274765875

theorem tailTrace_3784276 : CollatzResearch.WordTrace tailWord_3784276 prefixEnd_3784276 431811670505320274765875 := by
  unfold tailWord_3784276
  simp only [CollatzResearch.WordTrace]
  refine ⟨69011942419110914865554341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92015923225481219820739121 69011942419110914865554341)
  ·
    refine ⟨12939739203583296537291439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69011942419110914865554341 12939739203583296537291439)
    ·
      refine ⟨19409608805374944805937159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12939739203583296537291439 19409608805374944805937159)
      ·
        refine ⟨29114413208062417208905739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19409608805374944805937159 29114413208062417208905739)
        ·
          refine ⟨43671619812093625813358609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29114413208062417208905739 43671619812093625813358609)
          ·
            refine ⟨32753714859070219360018957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43671619812093625813358609 32753714859070219360018957)
            ·
              refine ⟨12282643072151332260007109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32753714859070219360018957 12282643072151332260007109)
              ·
                refine ⟨2302995576028374798751333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12282643072151332260007109 2302995576028374798751333)
                ·
                  refine ⟨431811670505320274765875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302995576028374798751333 431811670505320274765875)
                  ·
                    rfl

theorem cell22_3784276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_3784276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784276 prefixEnd_3784276 := by exact prefixLift 3784276
  have htrace : WordTrace (prefixWord ++ tailWord_3784276) baseStart_3784276 baseEnd_3784276 := by
    simpa [prefixWord, tailWord_3784276, baseEnd_3784276] using wordTrace_append hprefix tailTrace_3784276
  have hstable : (prefixWord ++ tailWord_3784276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784276).length < 2 ^ (prefixWord ++ tailWord_3784276).sum := by decide
  have hdescent : baseEnd_3784276 < baseStart_3784276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784291 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 2, 3]
def baseStart_3784291 : Nat := 118140960795 + 3784291 * 2 ^ 59
def prefixEnd_3784291 : Nat := 4983230072969 + 3 ^ 40 * 3784291 * 2
def baseEnd_3784291 : Nat := 1295440146322505785172579

theorem tailTrace_3784291 : CollatzResearch.WordTrace tailWord_3784291 prefixEnd_3784291 1295440146322505785172579 := by
  unfold tailWord_3784291
  simp only [CollatzResearch.WordTrace]
  refine ⟨138024431933167487292904727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92016287955444991528603151 138024431933167487292904727)
  ·
    refine ⟨207036647899751230939357091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138024431933167487292904727 207036647899751230939357091)
    ·
      refine ⟨310554971849626846409035637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207036647899751230939357091 310554971849626846409035637)
      ·
        refine ⟨29114528610902516850847091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310554971849626846409035637 29114528610902516850847091)
        ·
          refine ⟨43671792916353775276270637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29114528610902516850847091 43671792916353775276270637)
          ·
            refine ⟨16376922343632665728601489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43671792916353775276270637 16376922343632665728601489)
            ·
              refine ⟨12282691757724499296451117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16376922343632665728601489 12282691757724499296451117)
              ·
                refine ⟨4606009409146687236169169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12282691757724499296451117 4606009409146687236169169)
                ·
                  refine ⟨3454507056860015427126877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4606009409146687236169169 3454507056860015427126877)
                  ·
                    refine ⟨1295440146322505785172579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454507056860015427126877 1295440146322505785172579)
                    ·
                      rfl

theorem cell22_3784291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 3].length) (baseStart_3784291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784291 prefixEnd_3784291 := by exact prefixLift 3784291
  have htrace : WordTrace (prefixWord ++ tailWord_3784291) baseStart_3784291 baseEnd_3784291 := by
    simpa [prefixWord, tailWord_3784291, baseEnd_3784291] using wordTrace_append hprefix tailTrace_3784291
  have hstable : (prefixWord ++ tailWord_3784291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784291).length < 2 ^ (prefixWord ++ tailWord_3784291).sum := by decide
  have hdescent : baseEnd_3784291 < baseStart_3784291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784306 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_3784306 : Nat := 118140960795 + 3784306 * 2 ^ 59
def prefixEnd_3784306 : Nat := 4983230072969 + 3 ^ 40 * 3784306 * 2
def baseEnd_3784306 : Nat := 1295445281129050746047533

theorem tailTrace_3784306 : CollatzResearch.WordTrace tailWord_3784306 prefixEnd_3784306 1295445281129050746047533 := by
  unfold tailWord_3784306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506244757028286213675193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92016652685408763236467181 34506244757028286213675193)
  ·
    refine ⟨25879683567771214660256395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34506244757028286213675193 25879683567771214660256395)
    ·
      refine ⟨38819525351656821990384593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25879683567771214660256395 38819525351656821990384593)
      ·
        refine ⟨29114644013742616492788445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38819525351656821990384593 29114644013742616492788445)
        ·
          refine ⟨10917991505153481184795667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29114644013742616492788445 10917991505153481184795667)
          ·
            refine ⟨16376987257730221777193501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917991505153481184795667 16376987257730221777193501)
            ·
              refine ⟨6141370221648833166447563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16376987257730221777193501 6141370221648833166447563)
              ·
                refine ⟨9212055332473249749671345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141370221648833166447563 9212055332473249749671345)
                ·
                  refine ⟨6909041499354937312253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212055332473249749671345 6909041499354937312253509)
                  ·
                    refine ⟨1295445281129050746047533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6909041499354937312253509 1295445281129050746047533)
                    ·
                      rfl

theorem cell22_3784306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_3784306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784306 prefixEnd_3784306 := by exact prefixLift 3784306
  have htrace : WordTrace (prefixWord ++ tailWord_3784306) baseStart_3784306 baseEnd_3784306 := by
    simpa [prefixWord, tailWord_3784306, baseEnd_3784306] using wordTrace_append hprefix tailTrace_3784306
  have hstable : (prefixWord ++ tailWord_3784306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784306).length < 2 ^ (prefixWord ++ tailWord_3784306).sum := by decide
  have hdescent : baseEnd_3784306 < baseStart_3784306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784426 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_3784426 : Nat := 118140960795 + 3784426 * 2 ^ 59
def prefixEnd_3784426 : Nat := 4983230072969 + 3 ^ 40 * 3784426 * 2
def baseEnd_3784426 : Nat := 1295486359581410433047165

theorem tailTrace_3784426 : CollatzResearch.WordTrace tailWord_3784426 prefixEnd_3784426 1295486359581410433047165 := by
  unfold tailWord_3784426
  simp only [CollatzResearch.WordTrace]
  refine ⟨34507338946919601337267283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92019570525118936899379421 34507338946919601337267283)
  ·
    refine ⟨51761008420379402005900925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34507338946919601337267283 51761008420379402005900925)
    ·
      refine ⟨19410378157642275752212847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51761008420379402005900925 19410378157642275752212847)
      ·
        refine ⟨29115567236463413628319271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19410378157642275752212847 29115567236463413628319271)
        ·
          refine ⟨43673350854695120442478907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29115567236463413628319271 43673350854695120442478907)
          ·
            refine ⟨65510026282042680663718361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43673350854695120442478907 65510026282042680663718361)
            ·
              refine ⟨49132519711532010497788771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65510026282042680663718361 49132519711532010497788771)
              ·
                refine ⟨73698779567298015746683157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49132519711532010497788771 73698779567298015746683157)
                ·
                  refine ⟨3454630292217094488125773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73698779567298015746683157 3454630292217094488125773)
                  ·
                    refine ⟨1295486359581410433047165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454630292217094488125773 1295486359581410433047165)
                    ·
                      rfl

theorem cell22_3784426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_3784426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784426 prefixEnd_3784426 := by exact prefixLift 3784426
  have htrace : WordTrace (prefixWord ++ tailWord_3784426) baseStart_3784426 baseEnd_3784426 := by
    simpa [prefixWord, tailWord_3784426, baseEnd_3784426] using wordTrace_append hprefix tailTrace_3784426
  have hstable : (prefixWord ++ tailWord_3784426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784426).length < 2 ^ (prefixWord ++ tailWord_3784426).sum := by decide
  have hdescent : baseEnd_3784426 < baseStart_3784426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784494 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3784494 : Nat := 118140960795 + 3784494 * 2 ^ 59
def prefixEnd_3784494 : Nat := 4983230072969 + 3 ^ 40 * 3784494 * 2
def baseEnd_3784494 : Nat := 1295509637371080922346957

theorem tailTrace_3784494 : CollatzResearch.WordTrace tailWord_3784494 prefixEnd_3784494 1295509637371080922346957 := by
  unfold tailWord_3784494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17253979493929006620318067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92021223967621368641696357 17253979493929006620318067)
  ·
    refine ⟨25880969240893509930477101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17253979493929006620318067 25880969240893509930477101)
    ·
      refine ⟨9705363465335066223928913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25880969240893509930477101 9705363465335066223928913)
      ·
        refine ⟨7279022599001299667946685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9705363465335066223928913 7279022599001299667946685)
        ·
          refine ⟨2729633474625487375480007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7279022599001299667946685 2729633474625487375480007)
          ·
            refine ⟨4094450211938231063220011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729633474625487375480007 4094450211938231063220011)
            ·
              refine ⟨6141675317907346594830017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094450211938231063220011 6141675317907346594830017)
              ·
                refine ⟨4606256488430509946122513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6141675317907346594830017 4606256488430509946122513)
                ·
                  refine ⟨3454692366322882459591885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4606256488430509946122513 3454692366322882459591885)
                  ·
                    refine ⟨1295509637371080922346957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454692366322882459591885 1295509637371080922346957)
                    ·
                      rfl

theorem cell22_3784494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3784494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784494 prefixEnd_3784494 := by exact prefixLift 3784494
  have htrace : WordTrace (prefixWord ++ tailWord_3784494) baseStart_3784494 baseEnd_3784494 := by
    simpa [prefixWord, tailWord_3784494, baseEnd_3784494] using wordTrace_append hprefix tailTrace_3784494
  have hstable : (prefixWord ++ tailWord_3784494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784494).length < 2 ^ (prefixWord ++ tailWord_3784494).sum := by decide
  have hdescent : baseEnd_3784494 < baseStart_3784494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784576 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_3784576 : Nat := 118140960795 + 3784576 * 2 ^ 59
def prefixEnd_3784576 : Nat := 4983230072969 + 3 ^ 40 * 3784576 * 2
def baseEnd_3784576 : Nat := 1295537707646860041796705

theorem tailTrace_3784576 : CollatzResearch.WordTrace tailWord_3784576 prefixEnd_3784576 1295537707646860041796705 := by
  unfold tailWord_3784576
  simp only [CollatzResearch.WordTrace]
  refine ⟨69017413368567490483514791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92023217824756653978019721 69017413368567490483514791)
  ·
    refine ⟨103526120052851235725272187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69017413368567490483514791 103526120052851235725272187)
    ·
      refine ⟨155289180079276853587908281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103526120052851235725272187 155289180079276853587908281)
      ·
        refine ⟨116466885059457640190931211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155289180079276853587908281 116466885059457640190931211)
        ·
          refine ⟨174700327589186460286396817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116466885059457640190931211 174700327589186460286396817)
          ·
            refine ⟨131025245691889845214797613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174700327589186460286396817 131025245691889845214797613)
            ·
              refine ⟨49134467134458691955549105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131025245691889845214797613 49134467134458691955549105)
              ·
                refine ⟨36850850350844018966661829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49134467134458691955549105 36850850350844018966661829)
                ·
                  refine ⟨6909534440783253556249093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36850850350844018966661829 6909534440783253556249093)
                  ·
                    refine ⟨1295537707646860041796705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6909534440783253556249093 1295537707646860041796705)
                    ·
                      rfl

theorem cell22_3784576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_3784576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784576 prefixEnd_3784576 := by exact prefixLift 3784576
  have htrace : WordTrace (prefixWord ++ tailWord_3784576) baseStart_3784576 baseEnd_3784576 := by
    simpa [prefixWord, tailWord_3784576, baseEnd_3784576] using wordTrace_append hprefix tailTrace_3784576
  have hstable : (prefixWord ++ tailWord_3784576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784576).length < 2 ^ (prefixWord ++ tailWord_3784576).sum := by decide
  have hdescent : baseEnd_3784576 < baseStart_3784576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784623 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 3, 3]
def baseStart_3784623 : Nat := 118140960795 + 3784623 * 2 ^ 59
def prefixEnd_3784623 : Nat := 4983230072969 + 3 ^ 40 * 3784623 * 2
def baseEnd_3784623 : Nat := 1295553796707367585871561

theorem tailTrace_3784623 : CollatzResearch.WordTrace tailWord_3784623 prefixEnd_3784623 1295553796707367585871561 := by
  unfold tailWord_3784623
  simp only [CollatzResearch.WordTrace]
  refine ⟨138036540967964707993990523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92024360645309805329327015 138036540967964707993990523)
  ·
    refine ⟨207054811451947061990985785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138036540967964707993990523 207054811451947061990985785)
    ·
      refine ⟨155291108588960296493239339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207054811451947061990985785 155291108588960296493239339)
      ·
        refine ⟨232936662883440444739859009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155291108588960296493239339 232936662883440444739859009)
        ·
          refine ⟨174702497162580333554894257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232936662883440444739859009 174702497162580333554894257)
          ·
            refine ⟨131026872871935250166170693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174702497162580333554894257 131026872871935250166170693)
            ·
              refine ⟨24567538663487859406157005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131026872871935250166170693 24567538663487859406157005)
              ·
                refine ⟨9212826998807947277308877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24567538663487859406157005 9212826998807947277308877)
                ·
                  refine ⟨3454810124552980228990829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9212826998807947277308877 3454810124552980228990829)
                  ·
                    refine ⟨1295553796707367585871561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454810124552980228990829 1295553796707367585871561)
                    ·
                      rfl

theorem cell22_3784623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_3784623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784623 prefixEnd_3784623 := by exact prefixLift 3784623
  have htrace : WordTrace (prefixWord ++ tailWord_3784623) baseStart_3784623 baseEnd_3784623 := by
    simpa [prefixWord, tailWord_3784623, baseEnd_3784623] using wordTrace_append hprefix tailTrace_3784623
  have hstable : (prefixWord ++ tailWord_3784623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784623).length < 2 ^ (prefixWord ++ tailWord_3784623).sum := by decide
  have hdescent : baseEnd_3784623 < baseStart_3784623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784651 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_3784651 : Nat := 118140960795 + 3784651 * 2 ^ 59
def prefixEnd_3784651 : Nat := 4983230072969 + 3 ^ 40 * 3784651 * 2
def baseEnd_3784651 : Nat := 1295563381679584846171475

theorem tailTrace_3784651 : CollatzResearch.WordTrace tailWord_3784651 prefixEnd_3784651 1295563381679584846171475 := by
  unfold tailWord_3784651
  simp only [CollatzResearch.WordTrace]
  refine ⟨138037562211863268776009807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92025041474575512517339871 138037562211863268776009807)
  ·
    refine ⟨207056343317794903164014711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138037562211863268776009807 207056343317794903164014711)
    ·
      refine ⟨310584514976692354746022067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207056343317794903164014711 310584514976692354746022067)
      ·
        refine ⟨465876772465038532119033101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310584514976692354746022067 465876772465038532119033101)
        ·
          refine ⟨174703789674389449544637413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465876772465038532119033101 174703789674389449544637413)
          ·
            refine ⟨32756960563948021789619515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174703789674389449544637413 32756960563948021789619515)
            ·
              refine ⟨49135440845922032684429273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32756960563948021789619515 49135440845922032684429273)
              ·
                refine ⟨36851580634441524513321955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49135440845922032684429273 36851580634441524513321955)
                ·
                  refine ⟨55277370951662286769982933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36851580634441524513321955 55277370951662286769982933)
                  ·
                    refine ⟨1295563381679584846171475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55277370951662286769982933 1295563381679584846171475)
                    ·
                      rfl

theorem cell22_3784651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_3784651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784651 prefixEnd_3784651 := by exact prefixLift 3784651
  have htrace : WordTrace (prefixWord ++ tailWord_3784651) baseStart_3784651 baseEnd_3784651 := by
    simpa [prefixWord, tailWord_3784651, baseEnd_3784651] using wordTrace_append hprefix tailTrace_3784651
  have hstable : (prefixWord ++ tailWord_3784651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784651).length < 2 ^ (prefixWord ++ tailWord_3784651).sum := by decide
  have hdescent : baseEnd_3784651 < baseStart_3784651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784674 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3784674 : Nat := 118140960795 + 3784674 * 2 ^ 59
def prefixEnd_3784674 : Nat := 4983230072969 + 3 ^ 40 * 3784674 * 2
def baseEnd_3784674 : Nat := 1295571255049620452846405

theorem tailTrace_3784674 : CollatzResearch.WordTrace tailWord_3784674 prefixEnd_3784674 1295571255049620452846405 := by
  unfold tailWord_3784674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34509600272694985926024269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92025600727186629136064717 34509600272694985926024269)
  ·
    refine ⟨12941100102260619722259101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34509600272694985926024269 12941100102260619722259101)
    ·
      refine ⟨4852912538347732395847163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12941100102260619722259101 4852912538347732395847163)
      ·
        refine ⟨7279368807521598593770745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4852912538347732395847163 7279368807521598593770745)
        ·
          refine ⟨5459526605641198945328059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7279368807521598593770745 5459526605641198945328059)
          ·
            refine ⟨8189289908461798417992089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5459526605641198945328059 8189289908461798417992089)
            ·
              refine ⟨6141967431346348813494067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8189289908461798417992089 6141967431346348813494067)
              ·
                refine ⟨9212951147019523220241101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141967431346348813494067 9212951147019523220241101)
                ·
                  refine ⟨3454856680132321207590413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9212951147019523220241101 3454856680132321207590413)
                  ·
                    refine ⟨1295571255049620452846405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454856680132321207590413 1295571255049620452846405)
                    ·
                      rfl

theorem cell22_3784674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3784674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784674 prefixEnd_3784674 := by exact prefixLift 3784674
  have htrace : WordTrace (prefixWord ++ tailWord_3784674) baseStart_3784674 baseEnd_3784674 := by
    simpa [prefixWord, tailWord_3784674, baseEnd_3784674] using wordTrace_append hprefix tailTrace_3784674
  have hstable : (prefixWord ++ tailWord_3784674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784674).length < 2 ^ (prefixWord ++ tailWord_3784674).sum := by decide
  have hdescent : baseEnd_3784674 < baseStart_3784674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784700 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_3784700 : Nat := 118140960795 + 3784700 * 2 ^ 59
def prefixEnd_3784700 : Nat := 4983230072969 + 3 ^ 40 * 3784700 * 2
def baseEnd_3784700 : Nat := 1295580155380965051696325

theorem tailTrace_3784700 : CollatzResearch.WordTrace tailWord_3784700 prefixEnd_3784700 1295580155380965051696325 := by
  unfold tailWord_3784700
  simp only [CollatzResearch.WordTrace]
  refine ⟨69019674694342875072271777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92026232925790500096362369 69019674694342875072271777)
  ·
    refine ⟨51764756020757156304203833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69019674694342875072271777 51764756020757156304203833)
    ·
      refine ⟨38823567015567867228152875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51764756020757156304203833 38823567015567867228152875)
      ·
        refine ⟨58235350523351800842229313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38823567015567867228152875 58235350523351800842229313)
        ·
          refine ⟨43676512892513850631671985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58235350523351800842229313 43676512892513850631671985)
          ·
            refine ⟨32757384669385387973753989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43676512892513850631671985 32757384669385387973753989)
            ·
              refine ⟨6142009625509760245078873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32757384669385387973753989 6142009625509760245078873)
              ·
                refine ⟨4606507219132320183809155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6142009625509760245078873 4606507219132320183809155)
                ·
                  refine ⟨6909760828698480275713733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606507219132320183809155 6909760828698480275713733)
                  ·
                    refine ⟨1295580155380965051696325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6909760828698480275713733 1295580155380965051696325)
                    ·
                      rfl

theorem cell22_3784700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_3784700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784700 prefixEnd_3784700 := by exact prefixLift 3784700
  have htrace : WordTrace (prefixWord ++ tailWord_3784700) baseStart_3784700 baseEnd_3784700 := by
    simpa [prefixWord, tailWord_3784700, baseEnd_3784700] using wordTrace_append hprefix tailTrace_3784700
  have hstable : (prefixWord ++ tailWord_3784700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784700).length < 2 ^ (prefixWord ++ tailWord_3784700).sum := by decide
  have hdescent : baseEnd_3784700 < baseStart_3784700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784708 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3784708 : Nat := 118140960795 + 3784708 * 2 ^ 59
def prefixEnd_3784708 : Nat := 4983230072969 + 3 ^ 40 * 3784708 * 2
def baseEnd_3784708 : Nat := 1295582893944455697496301

theorem tailTrace_3784708 : CollatzResearch.WordTrace tailWord_3784708 prefixEnd_3784708 1295582893944455697496301 := by
  unfold tailWord_3784708
  simp only [CollatzResearch.WordTrace]
  refine ⟨69019820586328383755417389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92026427448437845007223185 69019820586328383755417389)
  ·
    refine ⟨25882432719873143908281521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69019820586328383755417389 25882432719873143908281521)
    ·
      refine ⟨19411824539904857931211141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25882432719873143908281521 19411824539904857931211141)
      ·
        refine ⟨3639717101232160862102089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19411824539904857931211141 3639717101232160862102089)
        ·
          refine ⟨2729787825924120646576567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639717101232160862102089 2729787825924120646576567)
          ·
            refine ⟨4094681738886180969864851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729787825924120646576567 4094681738886180969864851)
            ·
              refine ⟨6142022608329271454797277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094681738886180969864851 6142022608329271454797277)
              ·
                refine ⟨2303258478123476795548979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6142022608329271454797277 2303258478123476795548979)
                ·
                  refine ⟨3454887717185215193323469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303258478123476795548979 3454887717185215193323469)
                  ·
                    refine ⟨1295582893944455697496301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454887717185215193323469 1295582893944455697496301)
                    ·
                      rfl

theorem cell22_3784708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3784708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784708 prefixEnd_3784708 := by exact prefixLift 3784708
  have htrace : WordTrace (prefixWord ++ tailWord_3784708) baseStart_3784708 baseEnd_3784708 := by
    simpa [prefixWord, tailWord_3784708, baseEnd_3784708] using wordTrace_append hprefix tailTrace_3784708
  have hstable : (prefixWord ++ tailWord_3784708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784708).length < 2 ^ (prefixWord ++ tailWord_3784708).sum := by decide
  have hdescent : baseEnd_3784708 < baseStart_3784708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784730 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_3784730 : Nat := 118140960795 + 3784730 * 2 ^ 59
def prefixEnd_3784730 : Nat := 4983230072969 + 3 ^ 40 * 3784730 * 2
def baseEnd_3784730 : Nat := 1295590424994054973446233

theorem tailTrace_3784730 : CollatzResearch.WordTrace tailWord_3784730 prefixEnd_3784730 1295590424994054973446233 := by
  unfold tailWord_3784730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34510110894644266317033911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92026962385718043512090429 34510110894644266317033911)
  ·
    refine ⟨51765166341966399475550867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34510110894644266317033911 51765166341966399475550867)
    ·
      refine ⟨77647749512949599213326301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51765166341966399475550867 77647749512949599213326301)
      ·
        refine ⟨29117906067356099704997363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77647749512949599213326301 29117906067356099704997363)
        ·
          refine ⟨43676859101034149557496045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29117906067356099704997363 43676859101034149557496045)
          ·
            refine ⟨16378822162887806084061017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43676859101034149557496045 16378822162887806084061017)
            ·
              refine ⟨12284116622165854563045763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16378822162887806084061017 12284116622165854563045763)
              ·
                refine ⟨18426174933248781844568645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12284116622165854563045763 18426174933248781844568645)
                ·
                  refine ⟨3454907799984146595856621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18426174933248781844568645 3454907799984146595856621)
                  ·
                    refine ⟨1295590424994054973446233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3454907799984146595856621 1295590424994054973446233)
                    ·
                      rfl

theorem cell22_3784730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_3784730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784730 prefixEnd_3784730 := by exact prefixLift 3784730
  have htrace : WordTrace (prefixWord ++ tailWord_3784730) baseStart_3784730 baseEnd_3784730 := by
    simpa [prefixWord, tailWord_3784730, baseEnd_3784730] using wordTrace_append hprefix tailTrace_3784730
  have hstable : (prefixWord ++ tailWord_3784730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784730).length < 2 ^ (prefixWord ++ tailWord_3784730).sum := by decide
  have hdescent : baseEnd_3784730 < baseStart_3784730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784803 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_3784803 : Nat := 118140960795 + 3784803 * 2 ^ 59
def prefixEnd_3784803 : Nat := 4983230072969 + 3 ^ 40 * 3784803 * 2
def baseEnd_3784803 : Nat := 1295615414385907116371009

theorem tailTrace_3784803 : CollatzResearch.WordTrace tailWord_3784803 prefixEnd_3784803 1295615414385907116371009 := by
  unfold tailWord_3784803
  simp only [CollatzResearch.WordTrace]
  refine ⟨138043106107312598735543063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92028737404875065823695375 138043106107312598735543063)
  ·
    refine ⟨207064659160968898103314595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138043106107312598735543063 207064659160968898103314595)
    ·
      refine ⟨310596988741453347154971893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207064659160968898103314595 310596988741453347154971893)
      ·
        refine ⟨29118467694511251295778615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310596988741453347154971893 29118467694511251295778615)
        ·
          refine ⟨43677701541766876943667923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29118467694511251295778615 43677701541766876943667923)
          ·
            refine ⟨65516552312650315415501885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43677701541766876943667923 65516552312650315415501885)
            ·
              refine ⟨24568707117243868280813207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65516552312650315415501885 24568707117243868280813207)
              ·
                refine ⟨36853060675865802421219811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24568707117243868280813207 36853060675865802421219811)
                ·
                  refine ⟨55279591013798703631829717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36853060675865802421219811 55279591013798703631829717)
                  ·
                    refine ⟨1295615414385907116371009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55279591013798703631829717 1295615414385907116371009)
                    ·
                      rfl

theorem cell22_3784803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_3784803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784803 prefixEnd_3784803 := by exact prefixLift 3784803
  have htrace : WordTrace (prefixWord ++ tailWord_3784803) baseStart_3784803 baseEnd_3784803 := by
    simpa [prefixWord, tailWord_3784803, baseEnd_3784803] using wordTrace_append hprefix tailTrace_3784803
  have hstable : (prefixWord ++ tailWord_3784803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784803).length < 2 ^ (prefixWord ++ tailWord_3784803).sum := by decide
  have hdescent : baseEnd_3784803 < baseStart_3784803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3784805 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 5]
def baseStart_3784805 : Nat := 118140960795 + 3784805 * 2 ^ 59
def prefixEnd_3784805 : Nat := 4983230072969 + 3 ^ 40 * 3784805 * 2
def baseEnd_3784805 : Nat := 431872033008926592607001

theorem tailTrace_3784805 : CollatzResearch.WordTrace tailWord_3784805 prefixEnd_3784805 431872033008926592607001 := by
  unfold tailWord_3784805
  simp only [CollatzResearch.WordTrace]
  refine ⟨138043179053305353077115869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92028786035536902051410579 138043179053305353077115869)
  ·
    refine ⟨51766192144989507403918451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138043179053305353077115869 51766192144989507403918451)
    ·
      refine ⟨77649288217484261105877677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51766192144989507403918451 77649288217484261105877677)
      ·
        refine ⟨29118483081556597914704129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77649288217484261105877677 29118483081556597914704129)
        ·
          refine ⟨21838862311167448436028097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29118483081556597914704129 21838862311167448436028097)
          ·
            refine ⟨16379146733375586327021073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21838862311167448436028097 16379146733375586327021073)
            ·
              refine ⟨12284360050031689745265805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16379146733375586327021073 12284360050031689745265805)
              ·
                refine ⟨4606635018761883654474677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12284360050031689745265805 4606635018761883654474677)
                ·
                  refine ⟨431872033008926592607001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4606635018761883654474677 431872033008926592607001)
                  ·
                    rfl

theorem cell22_3784805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_3784805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3784805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3784805 prefixEnd_3784805 := by exact prefixLift 3784805
  have htrace : WordTrace (prefixWord ++ tailWord_3784805) baseStart_3784805 baseEnd_3784805 := by
    simpa [prefixWord, tailWord_3784805, baseEnd_3784805] using wordTrace_append hprefix tailTrace_3784805
  have hstable : (prefixWord ++ tailWord_3784805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3784805).length < 2 ^ (prefixWord ++ tailWord_3784805).sum := by decide
  have hdescent : baseEnd_3784805 < baseStart_3784805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3784805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785004 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_3785004 : Nat := 118140960795 + 3785004 * 2 ^ 59
def prefixEnd_3785004 : Nat := 4983230072969 + 3 ^ 40 * 3785004 * 2
def baseEnd_3785004 : Nat := 1295684220793609592095393

theorem tailTrace_3785004 : CollatzResearch.WordTrace tailWord_3785004 prefixEnd_3785004 1295684220793609592095393 := by
  unfold tailWord_3785004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69025218589792205031805033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92033624786389606709073377 69025218589792205031805033)
  ·
    refine ⟨51768913942344153773853775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69025218589792205031805033 51768913942344153773853775)
    ·
      refine ⟨77653370913516230660780663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51768913942344153773853775 77653370913516230660780663)
      ·
        refine ⟨116480056370274345991170995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77653370913516230660780663 116480056370274345991170995)
        ·
          refine ⟨174720084555411518986756493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116480056370274345991170995 174720084555411518986756493)
          ·
            refine ⟨65520031708279319620033685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174720084555411518986756493 65520031708279319620033685)
            ·
              refine ⟨3071251486325593107189079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65520031708279319620033685 3071251486325593107189079)
              ·
                refine ⟨4606877229488389660783619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071251486325593107189079 4606877229488389660783619)
                ·
                  refine ⟨6910315844232584491175429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606877229488389660783619 6910315844232584491175429)
                  ·
                    refine ⟨1295684220793609592095393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6910315844232584491175429 1295684220793609592095393)
                    ·
                      rfl

theorem cell22_3785004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_3785004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785004 prefixEnd_3785004 := by exact prefixLift 3785004
  have htrace : WordTrace (prefixWord ++ tailWord_3785004) baseStart_3785004 baseEnd_3785004 := by
    simpa [prefixWord, tailWord_3785004, baseEnd_3785004] using wordTrace_append hprefix tailTrace_3785004
  have hstable : (prefixWord ++ tailWord_3785004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785004).length < 2 ^ (prefixWord ++ tailWord_3785004).sum := by decide
  have hdescent : baseEnd_3785004 < baseStart_3785004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785173 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3785173 : Nat := 118140960795 + 3785173 * 2 ^ 59
def prefixEnd_3785173 : Nat := 4983230072969 + 3 ^ 40 * 3785173 * 2
def baseEnd_3785173 : Nat := 1295742072947349484619875

theorem tailTrace_3785173 : CollatzResearch.WordTrace tailWord_3785173 prefixEnd_3785173 1295742072947349484619875 := by
  unfold tailWord_3785173
  simp only [CollatzResearch.WordTrace]
  refine ⟨138056601115972151926512173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92037734077314767951008115 138056601115972151926512173)
  ·
    refine ⟨51771225418489556972442065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138056601115972151926512173 51771225418489556972442065)
    ·
      refine ⟨38828419063867167729331549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51771225418489556972442065 38828419063867167729331549)
      ·
        refine ⟨14560657148950187898499331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38828419063867167729331549 14560657148950187898499331)
        ·
          refine ⟨21840985723425281847748997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14560657148950187898499331 21840985723425281847748997)
          ·
            refine ⟨4095184823142240346452937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21840985723425281847748997 4095184823142240346452937)
            ·
              refine ⟨3071388617356680259839703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095184823142240346452937 3071388617356680259839703)
              ·
                refine ⟨4607082926035020389759555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071388617356680259839703 4607082926035020389759555)
                ·
                  refine ⟨6910624389052530584639333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607082926035020389759555 6910624389052530584639333)
                  ·
                    refine ⟨1295742072947349484619875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6910624389052530584639333 1295742072947349484619875)
                    ·
                      rfl

theorem cell22_3785173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3785173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785173 prefixEnd_3785173 := by exact prefixLift 3785173
  have htrace : WordTrace (prefixWord ++ tailWord_3785173) baseStart_3785173 baseEnd_3785173 := by
    simpa [prefixWord, tailWord_3785173, baseEnd_3785173] using wordTrace_append hprefix tailTrace_3785173
  have hstable : (prefixWord ++ tailWord_3785173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785173).length < 2 ^ (prefixWord ++ tailWord_3785173).sum := by decide
  have hdescent : baseEnd_3785173 < baseStart_3785173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785222 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3785222 : Nat := 118140960795 + 3785222 * 2 ^ 59
def prefixEnd_3785222 : Nat := 4983230072969 + 3 ^ 40 * 3785222 * 2
def baseEnd_3785222 : Nat := 431919615549576563381575

theorem tailTrace_3785222 : CollatzResearch.WordTrace tailWord_3785222 prefixEnd_3785222 431919615549576563381575 := by
  unfold tailWord_3785222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314324634149832290470185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92038925528529755530030613 4314324634149832290470185)
  ·
    refine ⟨3235743475612374217852639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4314324634149832290470185 3235743475612374217852639)
    ·
      refine ⟨4853615213418561326778959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235743475612374217852639 4853615213418561326778959)
      ·
        refine ⟨7280422820127841990168439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853615213418561326778959 7280422820127841990168439)
        ·
          refine ⟨10920634230191762985252659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280422820127841990168439 10920634230191762985252659)
          ·
            refine ⟨16380951345287644477878989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10920634230191762985252659 16380951345287644477878989)
            ·
              refine ⟨6142856754482866679204621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16380951345287644477878989 6142856754482866679204621)
              ·
                refine ⟨2303571282931075004701733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6142856754482866679204621 2303571282931075004701733)
                ·
                  refine ⟨431919615549576563381575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303571282931075004701733 431919615549576563381575)
                  ·
                    rfl

theorem cell22_3785222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3785222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785222 prefixEnd_3785222 := by exact prefixLift 3785222
  have htrace : WordTrace (prefixWord ++ tailWord_3785222) baseStart_3785222 baseEnd_3785222 := by
    simpa [prefixWord, tailWord_3785222, baseEnd_3785222] using wordTrace_append hprefix tailTrace_3785222
  have hstable : (prefixWord ++ tailWord_3785222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785222).length < 2 ^ (prefixWord ++ tailWord_3785222).sum := by decide
  have hdescent : baseEnd_3785222 < baseStart_3785222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785244 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_3785244 : Nat := 118140960795 + 3785244 * 2 ^ 59
def prefixEnd_3785244 : Nat := 4983230072969 + 3 ^ 40 * 3785244 * 2
def baseEnd_3785244 : Nat := 431922125899442988698219

theorem tailTrace_3785244 : CollatzResearch.WordTrace tailWord_3785244 prefixEnd_3785244 431922125899442988698219 := by
  unfold tailWord_3785244
  simp only [CollatzResearch.WordTrace]
  refine ⟨69029595349357465526173393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92039460465809954034897857 69029595349357465526173393)
  ·
    refine ⟨51772196512018099144630045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69029595349357465526173393 51772196512018099144630045)
    ·
      refine ⟨19414573692006787179236267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51772196512018099144630045 19414573692006787179236267)
      ·
        refine ⟨29121860538010180768854401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19414573692006787179236267 29121860538010180768854401)
        ·
          refine ⟨21841395403507635576640801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29121860538010180768854401 21841395403507635576640801)
          ·
            refine ⟨16381046552630726682480601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21841395403507635576640801 16381046552630726682480601)
            ·
              refine ⟨12285784914473045011860451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16381046552630726682480601 12285784914473045011860451)
              ·
                refine ⟨18428677371709567517790677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12285784914473045011860451 18428677371709567517790677)
                ·
                  refine ⟨431922125899442988698219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18428677371709567517790677 431922125899442988698219)
                  ·
                    rfl

theorem cell22_3785244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_3785244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785244 prefixEnd_3785244 := by exact prefixLift 3785244
  have htrace : WordTrace (prefixWord ++ tailWord_3785244) baseStart_3785244 baseEnd_3785244 := by
    simpa [prefixWord, tailWord_3785244, baseEnd_3785244] using wordTrace_append hprefix tailTrace_3785244
  have hstable : (prefixWord ++ tailWord_3785244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785244).length < 2 ^ (prefixWord ++ tailWord_3785244).sum := by decide
  have hdescent : baseEnd_3785244 < baseStart_3785244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785319 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3785319 : Nat := 118140960795 + 3785319 * 2 ^ 59
def prefixEnd_3785319 : Nat := 4983230072969 + 3 ^ 40 * 3785319 * 2
def baseEnd_3785319 : Nat := 1295792051731053770469427

theorem tailTrace_3785319 : CollatzResearch.WordTrace tailWord_3785319 prefixEnd_3785319 1295792051731053770469427 := by
  unfold tailWord_3785319
  simp only [CollatzResearch.WordTrace]
  refine ⟨138061926173443218861327011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92041284115628812574218007 138061926173443218861327011)
  ·
    refine ⟨207092889260164828291990517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138061926173443218861327011 207092889260164828291990517)
    ·
      refine ⟨19414958368140452652374111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207092889260164828291990517 19414958368140452652374111)
      ·
        refine ⟨29122437552210678978561167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19414958368140452652374111 29122437552210678978561167)
        ·
          refine ⟨43683656328316018467841751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29122437552210678978561167 43683656328316018467841751)
          ·
            refine ⟨65525484492474027701762627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43683656328316018467841751 65525484492474027701762627)
            ·
              refine ⟨98288226738711041552643941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65525484492474027701762627 98288226738711041552643941)
              ·
                refine ⟨18429042513508320291120739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98288226738711041552643941 18429042513508320291120739)
                ·
                  refine ⟨27643563770262480436681109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18429042513508320291120739 27643563770262480436681109)
                  ·
                    refine ⟨1295792051731053770469427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27643563770262480436681109 1295792051731053770469427)
                    ·
                      rfl

theorem cell22_3785319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3785319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785319 prefixEnd_3785319 := by exact prefixLift 3785319
  have htrace : WordTrace (prefixWord ++ tailWord_3785319) baseStart_3785319 baseEnd_3785319 := by
    simpa [prefixWord, tailWord_3785319, baseEnd_3785319] using wordTrace_append hprefix tailTrace_3785319
  have hstable : (prefixWord ++ tailWord_3785319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785319).length < 2 ^ (prefixWord ++ tailWord_3785319).sum := by decide
  have hdescent : baseEnd_3785319 < baseStart_3785319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785443 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 3, 4]
def baseStart_3785443 : Nat := 118140960795 + 3785443 * 2 ^ 59
def prefixEnd_3785443 : Nat := 4983230072969 + 3 ^ 40 * 3785443 * 2
def baseEnd_3785443 : Nat := 1295834499465158780369047

theorem tailTrace_3785443 : CollatzResearch.WordTrace tailWord_3785443 prefixEnd_3785443 1295834499465158780369047 := by
  unfold tailWord_3785443
  simp only [CollatzResearch.WordTrace]
  refine ⟨138066448824993988038840983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92044299216662658692560655 138066448824993988038840983)
  ·
    refine ⟨207099673237490982058261475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138066448824993988038840983 207099673237490982058261475)
    ·
      refine ⟨310649509856236473087392213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207099673237490982058261475 310649509856236473087392213)
      ·
        refine ⟨7280847887255542337985755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 310649509856236473087392213 7280847887255542337985755)
        ·
          refine ⟨10921271830883313506978633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280847887255542337985755 10921271830883313506978633)
          ·
            refine ⟨8190953873162485130233975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10921271830883313506978633 8190953873162485130233975)
            ·
              refine ⟨12286430809743727695350963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190953873162485130233975 12286430809743727695350963)
              ·
                refine ⟨18429646214615591543026445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286430809743727695350963 18429646214615591543026445)
                ·
                  refine ⟨6911117330480846828634917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18429646214615591543026445 6911117330480846828634917)
                  ·
                    refine ⟨1295834499465158780369047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6911117330480846828634917 1295834499465158780369047)
                    ·
                      rfl

theorem cell22_3785443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_3785443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785443 prefixEnd_3785443 := by exact prefixLift 3785443
  have htrace : WordTrace (prefixWord ++ tailWord_3785443) baseStart_3785443 baseEnd_3785443 := by
    simpa [prefixWord, tailWord_3785443, baseEnd_3785443] using wordTrace_append hprefix tailTrace_3785443
  have hstable : (prefixWord ++ tailWord_3785443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785443).length < 2 ^ (prefixWord ++ tailWord_3785443).sum := by decide
  have hdescent : baseEnd_3785443 < baseStart_3785443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785456 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_3785456 : Nat := 118140960795 + 3785456 * 2 ^ 59
def prefixEnd_3785456 : Nat := 4983230072969 + 3 ^ 40 * 3785456 * 2
def baseEnd_3785456 : Nat := 1295838949630831079794007

theorem tailTrace_3785456 : CollatzResearch.WordTrace tailWord_3785456 prefixEnd_3785456 1295838949630831079794007 := by
  unfold tailWord_3785456
  simp only [CollatzResearch.WordTrace]
  refine ⟨69033461486973445629532111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92044615315964594172709481 69033461486973445629532111)
  ·
    refine ⟨103550192230460168444298167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69033461486973445629532111 103550192230460168444298167)
    ·
      refine ⟨155325288345690252666447251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103550192230460168444298167 155325288345690252666447251)
      ·
        refine ⟨232987932518535378999670877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155325288345690252666447251 232987932518535378999670877)
        ·
          refine ⟨87370474694450767124876579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232987932518535378999670877 87370474694450767124876579)
          ·
            refine ⟨131055712041676150687314869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87370474694450767124876579 131055712041676150687314869)
            ·
              refine ⟨12286473003907139126935769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131055712041676150687314869 12286473003907139126935769)
              ·
                refine ⟨9214854752930354345201827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12286473003907139126935769 9214854752930354345201827)
                ·
                  refine ⟨13822282129395531517802741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9214854752930354345201827 13822282129395531517802741)
                  ·
                    refine ⟨1295838949630831079794007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13822282129395531517802741 1295838949630831079794007)
                    ·
                      rfl

theorem cell22_3785456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_3785456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785456 prefixEnd_3785456 := by exact prefixLift 3785456
  have htrace : WordTrace (prefixWord ++ tailWord_3785456) baseStart_3785456 baseEnd_3785456 := by
    simpa [prefixWord, tailWord_3785456, baseEnd_3785456] using wordTrace_append hprefix tailTrace_3785456
  have hstable : (prefixWord ++ tailWord_3785456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785456).length < 2 ^ (prefixWord ++ tailWord_3785456).sum := by decide
  have hdescent : baseEnd_3785456 < baseStart_3785456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785503 : List Nat := [1, 1, 2, 4, 2, 3, 3, 6]
def baseStart_3785503 : Nat := 118140960795 + 3785503 * 2 ^ 59
def prefixEnd_3785503 : Nat := 4983230072969 + 3 ^ 40 * 3785503 * 2
def baseEnd_3785503 : Nat := 143983893187926513763207

theorem tailTrace_3785503 : CollatzResearch.WordTrace tailWord_3785503 prefixEnd_3785503 143983893187926513763207 := by
  unfold tailWord_3785503
  simp only [CollatzResearch.WordTrace]
  refine ⟨138068637204776618286025163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92045758136517745524016775 138068637204776618286025163)
  ·
    refine ⟨207102955807164927429037745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138068637204776618286025163 207102955807164927429037745)
    ·
      refine ⟨155327216855373695571778309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207102955807164927429037745 155327216855373695571778309)
      ·
        refine ⟨29123853160382567919708433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155327216855373695571778309 29123853160382567919708433)
        ·
          refine ⟨21842889870286925939781325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29123853160382567919708433 21842889870286925939781325)
          ·
            refine ⟨8191083701357597227417997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21842889870286925939781325 8191083701357597227417997)
            ·
              refine ⟨3071656388009098960281749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8191083701357597227417997 3071656388009098960281749)
              ·
                refine ⟨143983893187926513763207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3071656388009098960281749 143983893187926513763207)
                ·
                  rfl

theorem cell22_3785503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 6].length) (baseStart_3785503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785503 prefixEnd_3785503 := by exact prefixLift 3785503
  have htrace : WordTrace (prefixWord ++ tailWord_3785503) baseStart_3785503 baseEnd_3785503 := by
    simpa [prefixWord, tailWord_3785503, baseEnd_3785503] using wordTrace_append hprefix tailTrace_3785503
  have hstable : (prefixWord ++ tailWord_3785503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785503).length < 2 ^ (prefixWord ++ tailWord_3785503).sum := by decide
  have hdescent : baseEnd_3785503 < baseStart_3785503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785524 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3785524 : Nat := 118140960795 + 3785524 * 2 ^ 59
def prefixEnd_3785524 : Nat := 4983230072969 + 3 ^ 40 * 3785524 * 2
def baseEnd_3785524 : Nat := 1295862227420501569093799

theorem tailTrace_3785524 : CollatzResearch.WordTrace tailWord_3785524 prefixEnd_3785524 1295862227420501569093799 := by
  unfold tailWord_3785524
  simp only [CollatzResearch.WordTrace]
  refine ⟨69034701568850269436269813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92046268758467025915026417 69034701568850269436269813)
  ·
    refine ⟨6472003272079712759650295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69034701568850269436269813 6472003272079712759650295)
    ·
      refine ⟨9708004908119569139475443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472003272079712759650295 9708004908119569139475443)
      ·
        refine ⟨14562007362179353709213165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9708004908119569139475443 14562007362179353709213165)
        ·
          refine ⟨5460752760817257640954937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14562007362179353709213165 5460752760817257640954937)
          ·
            refine ⟨4095564570612943230716203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5460752760817257640954937 4095564570612943230716203)
            ·
              refine ⟨6143346855919414846074305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095564570612943230716203 6143346855919414846074305)
              ·
                refine ⟨4607510141939561134555729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6143346855919414846074305 4607510141939561134555729)
                ·
                  refine ⟨3455632606454670850916797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607510141939561134555729 3455632606454670850916797)
                  ·
                    refine ⟨1295862227420501569093799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3455632606454670850916797 1295862227420501569093799)
                    ·
                      rfl

theorem cell22_3785524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3785524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785524 prefixEnd_3785524 := by exact prefixLift 3785524
  have htrace : WordTrace (prefixWord ++ tailWord_3785524) baseStart_3785524 baseEnd_3785524 := by
    simpa [prefixWord, tailWord_3785524, baseEnd_3785524] using wordTrace_append hprefix tailTrace_3785524
  have hstable : (prefixWord ++ tailWord_3785524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785524).length < 2 ^ (prefixWord ++ tailWord_3785524).sum := by decide
  have hdescent : baseEnd_3785524 < baseStart_3785524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785535 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 3, 3]
def baseStart_3785535 : Nat := 118140960795 + 3785535 * 2 ^ 59
def prefixEnd_3785535 : Nat := 4983230072969 + 3 ^ 40 * 3785535 * 2
def baseEnd_3785535 : Nat := 1295865992945301207068765

theorem tailTrace_3785535 : CollatzResearch.WordTrace tailWord_3785535 prefixEnd_3785535 1295865992945301207068765 := by
  unfold tailWord_3785535
  simp only [CollatzResearch.WordTrace]
  refine ⟨138069804340660687751190059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92046536227107125167460039 138069804340660687751190059)
  ·
    refine ⟨207104706510991031626785089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138069804340660687751190059 207104706510991031626785089)
    ·
      refine ⟨155328529883243273720088817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207104706510991031626785089 155328529883243273720088817)
      ·
        refine ⟨116496397412432455290066613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155328529883243273720088817 116496397412432455290066613)
        ·
          refine ⟨10921537257415542683443745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116496397412432455290066613 10921537257415542683443745)
          ·
            refine ⟨8191152943061657012582809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10921537257415542683443745 8191152943061657012582809)
            ·
              refine ⟨6143364707296242759437107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8191152943061657012582809 6143364707296242759437107)
              ·
                refine ⟨9215047060944364139155661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143364707296242759437107 9215047060944364139155661)
                ·
                  refine ⟨3455642647854136552183373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9215047060944364139155661 3455642647854136552183373)
                  ·
                    refine ⟨1295865992945301207068765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3455642647854136552183373 1295865992945301207068765)
                    ·
                      rfl

theorem cell22_3785535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_3785535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785535 prefixEnd_3785535 := by exact prefixLift 3785535
  have htrace : WordTrace (prefixWord ++ tailWord_3785535) baseStart_3785535 baseEnd_3785535 := by
    simpa [prefixWord, tailWord_3785535, baseEnd_3785535] using wordTrace_append hprefix tailTrace_3785535
  have hstable : (prefixWord ++ tailWord_3785535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785535).length < 2 ^ (prefixWord ++ tailWord_3785535).sum := by decide
  have hdescent : baseEnd_3785535 < baseStart_3785535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785546 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3785546 : Nat := 118140960795 + 3785546 * 2 ^ 59
def prefixEnd_3785546 : Nat := 4983230072969 + 3 ^ 40 * 3785546 * 2
def baseEnd_3785546 : Nat := 1295869758470100845043731

theorem tailTrace_3785546 : CollatzResearch.WordTrace tailWord_3785546 prefixEnd_3785546 1295869758470100845043731 := by
  unfold tailWord_3785546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34517551385905209157460123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92046803695747224419893661 34517551385905209157460123)
  ·
    refine ⟨51776327078857813736190185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34517551385905209157460123 51776327078857813736190185)
    ·
      refine ⟨38832245309143360302142639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51776327078857813736190185 38832245309143360302142639)
      ·
        refine ⟨58248367963715040453213959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38832245309143360302142639 58248367963715040453213959)
        ·
          refine ⟨87372551945572560679820939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58248367963715040453213959 87372551945572560679820939)
          ·
            refine ⟨131058827918358841019731409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87372551945572560679820939 131058827918358841019731409)
            ·
              refine ⟨98294120938769130764798557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131058827918358841019731409 98294120938769130764798557)
              ·
                refine ⟨36860295352038424036799459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98294120938769130764798557 36860295352038424036799459)
                ·
                  refine ⟨55290443028057636055199189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36860295352038424036799459 55290443028057636055199189)
                  ·
                    refine ⟨1295869758470100845043731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55290443028057636055199189 1295869758470100845043731)
                    ·
                      rfl

theorem cell22_3785546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3785546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785546 prefixEnd_3785546 := by exact prefixLift 3785546
  have htrace : WordTrace (prefixWord ++ tailWord_3785546) baseStart_3785546 baseEnd_3785546 := by
    simpa [prefixWord, tailWord_3785546, baseEnd_3785546] using wordTrace_append hprefix tailTrace_3785546
  have hstable : (prefixWord ++ tailWord_3785546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785546).length < 2 ^ (prefixWord ++ tailWord_3785546).sum := by decide
  have hdescent : baseEnd_3785546 < baseStart_3785546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785593 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 6]
def baseStart_3785593 : Nat := 118140960795 + 3785593 * 2 ^ 59
def prefixEnd_3785593 : Nat := 4983230072969 + 3 ^ 40 * 3785593 * 2
def baseEnd_3785593 : Nat := 431961949176869463039529

theorem tailTrace_3785593 : CollatzResearch.WordTrace tailWord_3785593 prefixEnd_3785593 431961949176869463039529 := by
  unfold tailWord_3785593
  simp only [CollatzResearch.WordTrace]
  refine ⟨138071919774450563656801433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92047946516300375771200955 138071919774450563656801433)
  ·
    refine ⟨103553939830837922742601075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138071919774450563656801433 103553939830837922742601075)
    ·
      refine ⟨155330909746256884113901613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103553939830837922742601075 155330909746256884113901613)
      ·
        refine ⟨58249091154846331542713105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155330909746256884113901613 58249091154846331542713105)
        ·
          refine ⟨43686818366134748657034829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58249091154846331542713105 43686818366134748657034829)
          ·
            refine ⟨16382556887300530746388061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43686818366134748657034829 16382556887300530746388061)
            ·
              refine ⟨6143458832737699029895523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16382556887300530746388061 6143458832737699029895523)
              ·
                refine ⟨9215188249106548544843285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143458832737699029895523 9215188249106548544843285)
                ·
                  refine ⟨431961949176869463039529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9215188249106548544843285 431961949176869463039529)
                  ·
                    rfl

theorem cell22_3785593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_3785593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785593 prefixEnd_3785593 := by exact prefixLift 3785593
  have htrace : WordTrace (prefixWord ++ tailWord_3785593) baseStart_3785593 baseEnd_3785593 := by
    simpa [prefixWord, tailWord_3785593, baseEnd_3785593] using wordTrace_append hprefix tailTrace_3785593
  have hstable : (prefixWord ++ tailWord_3785593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785593).length < 2 ^ (prefixWord ++ tailWord_3785593).sum := by decide
  have hdescent : baseEnd_3785593 < baseStart_3785593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785762 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_3785762 : Nat := 118140960795 + 3785762 * 2 ^ 59
def prefixEnd_3785762 : Nat := 4983230072969 + 3 ^ 40 * 3785762 * 2
def baseEnd_3785762 : Nat := 431981233228116093881023

theorem tailTrace_3785762 : CollatzResearch.WordTrace tailWord_3785762 prefixEnd_3785762 431981233228116093881023 := by
  unfold tailWord_3785762
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519520927709576379925885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92052055807225537013135693 34519520927709576379925885)
  ·
    refine ⟨12944820347891091142472207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34519520927709576379925885 12944820347891091142472207)
    ·
      refine ⟨19417230521836636713708311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944820347891091142472207 19417230521836636713708311)
      ·
        refine ⟨29125845782754955070562467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19417230521836636713708311 29125845782754955070562467)
        ·
          refine ⟨43688768674132432605843701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29125845782754955070562467 43688768674132432605843701)
          ·
            refine ⟨4095822063199915556797847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43688768674132432605843701 4095822063199915556797847)
            ·
              refine ⟨6143733094799873335196771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095822063199915556797847 6143733094799873335196771)
              ·
                refine ⟨9215599642199810002795157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143733094799873335196771 9215599642199810002795157)
                ·
                  refine ⟨431981233228116093881023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9215599642199810002795157 431981233228116093881023)
                  ·
                    rfl

theorem cell22_3785762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_3785762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785762 prefixEnd_3785762 := by exact prefixLift 3785762
  have htrace : WordTrace (prefixWord ++ tailWord_3785762) baseStart_3785762 baseEnd_3785762 := by
    simpa [prefixWord, tailWord_3785762, baseEnd_3785762] using wordTrace_append hprefix tailTrace_3785762
  have hstable : (prefixWord ++ tailWord_3785762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785762).length < 2 ^ (prefixWord ++ tailWord_3785762).sum := by decide
  have hdescent : baseEnd_3785762 < baseStart_3785762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785777 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 2, 3]
def baseStart_3785777 : Nat := 118140960795 + 3785777 * 2 ^ 59
def prefixEnd_3785777 : Nat := 4983230072969 + 3 ^ 40 * 3785777 * 2
def baseEnd_3785777 : Nat := 1295948834490893242518023

theorem tailTrace_3785777 : CollatzResearch.WordTrace tailWord_3785777 prefixEnd_3785777 1295948834490893242518023 := by
  unfold tailWord_3785777
  simp only [CollatzResearch.WordTrace]
  refine ⟨138078630805783963081499585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92052420537189308720999723 138078630805783963081499585)
  ·
    refine ⟨103558973104337972311124689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138078630805783963081499585 103558973104337972311124689)
    ·
      refine ⟨77669229828253479233343517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103558973104337972311124689 77669229828253479233343517)
      ·
        refine ⟨29125961185595054712503819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77669229828253479233343517 29125961185595054712503819)
        ·
          refine ⟨43688941778392582068755729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29125961185595054712503819 43688941778392582068755729)
          ·
            refine ⟨32766706333794436551566797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43688941778392582068755729 32766706333794436551566797)
            ·
              refine ⟨12287514875172913706837549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32766706333794436551566797 12287514875172913706837549)
              ·
                refine ⟨4607818078189842640064081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12287514875172913706837549 4607818078189842640064081)
                ·
                  refine ⟨3455863558642381980048061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607818078189842640064081 3455863558642381980048061)
                  ·
                    refine ⟨1295948834490893242518023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3455863558642381980048061 1295948834490893242518023)
                    ·
                      rfl

theorem cell22_3785777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_3785777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785777 prefixEnd_3785777 := by exact prefixLift 3785777
  have htrace : WordTrace (prefixWord ++ tailWord_3785777) baseStart_3785777 baseEnd_3785777 := by
    simpa [prefixWord, tailWord_3785777, baseEnd_3785777] using wordTrace_append hprefix tailTrace_3785777
  have hstable : (prefixWord ++ tailWord_3785777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785777).length < 2 ^ (prefixWord ++ tailWord_3785777).sum := by decide
  have hdescent : baseEnd_3785777 < baseStart_3785777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785803 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_3785803 : Nat := 118140960795 + 3785803 * 2 ^ 59
def prefixEnd_3785803 : Nat := 4983230072969 + 3 ^ 40 * 3785803 * 2
def baseEnd_3785803 : Nat := 1295957734822237841367943

theorem tailTrace_3785803 : CollatzResearch.WordTrace tailWord_3785803 prefixEnd_3785803 1295957734822237841367943 := by
  unfold tailWord_3785803
  simp only [CollatzResearch.WordTrace]
  refine ⟨138079579103689769521946063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92053052735793179681297375 138079579103689769521946063)
  ·
    refine ⟨207119368655534654282919095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138079579103689769521946063 207119368655534654282919095)
    ·
      refine ⟨310679052983301981424378643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207119368655534654282919095 310679052983301981424378643)
      ·
        refine ⟨466018579474952972136567965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310679052983301981424378643 466018579474952972136567965)
        ·
          refine ⟨174756967303107364551212987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466018579474952972136567965 174756967303107364551212987)
          ·
            refine ⟨262135450954661046826819481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174756967303107364551212987 262135450954661046826819481)
            ·
              refine ⟨196601588215995785120114611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262135450954661046826819481 196601588215995785120114611)
              ·
                refine ⟨294902382323993677680171917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196601588215995785120114611 294902382323993677680171917)
                ·
                  refine ⟨110588393371497629130064469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294902382323993677680171917 110588393371497629130064469)
                  ·
                    refine ⟨1295957734822237841367943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110588393371497629130064469 1295957734822237841367943)
                    ·
                      rfl

theorem cell22_3785803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_3785803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785803 prefixEnd_3785803 := by exact prefixLift 3785803
  have htrace : WordTrace (prefixWord ++ tailWord_3785803) baseStart_3785803 baseEnd_3785803 := by
    simpa [prefixWord, tailWord_3785803, baseEnd_3785803] using wordTrace_append hprefix tailTrace_3785803
  have hstable : (prefixWord ++ tailWord_3785803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785803).length < 2 ^ (prefixWord ++ tailWord_3785803).sum := by decide
  have hdescent : baseEnd_3785803 < baseStart_3785803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785820 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3785820 : Nat := 118140960795 + 3785820 * 2 ^ 59
def prefixEnd_3785820 : Nat := 4983230072969 + 3 ^ 40 * 3785820 * 2
def baseEnd_3785820 : Nat := 1295963554269655463692891

theorem tailTrace_3785820 : CollatzResearch.WordTrace tailWord_3785820 prefixEnd_3785820 1295963554269655463692891 := by
  unfold tailWord_3785820
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040099572314090712657457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92053466096418787616876609 69040099572314090712657457)
  ·
    refine ⟨51780074679235568034493093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69040099572314090712657457 51780074679235568034493093)
    ·
      refine ⟨9708764002356669006467455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51780074679235568034493093 9708764002356669006467455)
      ·
        refine ⟨14563146003535003509701183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9708764002356669006467455 14563146003535003509701183)
        ·
          refine ⟨21844719005302505264551775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14563146003535003509701183 21844719005302505264551775)
          ·
            refine ⟨32767078507953757896827663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21844719005302505264551775 32767078507953757896827663)
            ·
              refine ⟨49150617761930636845241495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32767078507953757896827663 49150617761930636845241495)
              ·
                refine ⟨73725926642895955267862243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49150617761930636845241495 73725926642895955267862243)
                ·
                  refine ⟨110588889964343932901793365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73725926642895955267862243 110588889964343932901793365)
                  ·
                    refine ⟨1295963554269655463692891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110588889964343932901793365 1295963554269655463692891)
                    ·
                      rfl

theorem cell22_3785820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3785820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785820 prefixEnd_3785820 := by exact prefixLift 3785820
  have htrace : WordTrace (prefixWord ++ tailWord_3785820) baseStart_3785820 baseEnd_3785820 := by
    simpa [prefixWord, tailWord_3785820, baseEnd_3785820] using wordTrace_append hprefix tailTrace_3785820
  have hstable : (prefixWord ++ tailWord_3785820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785820).length < 2 ^ (prefixWord ++ tailWord_3785820).sum := by decide
  have hdescent : baseEnd_3785820 < baseStart_3785820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785886 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3785886 : Nat := 118140960795 + 3785886 * 2 ^ 59
def prefixEnd_3785886 : Nat := 4983230072969 + 3 ^ 40 * 3785886 * 2
def baseEnd_3785886 : Nat := 431995382472817763847563

theorem tailTrace_3785886 : CollatzResearch.WordTrace tailWord_3785886 prefixEnd_3785886 431995382472817763847563 := by
  unfold tailWord_3785886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17260325795298634337152189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92055070908259383131478341 17260325795298634337152189)
  ·
    refine ⟨6472622173236987876432071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17260325795298634337152189 6472622173236987876432071)
    ·
      refine ⟨9708933259855481814648107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472622173236987876432071 9708933259855481814648107)
      ·
        refine ⟨14563399889783222721972161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9708933259855481814648107 14563399889783222721972161)
        ·
          refine ⟨10922549917337417041479121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14563399889783222721972161 10922549917337417041479121)
          ·
            refine ⟨8191912438003062781109341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10922549917337417041479121 8191912438003062781109341)
            ·
              refine ⟨3071967164251148542916003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8191912438003062781109341 3071967164251148542916003)
              ·
                refine ⟨4607950746376722814374005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071967164251148542916003 4607950746376722814374005)
                ·
                  refine ⟨431995382472817763847563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4607950746376722814374005 431995382472817763847563)
                  ·
                    rfl

theorem cell22_3785886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3785886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785886 prefixEnd_3785886 := by exact prefixLift 3785886
  have htrace : WordTrace (prefixWord ++ tailWord_3785886) baseStart_3785886 baseEnd_3785886 := by
    simpa [prefixWord, tailWord_3785886, baseEnd_3785886] using wordTrace_append hprefix tailTrace_3785886
  have hstable : (prefixWord ++ tailWord_3785886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785886).length < 2 ^ (prefixWord ++ tailWord_3785886).sum := by decide
  have hdescent : baseEnd_3785886 < baseStart_3785886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3785987 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 5]
def baseStart_3785987 : Nat := 118140960795 + 3785987 * 2 ^ 59
def prefixEnd_3785987 : Nat := 4983230072969 + 3 ^ 40 * 3785987 * 2
def baseEnd_3785987 : Nat := 432006907260840898255793

theorem tailTrace_3785987 : CollatzResearch.WordTrace tailWord_3785987 prefixEnd_3785987 432006907260840898255793 := by
  unfold tailWord_3785987
  simp only [CollatzResearch.WordTrace]
  refine ⟨138086290135023168946644215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92057526756682112631096143 138086290135023168946644215)
  ·
    refine ⟨207129435202534753419966323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138086290135023168946644215 207129435202534753419966323)
    ·
      refine ⟨310694152803802130129949485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207129435202534753419966323 310694152803802130129949485)
      ·
        refine ⟨116510307301425798798731057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310694152803802130129949485 116510307301425798798731057)
        ·
          refine ⟨87382730476069349099048293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116510307301425798798731057 87382730476069349099048293)
          ·
            refine ⟨16384261964263002956071555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87382730476069349099048293 16384261964263002956071555)
            ·
              refine ⟨24576392946394504434107333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16384261964263002956071555 24576392946394504434107333)
              ·
                refine ⟨4608073677448969581395125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24576392946394504434107333 4608073677448969581395125)
                ·
                  refine ⟨432006907260840898255793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4608073677448969581395125 432006907260840898255793)
                  ·
                    rfl

theorem cell22_3785987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 5].length) (baseStart_3785987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3785987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3785987 prefixEnd_3785987 := by exact prefixLift 3785987
  have htrace : WordTrace (prefixWord ++ tailWord_3785987) baseStart_3785987 baseEnd_3785987 := by
    simpa [prefixWord, tailWord_3785987, baseEnd_3785987] using wordTrace_append hprefix tailTrace_3785987
  have hstable : (prefixWord ++ tailWord_3785987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3785987).length < 2 ^ (prefixWord ++ tailWord_3785987).sum := by decide
  have hdescent : baseEnd_3785987 < baseStart_3785987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3785987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786049 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 6]
def baseStart_3786049 : Nat := 118140960795 + 3786049 * 2 ^ 59
def prefixEnd_3786049 : Nat := 4983230072969 + 3 ^ 40 * 3786049 * 2
def baseEnd_3786049 : Nat := 432013981883191733239063

theorem tailTrace_3786049 : CollatzResearch.WordTrace tailWord_3786049 prefixEnd_3786049 432013981883191733239063 := by
  unfold tailWord_3786049
  simp only [CollatzResearch.WordTrace]
  refine ⟨138088551460798553535401201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92059034307199035690267467 138088551460798553535401201)
  ·
    refine ⟨103566413595598915151550901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138088551460798553535401201 103566413595598915151550901)
    ·
      refine ⟨9709351274587398295457897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103566413595598915151550901 9709351274587398295457897)
      ·
        refine ⟨7282013455940548721593423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9709351274587398295457897 7282013455940548721593423)
        ·
          refine ⟨10923020183910823082390135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282013455940548721593423 10923020183910823082390135)
          ·
            refine ⟨16384530275866234623585203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923020183910823082390135 16384530275866234623585203)
            ·
              refine ⟨24576795413799351935377805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16384530275866234623585203 24576795413799351935377805)
              ·
                refine ⟨9216298280174756975766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24576795413799351935377805 9216298280174756975766677)
                ·
                  refine ⟨432013981883191733239063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9216298280174756975766677 432013981883191733239063)
                  ·
                    rfl

theorem cell22_3786049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_3786049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786049 prefixEnd_3786049 := by exact prefixLift 3786049
  have htrace : WordTrace (prefixWord ++ tailWord_3786049) baseStart_3786049 baseEnd_3786049 := by
    simpa [prefixWord, tailWord_3786049, baseEnd_3786049] using wordTrace_append hprefix tailTrace_3786049
  have hstable : (prefixWord ++ tailWord_3786049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786049).length < 2 ^ (prefixWord ++ tailWord_3786049).sum := by decide
  have hdescent : baseEnd_3786049 < baseStart_3786049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786062 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3786062 : Nat := 118140960795 + 3786062 * 2 ^ 59
def prefixEnd_3786062 : Nat := 4983230072969 + 3 ^ 40 * 3786062 * 2
def baseEnd_3786062 : Nat := 1296046395815247499142149

theorem tailTrace_3786062 : CollatzResearch.WordTrace tailWord_3786062 prefixEnd_3786062 1296046395815247499142149 := by
  unfold tailWord_3786062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17261128201218932094453055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92059350406500971170416293 17261128201218932094453055)
  ·
    refine ⟨25891692301828398141679583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17261128201218932094453055 25891692301828398141679583)
    ·
      refine ⟨38837538452742597212519375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25891692301828398141679583 38837538452742597212519375)
      ·
        refine ⟨58256307679113895818779063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38837538452742597212519375 58256307679113895818779063)
        ·
          refine ⟨87384461518670843728168595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58256307679113895818779063 87384461518670843728168595)
          ·
            refine ⟨131076692278006265592252893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87384461518670843728168595 131076692278006265592252893)
            ·
              refine ⟨49153759604252349597094835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131076692278006265592252893 49153759604252349597094835)
              ·
                refine ⟨73730639406378524395642253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49153759604252349597094835 73730639406378524395642253)
                ·
                  refine ⟨27648989777391946648365845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73730639406378524395642253 27648989777391946648365845)
                  ·
                    refine ⟨1296046395815247499142149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27648989777391946648365845 1296046395815247499142149)
                    ·
                      rfl

theorem cell22_3786062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3786062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786062 prefixEnd_3786062 := by exact prefixLift 3786062
  have htrace : WordTrace (prefixWord ++ tailWord_3786062) baseStart_3786062 baseEnd_3786062 := by
    simpa [prefixWord, tailWord_3786062, baseEnd_3786062] using wordTrace_append hprefix tailTrace_3786062
  have hstable : (prefixWord ++ tailWord_3786062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786062).length < 2 ^ (prefixWord ++ tailWord_3786062).sum := by decide
  have hdescent : baseEnd_3786062 < baseStart_3786062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786107 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_3786107 : Nat := 118140960795 + 3786107 * 2 ^ 59
def prefixEnd_3786107 : Nat := 4983230072969 + 3 ^ 40 * 3786107 * 2
def baseEnd_3786107 : Nat := 1296061800234882381767011

theorem tailTrace_3786107 : CollatzResearch.WordTrace tailWord_3786107 prefixEnd_3786107 1296061800234882381767011 := by
  unfold tailWord_3786107
  simp only [CollatzResearch.WordTrace]
  refine ⟨138090666894588429441012575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92060444596392286294008383 138090666894588429441012575)
  ·
    refine ⟨207136000341882644161518863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138090666894588429441012575 207136000341882644161518863)
    ·
      refine ⟨310704000512823966242278295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207136000341882644161518863 310704000512823966242278295)
      ·
        refine ⟨466056000769235949363417443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310704000512823966242278295 466056000769235949363417443)
        ·
          refine ⟨699084001153853924045126165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466056000769235949363417443 699084001153853924045126165)
          ·
            refine ⟨32769562554086902689615289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 699084001153853924045126165 32769562554086902689615289)
            ·
              refine ⟨24577171915565177017211467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32769562554086902689615289 24577171915565177017211467)
              ·
                refine ⟨36865757873347765525817201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24577171915565177017211467 36865757873347765525817201)
                ·
                  refine ⟨27649318405010824144362901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36865757873347765525817201 27649318405010824144362901)
                  ·
                    refine ⟨1296061800234882381767011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27649318405010824144362901 1296061800234882381767011)
                    ·
                      rfl

theorem cell22_3786107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_3786107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786107 prefixEnd_3786107 := by exact prefixLift 3786107
  have htrace : WordTrace (prefixWord ++ tailWord_3786107) baseStart_3786107 baseEnd_3786107 := by
    simpa [prefixWord, tailWord_3786107, baseEnd_3786107] using wordTrace_append hprefix tailTrace_3786107
  have hstable : (prefixWord ++ tailWord_3786107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786107).length < 2 ^ (prefixWord ++ tailWord_3786107).sum := by decide
  have hdescent : baseEnd_3786107 < baseStart_3786107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786184 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_3786184 : Nat := 118140960795 + 3786184 * 2 ^ 59
def prefixEnd_3786184 : Nat := 4983230072969 + 3 ^ 40 * 3786184 * 2
def baseEnd_3786184 : Nat := 432029386302826615863925

theorem tailTrace_3786184 : CollatzResearch.WordTrace tailWord_3786184 prefixEnd_3786184 432029386302826615863925 := by
  unfold tailWord_3786184
  simp only [CollatzResearch.WordTrace]
  refine ⟨69046737657654735795782803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92062316876872981061043737 69046737657654735795782803)
  ·
    refine ⟨103570106486482103693674205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69046737657654735795782803 103570106486482103693674205)
    ·
      refine ⟨38838789932430788885127827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103570106486482103693674205 38838789932430788885127827)
      ·
        refine ⟨58258184898646183327691741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38838789932430788885127827 58258184898646183327691741)
        ·
          refine ⟨21846819336992318747884403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58258184898646183327691741 21846819336992318747884403)
          ·
            refine ⟨32770229005488478121826605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21846819336992318747884403 32770229005488478121826605)
            ·
              refine ⟨12288835877058179295684977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32770229005488478121826605 12288835877058179295684977)
              ·
                refine ⟨9216626907793634471763733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12288835877058179295684977 9216626907793634471763733)
                ·
                  refine ⟨432029386302826615863925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9216626907793634471763733 432029386302826615863925)
                  ·
                    rfl

theorem cell22_3786184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_3786184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786184 prefixEnd_3786184 := by exact prefixLift 3786184
  have htrace : WordTrace (prefixWord ++ tailWord_3786184) baseStart_3786184 baseEnd_3786184 := by
    simpa [prefixWord, tailWord_3786184, baseEnd_3786184] using wordTrace_append hprefix tailTrace_3786184
  have hstable : (prefixWord ++ tailWord_3786184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786184).length < 2 ^ (prefixWord ++ tailWord_3786184).sum := by decide
  have hdescent : baseEnd_3786184 < baseStart_3786184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786201 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 4]
def baseStart_3786201 : Nat := 118140960795 + 3786201 * 2 ^ 59
def prefixEnd_3786201 : Nat := 4983230072969 + 3 ^ 40 * 3786201 * 2
def baseEnd_3786201 : Nat := 432031326118632489972241

theorem tailTrace_3786201 : CollatzResearch.WordTrace tailWord_3786201 prefixEnd_3786201 432031326118632489972241 := by
  unfold tailWord_3786201
  simp only [CollatzResearch.WordTrace]
  refine ⟨138094095356247883494934457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92062730237498588996622971 138094095356247883494934457)
  ·
    refine ⟨103570571517185912621200843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138094095356247883494934457 103570571517185912621200843)
    ·
      refine ⟨155355857275778868931801265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103570571517185912621200843 155355857275778868931801265)
      ·
        refine ⟨116516892956834151698850949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155355857275778868931801265 116516892956834151698850949)
        ·
          refine ⟨21846917429406403443534553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116516892956834151698850949 21846917429406403443534553)
          ·
            refine ⟨16385188072054802582650915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21846917429406403443534553 16385188072054802582650915)
            ·
              refine ⟨24577782108082203873976373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16385188072054802582650915 24577782108082203873976373)
              ·
                refine ⟨2304167072632706613185285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24577782108082203873976373 2304167072632706613185285)
                ·
                  refine ⟨432031326118632489972241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304167072632706613185285 432031326118632489972241)
                  ·
                    rfl

theorem cell22_3786201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_3786201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786201 prefixEnd_3786201 := by exact prefixLift 3786201
  have htrace : WordTrace (prefixWord ++ tailWord_3786201) baseStart_3786201 baseEnd_3786201 := by
    simpa [prefixWord, tailWord_3786201, baseEnd_3786201] using wordTrace_append hprefix tailTrace_3786201
  have hstable : (prefixWord ++ tailWord_3786201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786201).length < 2 ^ (prefixWord ++ tailWord_3786201).sum := by decide
  have hdescent : baseEnd_3786201 < baseStart_3786201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786216 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_3786216 : Nat := 118140960795 + 3786216 * 2 ^ 59
def prefixEnd_3786216 : Nat := 4983230072969 + 3 ^ 40 * 3786216 * 2
def baseEnd_3786216 : Nat := 1296099113162442430791677

theorem tailTrace_3786216 : CollatzResearch.WordTrace tailWord_3786216 prefixEnd_3786216 1296099113162442430791677 := by
  unfold tailWord_3786216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69047321225596770528365251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92063094967462360704487001 69047321225596770528365251)
  ·
    refine ⟨103570981838395155792547877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69047321225596770528365251 103570981838395155792547877)
    ·
      refine ⟨19419559094699091711102727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103570981838395155792547877 19419559094699091711102727)
      ·
        refine ⟨29129338642048637566654091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19419559094699091711102727 29129338642048637566654091)
        ·
          refine ⟨43694007963072956349981137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29129338642048637566654091 43694007963072956349981137)
          ·
            refine ⟨32770505972304717262485853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43694007963072956349981137 32770505972304717262485853)
            ·
              refine ⟨12288939739614268973432195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32770505972304717262485853 12288939739614268973432195)
              ·
                refine ⟨18433409609421403460148293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12288939739614268973432195 18433409609421403460148293)
                ·
                  refine ⟨3456264301766513148777805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18433409609421403460148293 3456264301766513148777805)
                  ·
                    refine ⟨1296099113162442430791677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456264301766513148777805 1296099113162442430791677)
                    ·
                      rfl

theorem cell22_3786216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_3786216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786216 prefixEnd_3786216 := by exact prefixLift 3786216
  have htrace : WordTrace (prefixWord ++ tailWord_3786216) baseStart_3786216 baseEnd_3786216 := by
    simpa [prefixWord, tailWord_3786216, baseEnd_3786216] using wordTrace_append hprefix tailTrace_3786216
  have hstable : (prefixWord ++ tailWord_3786216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786216).length < 2 ^ (prefixWord ++ tailWord_3786216).sum := by decide
  have hdescent : baseEnd_3786216 < baseStart_3786216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786289 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3786289 : Nat := 118140960795 + 3786289 * 2 ^ 59
def prefixEnd_3786289 : Nat := 4983230072969 + 3 ^ 40 * 3786289 * 2
def baseEnd_3786289 : Nat := 1296124102554294573716453

theorem tailTrace_3786289 : CollatzResearch.WordTrace tailWord_3786289 prefixEnd_3786289 1296124102554294573716453 := by
  unfold tailWord_3786289
  simp only [CollatzResearch.WordTrace]
  refine ⟨138097304979929074524137921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92064869986619383016091947 138097304979929074524137921)
  ·
    refine ⟨103572978734946805893103441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138097304979929074524137921 103572978734946805893103441)
    ·
      refine ⟨77679734051210104419827581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103572978734946805893103441 77679734051210104419827581)
      ·
        refine ⟨29129900269203789157435343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77679734051210104419827581 29129900269203789157435343)
        ·
          refine ⟨43694850403805683736153015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29129900269203789157435343 43694850403805683736153015)
          ·
            refine ⟨65542275605708525604229523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43694850403805683736153015 65542275605708525604229523)
            ·
              refine ⟨98313413408562788406344285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65542275605708525604229523 98313413408562788406344285)
              ·
                refine ⟨36867530028211045652379107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98313413408562788406344285 36867530028211045652379107)
                ·
                  refine ⟨55301295042316568478568661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36867530028211045652379107 55301295042316568478568661)
                  ·
                    refine ⟨1296124102554294573716453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55301295042316568478568661 1296124102554294573716453)
                    ·
                      rfl

theorem cell22_3786289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3786289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786289 prefixEnd_3786289 := by exact prefixLift 3786289
  have htrace : WordTrace (prefixWord ++ tailWord_3786289) baseStart_3786289 baseEnd_3786289 := by
    simpa [prefixWord, tailWord_3786289, baseEnd_3786289] using wordTrace_append hprefix tailTrace_3786289
  have hstable : (prefixWord ++ tailWord_3786289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786289).length < 2 ^ (prefixWord ++ tailWord_3786289).sum := by decide
  have hdescent : baseEnd_3786289 < baseStart_3786289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786291 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 5]
def baseStart_3786291 : Nat := 118140960795 + 3786291 * 2 ^ 59
def prefixEnd_3786291 : Nat := 4983230072969 + 3 ^ 40 * 3786291 * 2
def baseEnd_3786291 : Nat := 432041595731722411722149

theorem tailTrace_3786291 : CollatzResearch.WordTrace tailWord_3786291 prefixEnd_3786291 432041595731722411722149 := by
  unfold tailWord_3786291
  simp only [CollatzResearch.WordTrace]
  refine ⟨138097377925921828865710727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92064918617281219243807151 138097377925921828865710727)
  ·
    refine ⟨207146066888882743298566091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138097377925921828865710727 207146066888882743298566091)
    ·
      refine ⟨310719100333324114947849137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207146066888882743298566091 310719100333324114947849137)
      ·
        refine ⟨233039325249993086210886853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310719100333324114947849137 233039325249993086210886853)
        ·
          refine ⟨43694873484373703664541285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233039325249993086210886853 43694873484373703664541285)
          ·
            refine ⟨8192788778320069437101491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43694873484373703664541285 8192788778320069437101491)
            ·
              refine ⟨12289183167480104155652237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192788778320069437101491 12289183167480104155652237)
              ·
                refine ⟨4608443687805039058369589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12289183167480104155652237 4608443687805039058369589)
                ·
                  refine ⟨432041595731722411722149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4608443687805039058369589 432041595731722411722149)
                  ·
                    rfl

theorem cell22_3786291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 5].length) (baseStart_3786291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786291 prefixEnd_3786291 := by exact prefixLift 3786291
  have htrace : WordTrace (prefixWord ++ tailWord_3786291) baseStart_3786291 baseEnd_3786291 := by
    simpa [prefixWord, tailWord_3786291, baseEnd_3786291] using wordTrace_append hprefix tailTrace_3786291
  have hstable : (prefixWord ++ tailWord_3786291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786291).length < 2 ^ (prefixWord ++ tailWord_3786291).sum := by decide
  have hdescent : baseEnd_3786291 < baseStart_3786291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786351 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 6, 3]
def baseStart_3786351 : Nat := 118140960795 + 3786351 * 2 ^ 59
def prefixEnd_3786351 : Nat := 4983230072969 + 3 ^ 40 * 3786351 * 2
def baseEnd_3786351 : Nat := 1296145326421347078666263

theorem tailTrace_3786351 : CollatzResearch.WordTrace tailWord_3786351 prefixEnd_3786351 1296145326421347078666263 := by
  unfold tailWord_3786351
  simp only [CollatzResearch.WordTrace]
  refine ⟨138099566305704459112894907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92066377537136306075263271 138099566305704459112894907)
  ·
    refine ⟨207149349458556688669342361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138099566305704459112894907 207149349458556688669342361)
    ·
      refine ⟨155362012093917516502006771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207149349458556688669342361 155362012093917516502006771)
      ·
        refine ⟨233043018140876274753010157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155362012093917516502006771 233043018140876274753010157)
        ·
          refine ⟨87391131802828603032378809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233043018140876274753010157 87391131802828603032378809)
          ·
            refine ⟨65543348852121452274284107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87391131802828603032378809 65543348852121452274284107)
            ·
              refine ⟨98315023278182178411426161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65543348852121452274284107 98315023278182178411426161)
              ·
                refine ⟨73736267458636633808569621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98315023278182178411426161 73736267458636633808569621)
                ·
                  refine ⟨3456387537123592209776701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73736267458636633808569621 3456387537123592209776701)
                  ·
                    refine ⟨1296145326421347078666263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456387537123592209776701 1296145326421347078666263)
                    ·
                      rfl

theorem cell22_3786351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_3786351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786351 prefixEnd_3786351 := by exact prefixLift 3786351
  have htrace : WordTrace (prefixWord ++ tailWord_3786351) baseStart_3786351 baseEnd_3786351 := by
    simpa [prefixWord, tailWord_3786351, baseEnd_3786351] using wordTrace_append hprefix tailTrace_3786351
  have hstable : (prefixWord ++ tailWord_3786351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786351).length < 2 ^ (prefixWord ++ tailWord_3786351).sum := by decide
  have hdescent : baseEnd_3786351 < baseStart_3786351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786372 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_3786372 : Nat := 118140960795 + 3786372 * 2 ^ 59
def prefixEnd_3786372 : Nat := 4983230072969 + 3 ^ 40 * 3786372 * 2
def baseEnd_3786372 : Nat := 1296152515150510023891199

theorem tailTrace_3786372 : CollatzResearch.WordTrace tailWord_3786372 prefixEnd_3786372 1296152515150510023891199 := by
  unfold tailWord_3786372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69050166119314189849704685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92066888159085586466272913 69050166119314189849704685)
  ·
    refine ⟨25893812294742821193639257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69050166119314189849704685 25893812294742821193639257)
    ·
      refine ⟨19420359221057115895229443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25893812294742821193639257 19420359221057115895229443)
      ·
        refine ⟨29130538831585673842844165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19420359221057115895229443 29130538831585673842844165)
        ·
          refine ⟨5461976030922313845533281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29130538831585673842844165 5461976030922313845533281)
          ·
            refine ⟨4096482023191735384149961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5461976030922313845533281 4096482023191735384149961)
            ·
              refine ⟨3072361517393801538112471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4096482023191735384149961 3072361517393801538112471)
              ·
                refine ⟨4608542276090702307168707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072361517393801538112471 4608542276090702307168707)
                ·
                  refine ⟨6912813414136053460753061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608542276090702307168707 6912813414136053460753061)
                  ·
                    refine ⟨1296152515150510023891199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6912813414136053460753061 1296152515150510023891199)
                    ·
                      rfl

theorem cell22_3786372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_3786372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786372 prefixEnd_3786372 := by exact prefixLift 3786372
  have htrace : WordTrace (prefixWord ++ tailWord_3786372) baseStart_3786372 baseEnd_3786372 := by
    simpa [prefixWord, tailWord_3786372, baseEnd_3786372] using wordTrace_append hprefix tailTrace_3786372
  have hstable : (prefixWord ++ tailWord_3786372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786372).length < 2 ^ (prefixWord ++ tailWord_3786372).sum := by decide
  have hdescent : baseEnd_3786372 < baseStart_3786372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786402 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3786402 : Nat := 118140960795 + 3786402 * 2 ^ 59
def prefixEnd_3786402 : Nat := 4983230072969 + 3 ^ 40 * 3786402 * 2
def baseEnd_3786402 : Nat := 1296162784763599945641107

theorem tailTrace_3786402 : CollatzResearch.WordTrace tailWord_3786402 prefixEnd_3786402 1296162784763599945641107 := by
  unfold tailWord_3786402
  simp only [CollatzResearch.WordTrace]
  refine ⟨34525356607129923705750365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92067617619013129882000973 34525356607129923705750365)
  ·
    refine ⟨12947008727673721389656387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34525356607129923705750365 12947008727673721389656387)
    ·
      refine ⟨19420513091510582084484581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12947008727673721389656387 19420513091510582084484581)
      ·
        refine ⟨3641346204658234140840859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19420513091510582084484581 3641346204658234140840859)
        ·
          refine ⟨5462019306987351211261289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641346204658234140840859 5462019306987351211261289)
          ·
            refine ⟨4096514480240513408445967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5462019306987351211261289 4096514480240513408445967)
            ·
              refine ⟨6144771720360770112668951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096514480240513408445967 6144771720360770112668951)
              ·
                refine ⟨9217157580541155169003427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144771720360770112668951 9217157580541155169003427)
                ·
                  refine ⟨13825736370811732753505141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9217157580541155169003427 13825736370811732753505141)
                  ·
                    refine ⟨1296162784763599945641107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13825736370811732753505141 1296162784763599945641107)
                    ·
                      rfl

theorem cell22_3786402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3786402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786402 prefixEnd_3786402 := by exact prefixLift 3786402
  have htrace : WordTrace (prefixWord ++ tailWord_3786402) baseStart_3786402 baseEnd_3786402 := by
    simpa [prefixWord, tailWord_3786402, baseEnd_3786402] using wordTrace_append hprefix tailTrace_3786402
  have hstable : (prefixWord ++ tailWord_3786402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786402).length < 2 ^ (prefixWord ++ tailWord_3786402).sum := by decide
  have hdescent : baseEnd_3786402 < baseStart_3786402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786426 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_3786426 : Nat := 118140960795 + 3786426 * 2 ^ 59
def prefixEnd_3786426 : Nat := 4983230072969 + 3 ^ 40 * 3786426 * 2
def baseEnd_3786426 : Nat := 432057000151357294347011

theorem tailTrace_3786426 : CollatzResearch.WordTrace tailWord_3786426 prefixEnd_3786426 432057000151357294347011 := by
  unfold tailWord_3786426
  simp only [CollatzResearch.WordTrace]
  refine ⟨34525575445108186730468783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92068201186955164614583421 34525575445108186730468783)
  ·
    refine ⟨51788363167662280095703175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34525575445108186730468783 51788363167662280095703175)
    ·
      refine ⟨77682544751493420143554763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51788363167662280095703175 77682544751493420143554763)
      ·
        refine ⟨116523817127240130215332145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77682544751493420143554763 116523817127240130215332145)
        ·
          refine ⟨87392862845430097661499109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116523817127240130215332145 87392862845430097661499109)
          ·
            refine ⟨16386161783518143311531083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87392862845430097661499109 16386161783518143311531083)
            ·
              refine ⟨24579242675277214967296625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386161783518143311531083 24579242675277214967296625)
              ·
                refine ⟨18434432006457911225472469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24579242675277214967296625 18434432006457911225472469)
                ·
                  refine ⟨432057000151357294347011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18434432006457911225472469 432057000151357294347011)
                  ·
                    rfl

theorem cell22_3786426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_3786426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786426 prefixEnd_3786426 := by exact prefixLift 3786426
  have htrace : WordTrace (prefixWord ++ tailWord_3786426) baseStart_3786426 baseEnd_3786426 := by
    simpa [prefixWord, tailWord_3786426, baseEnd_3786426] using wordTrace_append hprefix tailTrace_3786426
  have hstable : (prefixWord ++ tailWord_3786426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786426).length < 2 ^ (prefixWord ++ tailWord_3786426).sum := by decide
  have hdescent : baseEnd_3786426 < baseStart_3786426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786434 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3786434 : Nat := 118140960795 + 3786434 * 2 ^ 59
def prefixEnd_3786434 : Nat := 4983230072969 + 3 ^ 40 * 3786434 * 2
def baseEnd_3786434 : Nat := 1296173739017562528841009

theorem tailTrace_3786434 : CollatzResearch.WordTrace tailWord_3786434 prefixEnd_3786434 1296173739017562528841009 := by
  unfold tailWord_3786434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34525648391100941072041589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92068395709602509525444237 34525648391100941072041589)
  ·
    refine ⟨3236779536665713225503899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34525648391100941072041589 3236779536665713225503899)
    ·
      refine ⟨4855169304998569838255849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236779536665713225503899 4855169304998569838255849)
      ·
        refine ⟨3641376978748927378691887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4855169304998569838255849 3641376978748927378691887)
        ·
          refine ⟨5462065468123391068037831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641376978748927378691887 5462065468123391068037831)
          ·
            refine ⟨8193098202185086602056747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462065468123391068037831 8193098202185086602056747)
            ·
              refine ⟨12289647303277629903085121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193098202185086602056747 12289647303277629903085121)
              ·
                refine ⟨9217235477458222427313841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12289647303277629903085121 9217235477458222427313841)
                ·
                  refine ⟨6912926608093666820485381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9217235477458222427313841 6912926608093666820485381)
                  ·
                    refine ⟨1296173739017562528841009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6912926608093666820485381 1296173739017562528841009)
                    ·
                      rfl

theorem cell22_3786434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3786434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786434 prefixEnd_3786434 := by exact prefixLift 3786434
  have htrace : WordTrace (prefixWord ++ tailWord_3786434) baseStart_3786434 baseEnd_3786434 := by
    simpa [prefixWord, tailWord_3786434, baseEnd_3786434] using wordTrace_append hprefix tailTrace_3786434
  have hstable : (prefixWord ++ tailWord_3786434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786434).length < 2 ^ (prefixWord ++ tailWord_3786434).sum := by decide
  have hdescent : baseEnd_3786434 < baseStart_3786434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786501 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3786501 : Nat := 118140960795 + 3786501 * 2 ^ 59
def prefixEnd_3786501 : Nat := 4983230072969 + 3 ^ 40 * 3786501 * 2
def baseEnd_3786501 : Nat := 1296196674486796687415803

theorem tailTrace_3786501 : CollatzResearch.WordTrace tailWord_3786501 prefixEnd_3786501 1296196674486796687415803 := by
  unfold tailWord_3786501
  simp only [CollatzResearch.WordTrace]
  refine ⟨138105037255161034730855357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92070024836774023153903571 138105037255161034730855357)
  ·
    refine ⟨51789388970685388024070759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138105037255161034730855357 51789388970685388024070759)
    ·
      refine ⟨77684083456028082036106139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51789388970685388024070759 77684083456028082036106139)
      ·
        refine ⟨116526125184042123054159209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77684083456028082036106139 116526125184042123054159209)
        ·
          refine ⟨87394593888031592290619407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116526125184042123054159209 87394593888031592290619407)
          ·
            refine ⟨131091890832047388435929111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87394593888031592290619407 131091890832047388435929111)
            ·
              refine ⟨196637836248071082653893667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131091890832047388435929111 196637836248071082653893667)
              ·
                refine ⟨294956754372106623980840501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196637836248071082653893667 294956754372106623980840501)
                ·
                  refine ⟨27652195722384995998203797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294956754372106623980840501 27652195722384995998203797)
                  ·
                    refine ⟨1296196674486796687415803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27652195722384995998203797 1296196674486796687415803)
                    ·
                      rfl

theorem cell22_3786501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3786501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786501 prefixEnd_3786501 := by exact prefixLift 3786501
  have htrace : WordTrace (prefixWord ++ tailWord_3786501) baseStart_3786501 baseEnd_3786501 := by
    simpa [prefixWord, tailWord_3786501, baseEnd_3786501] using wordTrace_append hprefix tailTrace_3786501
  have hstable : (prefixWord ++ tailWord_3786501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786501).length < 2 ^ (prefixWord ++ tailWord_3786501).sum := by decide
  have hdescent : baseEnd_3786501 < baseStart_3786501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786520 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_3786520 : Nat := 118140960795 + 3786520 * 2 ^ 59
def prefixEnd_3786520 : Nat := 4983230072969 + 3 ^ 40 * 3786520 * 2
def baseEnd_3786520 : Nat := 1296203178575086971190745

theorem tailTrace_3786520 : CollatzResearch.WordTrace tailWord_3786520 prefixEnd_3786520 1296203178575086971190745 := by
  unfold tailWord_3786520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69052865121046100487898507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92070486828061467317198009 69052865121046100487898507)
  ·
    refine ⟨103579297681569150731847761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69052865121046100487898507 103579297681569150731847761)
    ·
      refine ⟨77684473261176863048885821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103579297681569150731847761 77684473261176863048885821)
      ·
        refine ⟨29131677472941323643332183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77684473261176863048885821 29131677472941323643332183)
        ·
          refine ⟨43697516209411985464998275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29131677472941323643332183 43697516209411985464998275)
          ·
            refine ⟨65546274314117978197497413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43697516209411985464998275 65546274314117978197497413)
            ·
              refine ⟨12289926433897120912030765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65546274314117978197497413 12289926433897120912030765)
              ·
                refine ⟨4608722412711420342011537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12289926433897120912030765 4608722412711420342011537)
                ·
                  refine ⟨3456541809533565256508653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4608722412711420342011537 3456541809533565256508653)
                  ·
                    refine ⟨1296203178575086971190745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456541809533565256508653 1296203178575086971190745)
                    ·
                      rfl

theorem cell22_3786520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_3786520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786520 prefixEnd_3786520 := by exact prefixLift 3786520
  have htrace : WordTrace (prefixWord ++ tailWord_3786520) baseStart_3786520 baseEnd_3786520 := by
    simpa [prefixWord, tailWord_3786520, baseEnd_3786520] using wordTrace_append hprefix tailTrace_3786520
  have hstable : (prefixWord ++ tailWord_3786520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786520).length < 2 ^ (prefixWord ++ tailWord_3786520).sum := by decide
  have hdescent : baseEnd_3786520 < baseStart_3786520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786550 : List Nat := [5, 1, 2, 2, 1, 2, 9]
def baseStart_3786550 : Nat := 118140960795 + 3786550 * 2 ^ 59
def prefixEnd_3786550 : Nat := 4983230072969 + 3 ^ 40 * 3786550 * 2
def baseEnd_3786550 : Nat := 48007905488450996034839

theorem tailTrace_3786550 : CollatzResearch.WordTrace tailWord_3786550 prefixEnd_3786550 48007905488450996034839 := by
  unfold tailWord_3786550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631676526998969756211819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92071216287989010732926069 8631676526998969756211819)
  ·
    refine ⟨12947514790498454634317729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8631676526998969756211819 12947514790498454634317729)
    ·
      refine ⟨9710636092873840975738297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12947514790498454634317729 9710636092873840975738297)
      ·
        refine ⟨7282977069655380731803723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9710636092873840975738297 7282977069655380731803723)
        ·
          refine ⟨10924465604483071097705585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282977069655380731803723 10924465604483071097705585)
          ·
            refine ⟨8193349203362303323279189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10924465604483071097705585 8193349203362303323279189)
            ·
              refine ⟨48007905488450996034839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8193349203362303323279189 48007905488450996034839)
              ·
                rfl

theorem cell22_3786550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 9].length) (baseStart_3786550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786550 prefixEnd_3786550 := by exact prefixLift 3786550
  have htrace : WordTrace (prefixWord ++ tailWord_3786550) baseStart_3786550 baseEnd_3786550 := by
    simpa [prefixWord, tailWord_3786550, baseEnd_3786550] using wordTrace_append hprefix tailTrace_3786550
  have hstable : (prefixWord ++ tailWord_3786550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786550).length < 2 ^ (prefixWord ++ tailWord_3786550).sum := by decide
  have hdescent : baseEnd_3786550 < baseStart_3786550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786565 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_3786565 : Nat := 118140960795 + 3786565 * 2 ^ 59
def prefixEnd_3786565 : Nat := 4983230072969 + 3 ^ 40 * 3786565 * 2
def baseEnd_3786565 : Nat := 1296218582994721853815607

theorem tailTrace_3786565 : CollatzResearch.WordTrace tailWord_3786565 prefixEnd_3786565 1296218582994721853815607 := by
  unfold tailWord_3786565
  simp only [CollatzResearch.WordTrace]
  refine ⟨138107371526929173661185149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92071581017952782440790099 138107371526929173661185149)
  ·
    refine ⟨51790264322598440122944431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138107371526929173661185149 51790264322598440122944431)
    ·
      refine ⟨77685396483897660184416647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51790264322598440122944431 77685396483897660184416647)
      ·
        refine ⟨116528094725846490276624971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77685396483897660184416647 116528094725846490276624971)
        ·
          refine ⟨174792142088769735414937457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116528094725846490276624971 174792142088769735414937457)
          ·
            refine ⟨131094106566577301561203093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174792142088769735414937457 131094106566577301561203093)
            ·
              refine ⟨6145036245308311010681395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131094106566577301561203093 6145036245308311010681395)
              ·
                refine ⟨9217554367962466516022093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145036245308311010681395 9217554367962466516022093)
                ·
                  refine ⟨3456582887985924943508285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9217554367962466516022093 3456582887985924943508285)
                  ·
                    refine ⟨1296218582994721853815607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456582887985924943508285 1296218582994721853815607)
                    ·
                      rfl

theorem cell22_3786565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_3786565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786565 prefixEnd_3786565 := by exact prefixLift 3786565
  have htrace : WordTrace (prefixWord ++ tailWord_3786565) baseStart_3786565 baseEnd_3786565 := by
    simpa [prefixWord, tailWord_3786565, baseEnd_3786565] using wordTrace_append hprefix tailTrace_3786565
  have hstable : (prefixWord ++ tailWord_3786565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786565).length < 2 ^ (prefixWord ++ tailWord_3786565).sum := by decide
  have hdescent : baseEnd_3786565 < baseStart_3786565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786608 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_3786608 : Nat := 118140960795 + 3786608 * 2 ^ 59
def prefixEnd_3786608 : Nat := 4983230072969 + 3 ^ 40 * 3786608 * 2
def baseEnd_3786608 : Nat := 1296233302773484074990475

theorem tailTrace_3786608 : CollatzResearch.WordTrace tailWord_3786608 prefixEnd_3786608 1296233302773484074990475 := by
  unfold tailWord_3786608
  simp only [CollatzResearch.WordTrace]
  refine ⟨69054469932886696002500239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92072626577182261336666985 69054469932886696002500239)
  ·
    refine ⟨103581704899330044003750359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69054469932886696002500239 103581704899330044003750359)
    ·
      refine ⟨155372557348995066005625539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103581704899330044003750359 155372557348995066005625539)
      ·
        refine ⟨233058836023492599008438309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155372557348995066005625539 233058836023492599008438309)
        ·
          refine ⟨43698531754404862314082183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233058836023492599008438309 43698531754404862314082183)
          ·
            refine ⟨65547797631607293471123275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43698531754404862314082183 65547797631607293471123275)
            ·
              refine ⟨98321696447410940206684913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65547797631607293471123275 98321696447410940206684913)
              ·
                refine ⟨73741272335558205155013685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98321696447410940206684913 73741272335558205155013685)
                ·
                  refine ⟨6913244281458581733282533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73741272335558205155013685 6913244281458581733282533)
                  ·
                    refine ⟨1296233302773484074990475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6913244281458581733282533 1296233302773484074990475)
                    ·
                      rfl

theorem cell22_3786608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_3786608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786608 prefixEnd_3786608 := by exact prefixLift 3786608
  have htrace : WordTrace (prefixWord ++ tailWord_3786608) baseStart_3786608 baseEnd_3786608 := by
    simpa [prefixWord, tailWord_3786608, baseEnd_3786608] using wordTrace_append hprefix tailTrace_3786608
  have hstable : (prefixWord ++ tailWord_3786608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786608).length < 2 ^ (prefixWord ++ tailWord_3786608).sum := by decide
  have hdescent : baseEnd_3786608 < baseStart_3786608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786642 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3786642 : Nat := 118140960795 + 3786642 * 2 ^ 59
def prefixEnd_3786642 : Nat := 4983230072969 + 3 ^ 40 * 3786642 * 2
def baseEnd_3786642 : Nat := 1296244941668319319640371

theorem tailTrace_3786642 : CollatzResearch.WordTrace tailWord_3786642 prefixEnd_3786642 1296244941668319319640371 := by
  unfold tailWord_3786642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34527544986912553952934545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92073453298433477207825453 34527544986912553952934545)
  ·
    refine ⟨25895658740184415464700909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34527544986912553952934545 25895658740184415464700909)
    ·
      refine ⟨9710872027569155799262841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25895658740184415464700909 9710872027569155799262841)
      ·
        refine ⟨7283154020676866849447131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9710872027569155799262841 7283154020676866849447131)
        ·
          refine ⟨10924731031015300274170697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283154020676866849447131 10924731031015300274170697)
          ·
            refine ⟨8193548273261475205628023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10924731031015300274170697 8193548273261475205628023)
            ·
              refine ⟨12290322409892212808442035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193548273261475205628023 12290322409892212808442035)
              ·
                refine ⟨18435483614838319212663053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12290322409892212808442035 18435483614838319212663053)
                ·
                  refine ⟨6913306355564369704748645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18435483614838319212663053 6913306355564369704748645)
                  ·
                    refine ⟨1296244941668319319640371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6913306355564369704748645 1296244941668319319640371)
                    ·
                      rfl

theorem cell22_3786642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3786642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786642 prefixEnd_3786642 := by exact prefixLift 3786642
  have htrace : WordTrace (prefixWord ++ tailWord_3786642) baseStart_3786642 baseEnd_3786642 := by
    simpa [prefixWord, tailWord_3786642, baseEnd_3786642] using wordTrace_append hprefix tailTrace_3786642
  have hstable : (prefixWord ++ tailWord_3786642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786642).length < 2 ^ (prefixWord ++ tailWord_3786642).sum := by decide
  have hdescent : baseEnd_3786642 < baseStart_3786642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786685 : List Nat := [1, 4, 1, 2, 3, 1, 3, 7]
def baseStart_3786685 : Nat := 118140960795 + 3786685 * 2 ^ 59
def prefixEnd_3786685 : Nat := 4983230072969 + 3 ^ 40 * 3786685 * 2
def baseEnd_3786685 : Nat := 144028851271897948979471

theorem tailTrace_3786685 : CollatzResearch.WordTrace tailWord_3786685 prefixEnd_3786685 144028851271897948979471 := by
  unfold tailWord_3786685
  simp only [CollatzResearch.WordTrace]
  refine ⟨138111748286494434155553509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92074498857662956103702339 138111748286494434155553509)
  ·
    refine ⟨25895952803717706404166283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138111748286494434155553509 25895952803717706404166283)
    ·
      refine ⟨38843929205576559606249425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25895952803717706404166283 38843929205576559606249425)
      ·
        refine ⟨29132946904182419704687069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38843929205576559606249425 29132946904182419704687069)
        ·
          refine ⟨10924855089068407389257651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29132946904182419704687069 10924855089068407389257651)
          ·
            refine ⟨16387282633602611083886477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10924855089068407389257651 16387282633602611083886477)
            ·
              refine ⟨6145230987600979156457429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16387282633602611083886477 6145230987600979156457429)
              ·
                refine ⟨144028851271897948979471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6145230987600979156457429 144028851271897948979471)
                ·
                  rfl

theorem cell22_3786685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 7].length) (baseStart_3786685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786685 prefixEnd_3786685 := by exact prefixLift 3786685
  have htrace : WordTrace (prefixWord ++ tailWord_3786685) baseStart_3786685 baseEnd_3786685 := by
    simpa [prefixWord, tailWord_3786685, baseEnd_3786685] using wordTrace_append hprefix tailTrace_3786685
  have hstable : (prefixWord ++ tailWord_3786685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786685).length < 2 ^ (prefixWord ++ tailWord_3786685).sum := by decide
  have hdescent : baseEnd_3786685 < baseStart_3786685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786730 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_3786730 : Nat := 118140960795 + 3786730 * 2 ^ 59
def prefixEnd_3786730 : Nat := 4983230072969 + 3 ^ 40 * 3786730 * 2
def baseEnd_3786730 : Nat := 432091688622238807813367

theorem tailTrace_3786730 : CollatzResearch.WordTrace tailWord_3786730 prefixEnd_3786730 432091688622238807813367 := by
  unfold tailWord_3786730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34528347392832851710235411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92075593047554271227294429 34528347392832851710235411)
  ·
    refine ⟨51792521089249277565353117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34528347392832851710235411 51792521089249277565353117)
    ·
      refine ⟨19422195408468479087007419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51792521089249277565353117 19422195408468479087007419)
      ·
        refine ⟨29133293112702718630511129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19422195408468479087007419 29133293112702718630511129)
        ·
          refine ⟨21849969834527038972883347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29133293112702718630511129 21849969834527038972883347)
          ·
            refine ⟨32774954751790558459325021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21849969834527038972883347 32774954751790558459325021)
            ·
              refine ⟨12290608031921459422246883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32774954751790558459325021 12290608031921459422246883)
              ·
                refine ⟨18435912047882189133370325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12290608031921459422246883 18435912047882189133370325)
                ·
                  refine ⟨432091688622238807813367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18435912047882189133370325 432091688622238807813367)
                  ·
                    rfl

theorem cell22_3786730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_3786730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786730 prefixEnd_3786730 := by exact prefixLift 3786730
  have htrace : WordTrace (prefixWord ++ tailWord_3786730) baseStart_3786730 baseEnd_3786730 := by
    simpa [prefixWord, tailWord_3786730, baseEnd_3786730] using wordTrace_append hprefix tailTrace_3786730
  have hstable : (prefixWord ++ tailWord_3786730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786730).length < 2 ^ (prefixWord ++ tailWord_3786730).sum := by decide
  have hdescent : baseEnd_3786730 < baseStart_3786730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786734 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_3786734 : Nat := 118140960795 + 3786734 * 2 ^ 59
def prefixEnd_3786734 : Nat := 4983230072969 + 3 ^ 40 * 3786734 * 2
def baseEnd_3786734 : Nat := 1296276435148461746340089

theorem tailTrace_3786734 : CollatzResearch.WordTrace tailWord_3786734 prefixEnd_3786734 1296276435148461746340089 := by
  unfold tailWord_3786734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264191932914614440510907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92075690308877943682724837 17264191932914614440510907)
  ·
    refine ⟨25896287899371921660766361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264191932914614440510907 25896287899371921660766361)
    ·
      refine ⟨19422215924528941245574771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25896287899371921660766361 19422215924528941245574771)
      ·
        refine ⟨29133323886793411868362157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19422215924528941245574771 29133323886793411868362157)
        ·
          refine ⟨10924996457547529450635809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29133323886793411868362157 10924996457547529450635809)
          ·
            refine ⟨8193747343160647087976857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10924996457547529450635809 8193747343160647087976857)
            ·
              refine ⟨6145310507370485315982643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8193747343160647087976857 6145310507370485315982643)
              ·
                refine ⟨9217965761055727973973965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145310507370485315982643 9217965761055727973973965)
                ·
                  refine ⟨3456737160395897990240237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9217965761055727973973965 3456737160395897990240237)
                  ·
                    refine ⟨1296276435148461746340089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456737160395897990240237 1296276435148461746340089)
                    ·
                      rfl

theorem cell22_3786734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_3786734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786734 prefixEnd_3786734 := by exact prefixLift 3786734
  have htrace : WordTrace (prefixWord ++ tailWord_3786734) baseStart_3786734 baseEnd_3786734 := by
    simpa [prefixWord, tailWord_3786734, baseEnd_3786734] using wordTrace_append hprefix tailTrace_3786734
  have hstable : (prefixWord ++ tailWord_3786734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786734).length < 2 ^ (prefixWord ++ tailWord_3786734).sum := by decide
  have hdescent : baseEnd_3786734 < baseStart_3786734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786745 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_3786745 : Nat := 118140960795 + 3786745 * 2 ^ 59
def prefixEnd_3786745 : Nat := 4983230072969 + 3 ^ 40 * 3786745 * 2
def baseEnd_3786745 : Nat := 1296280200673261384315055

theorem tailTrace_3786745 : CollatzResearch.WordTrace tailWord_3786745 prefixEnd_3786745 1296280200673261384315055 := by
  unfold tailWord_3786745
  simp only [CollatzResearch.WordTrace]
  refine ⟨138113936666277064402737689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92075957777518042935158459 138113936666277064402737689)
  ·
    refine ⟨103585452499707798302053267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138113936666277064402737689 103585452499707798302053267)
    ·
      refine ⟨155378178749561697453079901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103585452499707798302053267 155378178749561697453079901)
      ·
        refine ⟨58266817031085636544904963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155378178749561697453079901 58266817031085636544904963)
        ·
          refine ⟨87400225546628454817357445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58266817031085636544904963 87400225546628454817357445)
          ·
            refine ⟨16387542289992835278254521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87400225546628454817357445 16387542289992835278254521)
            ·
              refine ⟨12290656717494626458690891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16387542289992835278254521 12290656717494626458690891)
              ·
                refine ⟨18435985076241939688036337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12290656717494626458690891 18435985076241939688036337)
                ·
                  refine ⟨13826988807181454766027253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18435985076241939688036337 13826988807181454766027253)
                  ·
                    refine ⟨1296280200673261384315055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13826988807181454766027253 1296280200673261384315055)
                    ·
                      rfl

theorem cell22_3786745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_3786745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786745 prefixEnd_3786745 := by exact prefixLift 3786745
  have htrace : WordTrace (prefixWord ++ tailWord_3786745) baseStart_3786745 baseEnd_3786745 := by
    simpa [prefixWord, tailWord_3786745, baseEnd_3786745] using wordTrace_append hprefix tailTrace_3786745
  have hstable : (prefixWord ++ tailWord_3786745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786745).length < 2 ^ (prefixWord ++ tailWord_3786745).sum := by decide
  have hdescent : baseEnd_3786745 < baseStart_3786745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786805 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3786805 : Nat := 118140960795 + 3786805 * 2 ^ 59
def prefixEnd_3786805 : Nat := 4983230072969 + 3 ^ 40 * 3786805 * 2
def baseEnd_3786805 : Nat := 1296300739899441227814871

theorem tailTrace_3786805 : CollatzResearch.WordTrace tailWord_3786805 prefixEnd_3786805 1296300739899441227814871 := by
  unfold tailWord_3786805
  simp only [CollatzResearch.WordTrace]
  refine ⟨138116125046059694649921869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92077416697373129766614579 138116125046059694649921869)
  ·
    refine ⟨51793546892272385493720701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138116125046059694649921869 51793546892272385493720701)
    ·
      refine ⟨19422580084602144560145263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51793546892272385493720701 19422580084602144560145263)
      ·
        refine ⟨29133870126903216840217895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19422580084602144560145263 29133870126903216840217895)
        ·
          refine ⟨43700805190354825260326843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29133870126903216840217895 43700805190354825260326843)
          ·
            refine ⟨65551207785532237890490265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43700805190354825260326843 65551207785532237890490265)
            ·
              refine ⟨49163405839149178417867699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65551207785532237890490265 49163405839149178417867699)
              ·
                refine ⟨73745108758723767626801549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49163405839149178417867699 73745108758723767626801549)
                ·
                  refine ⟨27654415784521412860050581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73745108758723767626801549 27654415784521412860050581)
                  ·
                    refine ⟨1296300739899441227814871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27654415784521412860050581 1296300739899441227814871)
                    ·
                      rfl

theorem cell22_3786805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3786805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786805 prefixEnd_3786805 := by exact prefixLift 3786805
  have htrace : WordTrace (prefixWord ++ tailWord_3786805) baseStart_3786805 baseEnd_3786805 := by
    simpa [prefixWord, tailWord_3786805, baseEnd_3786805] using wordTrace_append hprefix tailTrace_3786805
  have hstable : (prefixWord ++ tailWord_3786805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786805).length < 2 ^ (prefixWord ++ tailWord_3786805).sum := by decide
  have hdescent : baseEnd_3786805 < baseStart_3786805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786880 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_3786880 : Nat := 118140960795 + 3786880 * 2 ^ 59
def prefixEnd_3786880 : Nat := 4983230072969 + 3 ^ 40 * 3786880 * 2
def baseEnd_3786880 : Nat := 1296326413932166032189641

theorem tailTrace_3786880 : CollatzResearch.WordTrace tailWord_3786880 prefixEnd_3786880 1296326413932166032189641 := by
  unfold tailWord_3786880
  simp only [CollatzResearch.WordTrace]
  refine ⟨69059430260393991229451047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92079240347191988305934729 69059430260393991229451047)
  ·
    refine ⟨103589145390590986844176571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69059430260393991229451047 103589145390590986844176571)
    ·
      refine ⟨155383718085886480266264857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103589145390590986844176571 155383718085886480266264857)
      ·
        refine ⟨116537788564414860199698643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155383718085886480266264857 116537788564414860199698643)
        ·
          refine ⟨174806682846622290299547965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116537788564414860199698643 174806682846622290299547965)
          ·
            refine ⟨65552506067483358862330487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174806682846622290299547965 65552506067483358862330487)
            ·
              refine ⟨98328759101225038293495731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65552506067483358862330487 98328759101225038293495731)
              ·
                refine ⟨147493138651837557440243597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98328759101225038293495731 147493138651837557440243597)
                ·
                  refine ⟨55309926994439084040091349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147493138651837557440243597 55309926994439084040091349)
                  ·
                    refine ⟨1296326413932166032189641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55309926994439084040091349 1296326413932166032189641)
                    ·
                      rfl

theorem cell22_3786880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_3786880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786880 prefixEnd_3786880 := by exact prefixLift 3786880
  have htrace : WordTrace (prefixWord ++ tailWord_3786880) baseStart_3786880 baseEnd_3786880 := by
    simpa [prefixWord, tailWord_3786880, baseEnd_3786880] using wordTrace_append hprefix tailTrace_3786880
  have hstable : (prefixWord ++ tailWord_3786880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786880).length < 2 ^ (prefixWord ++ tailWord_3786880).sum := by decide
  have hdescent : baseEnd_3786880 < baseStart_3786880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786914 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3786914 : Nat := 118140960795 + 3786914 * 2 ^ 59
def prefixEnd_3786914 : Nat := 4983230072969 + 3 ^ 40 * 3786914 * 2
def baseEnd_3786914 : Nat := 1296338052827001276839537

theorem tailTrace_3786914 : CollatzResearch.WordTrace tailWord_3786914 prefixEnd_3786914 1296338052827001276839537 := by
  unfold tailWord_3786914
  simp only [CollatzResearch.WordTrace]
  refine ⟨34530025150666201566409949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92080067068443204177093197 34530025150666201566409949)
  ·
    refine ⟨12948759431499825587403731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34530025150666201566409949 12948759431499825587403731)
    ·
      refine ⟨19423139147249738381105597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12948759431499825587403731 19423139147249738381105597)
      ·
        refine ⟨7283677180218651892914599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19423139147249738381105597 7283677180218651892914599)
        ·
          refine ⟨10925515770327977839371899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283677180218651892914599 10925515770327977839371899)
          ·
            refine ⟨16388273655491966759057849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10925515770327977839371899 16388273655491966759057849)
            ·
              refine ⟨12291205241618975069293387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16388273655491966759057849 12291205241618975069293387)
              ·
                refine ⟨18436807862428462603940081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291205241618975069293387 18436807862428462603940081)
                ·
                  refine ⟨13827605896821346952955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18436807862428462603940081 13827605896821346952955061)
                  ·
                    refine ⟨1296338052827001276839537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13827605896821346952955061 1296338052827001276839537)
                    ·
                      rfl

theorem cell22_3786914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3786914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786914 prefixEnd_3786914 := by exact prefixLift 3786914
  have htrace : WordTrace (prefixWord ++ tailWord_3786914) baseStart_3786914 baseEnd_3786914 := by
    simpa [prefixWord, tailWord_3786914, baseEnd_3786914] using wordTrace_append hprefix tailTrace_3786914
  have hstable : (prefixWord ++ tailWord_3786914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786914).length < 2 ^ (prefixWord ++ tailWord_3786914).sum := by decide
  have hdescent : baseEnd_3786914 < baseStart_3786914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786916 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3786916 : Nat := 118140960795 + 3786916 * 2 ^ 59
def prefixEnd_3786916 : Nat := 4983230072969 + 3 ^ 40 * 3786916 * 2
def baseEnd_3786916 : Nat := 432112912489291312763177

theorem tailTrace_3786916 : CollatzResearch.WordTrace tailWord_3786916 prefixEnd_3786916 432112912489291312763177 := by
  unfold tailWord_3786916
  simp only [CollatzResearch.WordTrace]
  refine ⟨69060086774328780303606301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92080115699105040404808401 69060086774328780303606301)
  ·
    refine ⟨25897532540373292613852363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69060086774328780303606301 25897532540373292613852363)
    ·
      refine ⟨38846298810559938920778545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25897532540373292613852363 38846298810559938920778545)
      ·
        refine ⟨29134724107919954190583909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38846298810559938920778545 29134724107919954190583909)
        ·
          refine ⟨5462760770234991410734483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29134724107919954190583909 5462760770234991410734483)
          ·
            refine ⟨8194141155352487116101725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462760770234991410734483 8194141155352487116101725)
            ·
              refine ⟨3072802933257182668538147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8194141155352487116101725 3072802933257182668538147)
              ·
                refine ⟨4609204399885774002807221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072802933257182668538147 4609204399885774002807221)
                ·
                  refine ⟨432112912489291312763177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4609204399885774002807221 432112912489291312763177)
                  ·
                    rfl

theorem cell22_3786916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3786916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786916 prefixEnd_3786916 := by exact prefixLift 3786916
  have htrace : WordTrace (prefixWord ++ tailWord_3786916) baseStart_3786916 baseEnd_3786916 := by
    simpa [prefixWord, tailWord_3786916, baseEnd_3786916] using wordTrace_append hprefix tailTrace_3786916
  have hstable : (prefixWord ++ tailWord_3786916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786916).length < 2 ^ (prefixWord ++ tailWord_3786916).sum := by decide
  have hdescent : baseEnd_3786916 < baseStart_3786916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3786959 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 2, 3]
def baseStart_3786959 : Nat := 118140960795 + 3786959 * 2 ^ 59
def prefixEnd_3786959 : Nat := 4983230072969 + 3 ^ 40 * 3786959 * 2
def baseEnd_3786959 : Nat := 1296353457246636159464399

theorem tailTrace_3786959 : CollatzResearch.WordTrace tailWord_3786959 prefixEnd_3786959 1296353457246636159464399 := by
  unfold tailWord_3786959
  simp only [CollatzResearch.WordTrace]
  refine ⟨138121741887501778951027931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92081161258334519300685287 138121741887501778951027931)
  ·
    refine ⟨207182612831252668426541897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138121741887501778951027931 207182612831252668426541897)
    ·
      refine ⟨155386959623439501319906423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207182612831252668426541897 155386959623439501319906423)
      ·
        refine ⟨233080439435159251979859635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155386959623439501319906423 233080439435159251979859635)
        ·
          refine ⟨349620659152738877969789453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233080439435159251979859635 349620659152738877969789453)
          ·
            refine ⟨131107747182277079238671045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349620659152738877969789453 131107747182277079238671045)
            ·
              refine ⟨24582702596676952357250821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131107747182277079238671045 24582702596676952357250821)
              ·
                refine ⟨4609256736876928566984529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24582702596676952357250821 4609256736876928566984529)
                ·
                  refine ⟨3456942552657696425238397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609256736876928566984529 3456942552657696425238397)
                  ·
                    refine ⟨1296353457246636159464399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456942552657696425238397 1296353457246636159464399)
                    ·
                      rfl

theorem cell22_3786959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_3786959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3786959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3786959 prefixEnd_3786959 := by exact prefixLift 3786959
  have htrace : WordTrace (prefixWord ++ tailWord_3786959) baseStart_3786959 baseEnd_3786959 := by
    simpa [prefixWord, tailWord_3786959, baseEnd_3786959] using wordTrace_append hprefix tailTrace_3786959
  have hstable : (prefixWord ++ tailWord_3786959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3786959).length < 2 ^ (prefixWord ++ tailWord_3786959).sum := by decide
  have hdescent : baseEnd_3786959 < baseStart_3786959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3786959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787038 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3787038 : Nat := 118140960795 + 3787038 * 2 ^ 59
def prefixEnd_3787038 : Nat := 4983230072969 + 3 ^ 40 * 3787038 * 2
def baseEnd_3787038 : Nat := 1296380500561106286739157

theorem tailTrace_3787038 : CollatzResearch.WordTrace tailWord_3787038 prefixEnd_3787038 1296380500561106286739157 := by
  unfold tailWord_3787038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265577906776946930394221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92083082169477050295435845 17265577906776946930394221)
  ·
    refine ⟨6474591715041355098897833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17265577906776946930394221 6474591715041355098897833)
    ·
      refine ⟨4855943786281016324173375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6474591715041355098897833 4855943786281016324173375)
      ·
        refine ⟨7283915679421524486260063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4855943786281016324173375 7283915679421524486260063)
        ·
          refine ⟨10925873519132286729390095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283915679421524486260063 10925873519132286729390095)
          ·
            refine ⟨16388810278698430094085143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10925873519132286729390095 16388810278698430094085143)
            ·
              refine ⟨24583215418047645141127715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16388810278698430094085143 24583215418047645141127715)
              ·
                refine ⟨36874823127071467711691573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24583215418047645141127715 36874823127071467711691573)
                ·
                  refine ⟨3457014668162950097971085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36874823127071467711691573 3457014668162950097971085)
                  ·
                    refine ⟨1296380500561106286739157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457014668162950097971085 1296380500561106286739157)
                    ·
                      rfl

theorem cell22_3787038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3787038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787038 prefixEnd_3787038 := by exact prefixLift 3787038
  have htrace : WordTrace (prefixWord ++ tailWord_3787038) baseStart_3787038 baseEnd_3787038 := by
    simpa [prefixWord, tailWord_3787038, baseEnd_3787038] using wordTrace_append hprefix tailTrace_3787038
  have hstable : (prefixWord ++ tailWord_3787038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787038).length < 2 ^ (prefixWord ++ tailWord_3787038).sum := by decide
  have hdescent : baseEnd_3787038 < baseStart_3787038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787077 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 9]
def baseStart_3787077 : Nat := 118140960795 + 3787077 * 2 ^ 59
def prefixEnd_3787077 : Nat := 4983230072969 + 3 ^ 40 * 3787077 * 2
def baseEnd_3787077 : Nat := 1296393851058123185014037

theorem tailTrace_3787077 : CollatzResearch.WordTrace tailWord_3787077 prefixEnd_3787077 1296393851058123185014037 := by
  unfold tailWord_3787077
  simp only [CollatzResearch.WordTrace]
  refine ⟨138126045701074285103823485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92084030467382856735882323 138126045701074285103823485)
  ·
    refine ⟨51797267137902856913933807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138126045701074285103823485 51797267137902856913933807)
    ·
      refine ⟨77695900706854285370900711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51797267137902856913933807 77695900706854285370900711)
      ·
        refine ⟨116543851060281428056351067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77695900706854285370900711 116543851060281428056351067)
        ·
          refine ⟨174815776590422142084526601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116543851060281428056351067 174815776590422142084526601)
          ·
            refine ⟨131111832442816606563394951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174815776590422142084526601 131111832442816606563394951)
            ·
              refine ⟨196667748664224909845092427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131111832442816606563394951 196667748664224909845092427)
              ·
                refine ⟨295001622996337364767638641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196667748664224909845092427 295001622996337364767638641)
                ·
                  refine ⟨221251217247253023575728981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295001622996337364767638641 221251217247253023575728981)
                  ·
                    refine ⟨1296393851058123185014037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 221251217247253023575728981 1296393851058123185014037)
                    ·
                      rfl

theorem cell22_3787077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_3787077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787077 prefixEnd_3787077 := by exact prefixLift 3787077
  have htrace : WordTrace (prefixWord ++ tailWord_3787077) baseStart_3787077 baseEnd_3787077 := by
    simpa [prefixWord, tailWord_3787077, baseEnd_3787077] using wordTrace_append hprefix tailTrace_3787077
  have hstable : (prefixWord ++ tailWord_3787077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787077).length < 2 ^ (prefixWord ++ tailWord_3787077).sum := by decide
  have hdescent : baseEnd_3787077 < baseStart_3787077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787079 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 6]
def baseStart_3787079 : Nat := 118140960795 + 3787079 * 2 ^ 59
def prefixEnd_3787079 : Nat := 4983230072969 + 3 ^ 40 * 3787079 * 2
def baseEnd_3787079 : Nat := 432131511899665282154677

theorem tailTrace_3787079 : CollatzResearch.WordTrace tailWord_3787079 prefixEnd_3787079 432131511899665282154677 := by
  unfold tailWord_3787079
  simp only [CollatzResearch.WordTrace]
  refine ⟨138126118647067039445396291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92084079098044692963597527 138126118647067039445396291)
  ·
    refine ⟨207189177970600559168094437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138126118647067039445396291 207189177970600559168094437)
    ·
      refine ⟨38847970869487604844017707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207189177970600559168094437 38847970869487604844017707)
      ·
        refine ⟨58271956304231407266026561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38847970869487604844017707 58271956304231407266026561)
        ·
          refine ⟨43703967228173555449519921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58271956304231407266026561 43703967228173555449519921)
          ·
            refine ⟨32777975421130166587139941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43703967228173555449519921 32777975421130166587139941)
            ·
              refine ⟨6145870391461906235088739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32777975421130166587139941 6145870391461906235088739)
              ·
                refine ⟨9218805587192859352633109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145870391461906235088739 9218805587192859352633109)
                ·
                  refine ⟨432131511899665282154677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9218805587192859352633109 432131511899665282154677)
                  ·
                    rfl

theorem cell22_3787079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 6].length) (baseStart_3787079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787079 prefixEnd_3787079 := by exact prefixLift 3787079
  have htrace : WordTrace (prefixWord ++ tailWord_3787079) baseStart_3787079 baseEnd_3787079 := by
    simpa [prefixWord, tailWord_3787079, baseEnd_3787079] using wordTrace_append hprefix tailTrace_3787079
  have hstable : (prefixWord ++ tailWord_3787079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787079).length < 2 ^ (prefixWord ++ tailWord_3787079).sum := by decide
  have hdescent : baseEnd_3787079 < baseStart_3787079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787109 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_3787109 : Nat := 118140960795 + 3787109 * 2 ^ 59
def prefixEnd_3787109 : Nat := 4983230072969 + 3 ^ 40 * 3787109 * 2
def baseEnd_3787109 : Nat := 1296404805312085768213939

theorem tailTrace_3787109 : CollatzResearch.WordTrace tailWord_3787109 prefixEnd_3787109 1296404805312085768213939 := by
  unfold tailWord_3787109
  simp only [CollatzResearch.WordTrace]
  refine ⟨138127212836958354568988381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92084808557972236379325587 138127212836958354568988381)
  ·
    refine ⟨51797704813859382963370643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138127212836958354568988381 51797704813859382963370643)
    ·
      refine ⟨77696557220789074445055965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51797704813859382963370643 77696557220789074445055965)
      ·
        refine ⟨29136208957795902916895987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77696557220789074445055965 29136208957795902916895987)
        ·
          refine ⟨43704313436693854375343981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29136208957795902916895987 43704313436693854375343981)
          ·
            refine ⟨16389117538760195390753993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43704313436693854375343981 16389117538760195390753993)
            ·
              refine ⟨12291838154070146543065495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16389117538760195390753993 12291838154070146543065495)
              ·
                refine ⟨18437757231105219814598243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291838154070146543065495 18437757231105219814598243)
                ·
                  refine ⟨27656635846657829721897365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18437757231105219814598243 27656635846657829721897365)
                  ·
                    refine ⟨1296404805312085768213939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27656635846657829721897365 1296404805312085768213939)
                    ·
                      rfl

theorem cell22_3787109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_3787109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787109 prefixEnd_3787109 := by exact prefixLift 3787109
  have htrace : WordTrace (prefixWord ++ tailWord_3787109) baseStart_3787109 baseEnd_3787109 := by
    simpa [prefixWord, tailWord_3787109, baseEnd_3787109] using wordTrace_append hprefix tailTrace_3787109
  have hstable : (prefixWord ++ tailWord_3787109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787109).length < 2 ^ (prefixWord ++ tailWord_3787109).sum := by decide
  have hdescent : baseEnd_3787109 < baseStart_3787109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787111 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3787111 : Nat := 118140960795 + 3787111 * 2 ^ 59
def prefixEnd_3787111 : Nat := 4983230072969 + 3 ^ 40 * 3787111 * 2
def baseEnd_3787111 : Nat := 1296405489952958429663933

theorem tailTrace_3787111 : CollatzResearch.WordTrace tailWord_3787111 prefixEnd_3787111 1296405489952958429663933 := by
  unfold tailWord_3787111
  simp only [CollatzResearch.WordTrace]
  refine ⟨138127285782951108910561187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92084857188634072607040791 138127285782951108910561187)
  ·
    refine ⟨207190928674426663365841781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138127285782951108910561187 207190928674426663365841781)
    ·
      refine ⟨19424149563227499690547667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207190928674426663365841781 19424149563227499690547667)
      ·
        refine ⟨29136224344841249535821501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19424149563227499690547667 29136224344841249535821501)
        ·
          refine ⟨10926084129315468575933063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29136224344841249535821501 10926084129315468575933063)
          ·
            refine ⟨16389126193973202863899595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10926084129315468575933063 16389126193973202863899595)
            ·
              refine ⟨24583689290959804295849393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16389126193973202863899595 24583689290959804295849393)
              ·
                refine ⟨18437766968219853221887045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24583689290959804295849393 18437766968219853221887045)
                ·
                  refine ⟨3457081306541222479103821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18437766968219853221887045 3457081306541222479103821)
                  ·
                    refine ⟨1296405489952958429663933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457081306541222479103821 1296405489952958429663933)
                    ·
                      rfl

theorem cell22_3787111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3787111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787111 prefixEnd_3787111 := by exact prefixLift 3787111
  have htrace : WordTrace (prefixWord ++ tailWord_3787111) baseStart_3787111 baseEnd_3787111 := by
    simpa [prefixWord, tailWord_3787111, baseEnd_3787111] using wordTrace_append hprefix tailTrace_3787111
  have hstable : (prefixWord ++ tailWord_3787111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787111).length < 2 ^ (prefixWord ++ tailWord_3787111).sum := by decide
  have hdescent : baseEnd_3787111 < baseStart_3787111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787145 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 2, 3]
def baseStart_3787145 : Nat := 118140960795 + 3787145 * 2 ^ 59
def prefixEnd_3787145 : Nat := 4983230072969 + 3 ^ 40 * 3787145 * 2
def baseEnd_3787145 : Nat := 1296417128847793674313829

theorem tailTrace_3787145 : CollatzResearch.WordTrace tailWord_3787145 prefixEnd_3787145 1296417128847793674313829 := by
  unfold tailWord_3787145
  simp only [CollatzResearch.WordTrace]
  refine ⟨138128525864827932717298889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92085683909885288478199259 138128525864827932717298889)
  ·
    refine ⟨103596394398620949537974167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138128525864827932717298889 103596394398620949537974167)
    ·
      refine ⟨155394591597931424306961251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103596394398620949537974167 155394591597931424306961251)
      ·
        refine ⟨233091887396897136460441877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155394591597931424306961251 233091887396897136460441877)
        ·
          refine ⟨10926182221729553271583213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233091887396897136460441877 10926182221729553271583213)
          ·
            refine ⟨4097318333148582476843705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10926182221729553271583213 4097318333148582476843705)
            ·
              refine ⟨3072988749861436857632779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4097318333148582476843705 3072988749861436857632779)
              ·
                refine ⟨4609483124792155286449169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072988749861436857632779 4609483124792155286449169)
                ·
                  refine ⟨3457112343594116464836877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609483124792155286449169 3457112343594116464836877)
                  ·
                    refine ⟨1296417128847793674313829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457112343594116464836877 1296417128847793674313829)
                    ·
                      rfl

theorem cell22_3787145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 2, 3].length) (baseStart_3787145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787145 prefixEnd_3787145 := by exact prefixLift 3787145
  have htrace : WordTrace (prefixWord ++ tailWord_3787145) baseStart_3787145 baseEnd_3787145 := by
    simpa [prefixWord, tailWord_3787145, baseEnd_3787145] using wordTrace_append hprefix tailTrace_3787145
  have hstable : (prefixWord ++ tailWord_3787145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787145).length < 2 ^ (prefixWord ++ tailWord_3787145).sum := by decide
  have hdescent : baseEnd_3787145 < baseStart_3787145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787173 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 1, 3]
def baseStart_3787173 : Nat := 118140960795 + 3787173 * 2 ^ 59
def prefixEnd_3787173 : Nat := 4983230072969 + 3 ^ 40 * 3787173 * 2
def baseEnd_3787173 : Nat := 1296426713820010934613743

theorem tailTrace_3787173 : CollatzResearch.WordTrace tailWord_3787173 prefixEnd_3787173 1296426713820010934613743 := by
  unfold tailWord_3787173
  simp only [CollatzResearch.WordTrace]
  refine ⟨138129547108726493499318173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92086364739150995666212115 138129547108726493499318173)
  ·
    refine ⟨51798580165772435062244315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138129547108726493499318173 51798580165772435062244315)
    ·
      refine ⟨77697870248658652593366473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51798580165772435062244315 77697870248658652593366473)
      ·
        refine ⟨58273402686493989445024855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77697870248658652593366473 58273402686493989445024855)
        ·
          refine ⟨87410104029740984167537283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58273402686493989445024855 87410104029740984167537283)
          ·
            refine ⟨131115156044611476251305925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87410104029740984167537283 131115156044611476251305925)
            ·
              refine ⟨24584091758364651797119861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131115156044611476251305925 24584091758364651797119861)
              ·
                refine ⟨2304758602346686105979987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24584091758364651797119861 2304758602346686105979987)
                ·
                  refine ⟨3457137903520029158969981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304758602346686105979987 3457137903520029158969981)
                  ·
                    refine ⟨1296426713820010934613743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457137903520029158969981 1296426713820010934613743)
                    ·
                      rfl

theorem cell22_3787173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_3787173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787173 prefixEnd_3787173 := by exact prefixLift 3787173
  have htrace : WordTrace (prefixWord ++ tailWord_3787173) baseStart_3787173 baseEnd_3787173 := by
    simpa [prefixWord, tailWord_3787173, baseEnd_3787173] using wordTrace_append hprefix tailTrace_3787173
  have hstable : (prefixWord ++ tailWord_3787173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787173).length < 2 ^ (prefixWord ++ tailWord_3787173).sum := by decide
  have hdescent : baseEnd_3787173 < baseStart_3787173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787186 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3787186 : Nat := 118140960795 + 3787186 * 2 ^ 59
def prefixEnd_3787186 : Nat := 4983230072969 + 3 ^ 40 * 3787186 * 2
def baseEnd_3787186 : Nat := 432143721328561078012901

theorem tailTrace_3787186 : CollatzResearch.WordTrace tailWord_3787186 prefixEnd_3787186 432143721328561078012901 := by
  unfold tailWord_3787186
  simp only [CollatzResearch.WordTrace]
  refine ⟨34532505314419849179885353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92086680838452931146360941 34532505314419849179885353)
  ·
    refine ⟨25899378985814886884914015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34532505314419849179885353 25899378985814886884914015)
    ·
      refine ⟨38849068478722330327371023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25899378985814886884914015 38849068478722330327371023)
      ·
        refine ⟨58273602718083495491056535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38849068478722330327371023 58273602718083495491056535)
        ·
          refine ⟨87410404077125243236584803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58273602718083495491056535 87410404077125243236584803)
          ·
            refine ⟨131115606115687864854877205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87410404077125243236584803 131115606115687864854877205)
            ·
              refine ⟨6146044036672868665072369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131115606115687864854877205 6146044036672868665072369)
              ·
                refine ⟨4609533027504651498804277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6146044036672868665072369 4609533027504651498804277)
                ·
                  refine ⟨432143721328561078012901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4609533027504651498804277 432143721328561078012901)
                  ·
                    rfl

theorem cell22_3787186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3787186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787186 prefixEnd_3787186 := by exact prefixLift 3787186
  have htrace : WordTrace (prefixWord ++ tailWord_3787186) baseStart_3787186 baseEnd_3787186 := by
    simpa [prefixWord, tailWord_3787186, baseEnd_3787186] using wordTrace_append hprefix tailTrace_3787186
  have hstable : (prefixWord ++ tailWord_3787186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787186).length < 2 ^ (prefixWord ++ tailWord_3787186).sum := by decide
  have hdescent : baseEnd_3787186 < baseStart_3787186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787276 : List Nat := [2, 2, 1, 2, 4, 2, 1, 8]
def baseStart_3787276 : Nat := 118140960795 + 3787276 * 2 ^ 59
def prefixEnd_3787276 : Nat := 4983230072969 + 3 ^ 40 * 3787276 * 2
def baseEnd_3787276 : Nat := 144051330313883666587603

theorem tailTrace_3787276 : CollatzResearch.WordTrace tailWord_3787276 prefixEnd_3787276 144051330313883666587603 := by
  unfold tailWord_3787276
  simp only [CollatzResearch.WordTrace]
  refine ⟨69066651913676671045158841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92088869218235561393545121 69066651913676671045158841)
  ·
    refine ⟨51799988935257503283869131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69066651913676671045158841 51799988935257503283869131)
    ·
      refine ⟨77699983402886254925803697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51799988935257503283869131 77699983402886254925803697)
      ·
        refine ⟨58274987552164691194352773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77699983402886254925803697 58274987552164691194352773)
        ·
          refine ⟨10926560166030879598941145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58274987552164691194352773 10926560166030879598941145)
          ·
            refine ⟨8194920124523159699205859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10926560166030879598941145 8194920124523159699205859)
            ·
              refine ⟨12292380186784739548808789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194920124523159699205859 12292380186784739548808789)
              ·
                refine ⟨144051330313883666587603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12292380186784739548808789 144051330313883666587603)
                ·
                  rfl

theorem cell22_3787276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 8].length) (baseStart_3787276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787276 prefixEnd_3787276 := by exact prefixLift 3787276
  have htrace : WordTrace (prefixWord ++ tailWord_3787276) baseStart_3787276 baseEnd_3787276 := by
    simpa [prefixWord, tailWord_3787276, baseEnd_3787276] using wordTrace_append hprefix tailTrace_3787276
  have hstable : (prefixWord ++ tailWord_3787276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787276).length < 2 ^ (prefixWord ++ tailWord_3787276).sum := by decide
  have hdescent : baseEnd_3787276 < baseStart_3787276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787445 : List Nat := [1, 3, 3, 3, 1, 1, 4, 6]
def baseStart_3787445 : Nat := 118140960795 + 3787445 * 2 ^ 59
def prefixEnd_3787445 : Nat := 4983230072969 + 3 ^ 40 * 3787445 * 2
def baseEnd_3787445 : Nat := 144057758330965876868101

theorem tailTrace_3787445 : CollatzResearch.WordTrace tailWord_3787445 prefixEnd_3787445 144057758330965876868101 := by
  unfold tailWord_3787445
  simp only [CollatzResearch.WordTrace]
  refine ⟨138139467763741083953219789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92092978509160722635479859 138139467763741083953219789)
  ·
    refine ⟨51802300411402906482457421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138139467763741083953219789 51802300411402906482457421)
    ·
      refine ⟨19425862654276089930921533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51802300411402906482457421 19425862654276089930921533)
      ·
        refine ⟨7284698495353533724095575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19425862654276089930921533 7284698495353533724095575)
        ·
          refine ⟨10927047743030300586143363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7284698495353533724095575 10927047743030300586143363)
          ·
            refine ⟨16390571614545450879215045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10927047743030300586143363 16390571614545450879215045)
            ·
              refine ⟨3073232177727272039852821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16390571614545450879215045 3073232177727272039852821)
              ·
                refine ⟨144057758330965876868101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3073232177727272039852821 144057758330965876868101)
                ·
                  rfl

theorem cell22_3787445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 6].length) (baseStart_3787445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787445 prefixEnd_3787445 := by exact prefixLift 3787445
  have htrace : WordTrace (prefixWord ++ tailWord_3787445) baseStart_3787445 baseEnd_3787445 := by
    simpa [prefixWord, tailWord_3787445, baseEnd_3787445] using wordTrace_append hprefix tailTrace_3787445
  have hstable : (prefixWord ++ tailWord_3787445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787445).length < 2 ^ (prefixWord ++ tailWord_3787445).sum := by decide
  have hdescent : baseEnd_3787445 < baseStart_3787445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787473 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 5]
def baseStart_3787473 : Nat := 118140960795 + 3787473 * 2 ^ 59
def prefixEnd_3787473 : Nat := 4983230072969 + 3 ^ 40 * 3787473 * 2
def baseEnd_3787473 : Nat := 432176469983636717370941

theorem tailTrace_3787473 : CollatzResearch.WordTrace tailWord_3787473 prefixEnd_3787473 432176469983636717370941 := by
  unfold tailWord_3787473
  simp only [CollatzResearch.WordTrace]
  refine ⟨138140489007639644735239073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92093659338426429823492715 138140489007639644735239073)
  ·
    refine ⟨103605366755729733551429305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138140489007639644735239073 103605366755729733551429305)
    ·
      refine ⟨77704025066797300163571979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103605366755729733551429305 77704025066797300163571979)
      ·
        refine ⟨116556037600195950245357969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77704025066797300163571979 116556037600195950245357969)
        ·
          refine ⟨87417028200146962684018477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116556037600195950245357969 87417028200146962684018477)
          ·
            refine ⟨32781385575055111006506929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87417028200146962684018477 32781385575055111006506929)
            ·
              refine ⟨24586039181291333254880197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32781385575055111006506929 24586039181291333254880197)
              ·
                refine ⟨4609882346492124985290037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24586039181291333254880197 4609882346492124985290037)
                ·
                  refine ⟨432176469983636717370941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4609882346492124985290037 432176469983636717370941)
                  ·
                    rfl

theorem cell22_3787473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 5].length) (baseStart_3787473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787473 prefixEnd_3787473 := by exact prefixLift 3787473
  have htrace : WordTrace (prefixWord ++ tailWord_3787473) baseStart_3787473 baseEnd_3787473 := by
    simpa [prefixWord, tailWord_3787473, baseEnd_3787473] using wordTrace_append hprefix tailTrace_3787473
  have hstable : (prefixWord ++ tailWord_3787473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787473).length < 2 ^ (prefixWord ++ tailWord_3787473).sum := by decide
  have hdescent : baseEnd_3787473 < baseStart_3787473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787535 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 4]
def baseStart_3787535 : Nat := 118140960795 + 3787535 * 2 ^ 59
def prefixEnd_3787535 : Nat := 4983230072969 + 3 ^ 40 * 3787535 * 2
def baseEnd_3787535 : Nat := 432183544605987552354211

theorem tailTrace_3787535 : CollatzResearch.WordTrace tailWord_3787535 prefixEnd_3787535 432183544605987552354211 := by
  unfold tailWord_3787535
  simp only [CollatzResearch.WordTrace]
  refine ⟨138142750333415029323996059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92095166888943352882664039 138142750333415029323996059)
  ·
    refine ⟨207214125500122543985994089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138142750333415029323996059 207214125500122543985994089)
    ·
      refine ⟨155410594125091907989495567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207214125500122543985994089 155410594125091907989495567)
      ·
        refine ⟨233115891187637861984243351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155410594125091907989495567 233115891187637861984243351)
        ·
          refine ⟨349673836781456792976365027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233115891187637861984243351 349673836781456792976365027)
          ·
            refine ⟨524510755172185189464547541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349673836781456792976365027 524510755172185189464547541)
            ·
              refine ⟨12293220824348090378075333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 524510755172185189464547541 12293220824348090378075333)
              ·
                refine ⟨2304978904565266945889125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12293220824348090378075333 2304978904565266945889125)
                ·
                  refine ⟨432183544605987552354211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304978904565266945889125 432183544605987552354211)
                  ·
                    rfl

theorem cell22_3787535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 4].length) (baseStart_3787535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787535 prefixEnd_3787535 := by exact prefixLift 3787535
  have htrace : WordTrace (prefixWord ++ tailWord_3787535) baseStart_3787535 baseEnd_3787535 := by
    simpa [prefixWord, tailWord_3787535, baseEnd_3787535] using wordTrace_append hprefix tailTrace_3787535
  have hstable : (prefixWord ++ tailWord_3787535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787535).length < 2 ^ (prefixWord ++ tailWord_3787535).sum := by decide
  have hdescent : baseEnd_3787535 < baseStart_3787535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787704 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 4]
def baseStart_3787704 : Nat := 118140960795 + 3787704 * 2 ^ 59
def prefixEnd_3787704 : Nat := 4983230072969 + 3 ^ 40 * 3787704 * 2
def baseEnd_3787704 : Nat := 432202828657234183195705

theorem tailTrace_3787704 : CollatzResearch.WordTrace tailWord_3787704 prefixEnd_3787704 432202828657234183195705 := by
  unfold tailWord_3787704
  simp only [CollatzResearch.WordTrace]
  refine ⟨69074457134901385593449083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92099276179868514124598777 69074457134901385593449083)
  ·
    refine ⟨103611685702352078390173625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69074457134901385593449083 103611685702352078390173625)
    ·
      refine ⟨77708764276764058792630219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103611685702352078390173625 77708764276764058792630219)
      ·
        refine ⟨116563146415146088188945329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77708764276764058792630219 116563146415146088188945329)
        ·
          refine ⟨87422359811359566141708997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116563146415146088188945329 87422359811359566141708997)
          ·
            refine ⟨16391692464629918651570437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87422359811359566141708997 16391692464629918651570437)
            ·
              refine ⟨3073442337118109747169457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16391692464629918651570437 3073442337118109747169457)
              ·
                refine ⟨2305081752838582310377093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073442337118109747169457 2305081752838582310377093)
                ·
                  refine ⟨432202828657234183195705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305081752838582310377093 432202828657234183195705)
                  ·
                    rfl

theorem cell22_3787704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_3787704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787704 prefixEnd_3787704 := by exact prefixLift 3787704
  have htrace : WordTrace (prefixWord ++ tailWord_3787704) baseStart_3787704 baseEnd_3787704 := by
    simpa [prefixWord, tailWord_3787704, baseEnd_3787704] using wordTrace_append hprefix tailTrace_3787704
  have hstable : (prefixWord ++ tailWord_3787704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787704).length < 2 ^ (prefixWord ++ tailWord_3787704).sum := by decide
  have hdescent : baseEnd_3787704 < baseStart_3787704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787734 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3787734 : Nat := 118140960795 + 3787734 * 2 ^ 59
def prefixEnd_3787734 : Nat := 4983230072969 + 3 ^ 40 * 3787734 * 2
def baseEnd_3787734 : Nat := 1296618755584792471337023

theorem tailTrace_3787734 : CollatzResearch.WordTrace tailWord_3787734 prefixEnd_3787734 1296618755584792471337023 := by
  unfold tailWord_3787734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634375528730880394405641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92100005639796057540326837 8634375528730880394405641)
  ·
    refine ⟨6475781646548160295804231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8634375528730880394405641 6475781646548160295804231)
    ·
      refine ⟨9713672469822240443706347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6475781646548160295804231 9713672469822240443706347)
      ·
        refine ⟨14570508704733360665559521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9713672469822240443706347 14570508704733360665559521)
        ·
          refine ⟨10927881528550020499169641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14570508704733360665559521 10927881528550020499169641)
          ·
            refine ⟨8195911146412515374377231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10927881528550020499169641 8195911146412515374377231)
            ·
              refine ⟨12293866719618773061565847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195911146412515374377231 12293866719618773061565847)
              ·
                refine ⟨18440800079428159592348771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293866719618773061565847 18440800079428159592348771)
                ·
                  refine ⟨27661200119142239388523157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18440800079428159592348771 27661200119142239388523157)
                  ·
                    refine ⟨1296618755584792471337023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27661200119142239388523157 1296618755584792471337023)
                    ·
                      rfl

theorem cell22_3787734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3787734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787734 prefixEnd_3787734 := by exact prefixLift 3787734
  have htrace : WordTrace (prefixWord ++ tailWord_3787734) baseStart_3787734 baseEnd_3787734 := by
    simpa [prefixWord, tailWord_3787734, baseEnd_3787734] using wordTrace_append hprefix tailTrace_3787734
  have hstable : (prefixWord ++ tailWord_3787734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787734).length < 2 ^ (prefixWord ++ tailWord_3787734).sum := by decide
  have hdescent : baseEnd_3787734 < baseStart_3787734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787747 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 5, 3]
def baseStart_3787747 : Nat := 118140960795 + 3787747 * 2 ^ 59
def prefixEnd_3787747 : Nat := 4983230072969 + 3 ^ 40 * 3787747 * 2
def baseEnd_3787747 : Nat := 1296623205750464770761983

theorem tailTrace_3787747 : CollatzResearch.WordTrace tailWord_3787747 prefixEnd_3787747 1296623205750464770761983 := by
  unfold tailWord_3787747
  simp only [CollatzResearch.WordTrace]
  refine ⟨138150482608646989530713495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92100321739097993020475663 138150482608646989530713495)
  ·
    refine ⟨207225723912970484296070243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138150482608646989530713495 207225723912970484296070243)
    ·
      refine ⟨310838585869455726444105365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207225723912970484296070243 310838585869455726444105365)
      ·
        refine ⟨14570558712630737177067439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310838585869455726444105365 14570558712630737177067439)
        ·
          refine ⟨21855838068946105765601159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14570558712630737177067439 21855838068946105765601159)
          ·
            refine ⟨32783757103419158648401739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21855838068946105765601159 32783757103419158648401739)
            ·
              refine ⟨49175635655128737972602609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32783757103419158648401739 49175635655128737972602609)
              ·
                refine ⟨36881726741346553479451957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49175635655128737972602609 36881726741346553479451957)
                ·
                  refine ⟨3457661882001239388698621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36881726741346553479451957 3457661882001239388698621)
                  ·
                    refine ⟨1296623205750464770761983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457661882001239388698621 1296623205750464770761983)
                    ·
                      rfl

theorem cell22_3787747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 3].length) (baseStart_3787747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787747 prefixEnd_3787747 := by exact prefixLift 3787747
  have htrace : WordTrace (prefixWord ++ tailWord_3787747) baseStart_3787747 baseEnd_3787747 := by
    simpa [prefixWord, tailWord_3787747, baseEnd_3787747] using wordTrace_append hprefix tailTrace_3787747
  have hstable : (prefixWord ++ tailWord_3787747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787747).length < 2 ^ (prefixWord ++ tailWord_3787747).sum := by decide
  have hdescent : baseEnd_3787747 < baseStart_3787747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787815 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3787815 : Nat := 118140960795 + 3787815 * 2 ^ 59
def prefixEnd_3787815 : Nat := 4983230072969 + 3 ^ 40 * 3787815 * 2
def baseEnd_3787815 : Nat := 1296646483540135260061775

theorem tailTrace_3787815 : CollatzResearch.WordTrace tailWord_3787815 prefixEnd_3787815 1296646483540135260061775 := by
  unfold tailWord_3787815
  simp only [CollatzResearch.WordTrace]
  refine ⟨138152962772400637144188899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92101975181600424762792599 138152962772400637144188899)
  ·
    refine ⟨207229444158600955716283349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138152962772400637144188899 207229444158600955716283349)
    ·
      refine ⟨4856940097467209899600391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 207229444158600955716283349 4856940097467209899600391)
      ·
        refine ⟨7285410146200814849400587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856940097467209899600391 7285410146200814849400587)
        ·
          refine ⟨10928115219301222274100881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285410146200814849400587 10928115219301222274100881)
          ·
            refine ⟨8196086414475916705575661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10928115219301222274100881 8196086414475916705575661)
            ·
              refine ⟨3073532405428468764590873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8196086414475916705575661 3073532405428468764590873)
              ·
                refine ⟨2305149304071351573443155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073532405428468764590873 2305149304071351573443155)
                ·
                  refine ⟨3457723956107027360164733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305149304071351573443155 3457723956107027360164733)
                  ·
                    refine ⟨1296646483540135260061775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457723956107027360164733 1296646483540135260061775)
                    ·
                      rfl

theorem cell22_3787815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3787815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787815 prefixEnd_3787815 := by exact prefixLift 3787815
  have htrace : WordTrace (prefixWord ++ tailWord_3787815) baseStart_3787815 baseEnd_3787815 := by
    simpa [prefixWord, tailWord_3787815, baseEnd_3787815] using wordTrace_append hprefix tailTrace_3787815
  have hstable : (prefixWord ++ tailWord_3787815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787815).length < 2 ^ (prefixWord ++ tailWord_3787815).sum := by decide
  have hdescent : baseEnd_3787815 < baseStart_3787815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3787828 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3787828 : Nat := 118140960795 + 3787828 * 2 ^ 59
def prefixEnd_3787828 : Nat := 4983230072969 + 3 ^ 40 * 3787828 * 2
def baseEnd_3787828 : Nat := 432216977901935853162245

theorem tailTrace_3787828 : CollatzResearch.WordTrace tailWord_3787828 prefixEnd_3787828 432216977901935853162245 := by
  unfold tailWord_3787828
  simp only [CollatzResearch.WordTrace]
  refine ⟨69076718460676770182206069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92102291280902360242941425 69076718460676770182206069)
  ·
    refine ⟨6475942355688447204581819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69076718460676770182206069 6475942355688447204581819)
    ·
      refine ⟨9713913533532670806872729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6475942355688447204581819 9713913533532670806872729)
      ·
        refine ⟨7285435150149503105154547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9713913533532670806872729 7285435150149503105154547)
        ·
          refine ⟨10928152725224254657731821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285435150149503105154547 10928152725224254657731821)
          ·
            refine ⟨4098057271959095496649433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10928152725224254657731821 4098057271959095496649433)
            ·
              refine ⟨3073542953969321622487075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4098057271959095496649433 3073542953969321622487075)
              ·
                refine ⟨4610314430953982433730613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073542953969321622487075 4610314430953982433730613)
                ·
                  refine ⟨432216977901935853162245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4610314430953982433730613 432216977901935853162245)
                  ·
                    rfl

theorem cell22_3787828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3787828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3787828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3787828 prefixEnd_3787828 := by exact prefixLift 3787828
  have htrace : WordTrace (prefixWord ++ tailWord_3787828) baseStart_3787828 baseEnd_3787828 := by
    simpa [prefixWord, tailWord_3787828, baseEnd_3787828] using wordTrace_append hprefix tailTrace_3787828
  have hstable : (prefixWord ++ tailWord_3787828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3787828).length < 2 ^ (prefixWord ++ tailWord_3787828).sum := by decide
  have hdescent : baseEnd_3787828 < baseStart_3787828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3787828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788085 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3788085 : Nat := 118140960795 + 3788085 * 2 ^ 59
def prefixEnd_3788085 : Nat := 4983230072969 + 3 ^ 40 * 3788085 * 2
def baseEnd_3788085 : Nat := 1296738910057944555810947

theorem tailTrace_3788085 : CollatzResearch.WordTrace tailWord_3788085 prefixEnd_3788085 1296738910057944555810947 := by
  unfold tailWord_3788085
  simp only [CollatzResearch.WordTrace]
  refine ⟨138162810481422473256517709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92108540320948315504345139 138162810481422473256517709)
  ·
    refine ⟨51811053930533427471194141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138162810481422473256517709 51811053930533427471194141)
    ·
      refine ⟨19429145223950035301697803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51811053930533427471194141 19429145223950035301697803)
      ·
        refine ⟨29143717835925052952546705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19429145223950035301697803 29143717835925052952546705)
        ·
          refine ⟨21857788376943789714410029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29143717835925052952546705 21857788376943789714410029)
          ·
            refine ⟨8196670641353921142903761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21857788376943789714410029 8196670641353921142903761)
            ·
              refine ⟨6147502981015440857177821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8196670641353921142903761 6147502981015440857177821)
              ·
                refine ⟨2305313617880790321441683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6147502981015440857177821 2305313617880790321441683)
                ·
                  refine ⟨3457970426821185482162525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305313617880790321441683 3457970426821185482162525)
                  ·
                    refine ⟨1296738910057944555810947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457970426821185482162525 1296738910057944555810947)
                    ·
                      rfl

theorem cell22_3788085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3788085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788085 prefixEnd_3788085 := by exact prefixLift 3788085
  have htrace : WordTrace (prefixWord ++ tailWord_3788085) baseStart_3788085 baseEnd_3788085 := by
    simpa [prefixWord, tailWord_3788085, baseEnd_3788085] using wordTrace_append hprefix tailTrace_3788085
  have hstable : (prefixWord ++ tailWord_3788085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788085).length < 2 ^ (prefixWord ++ tailWord_3788085).sum := by decide
  have hdescent : baseEnd_3788085 < baseStart_3788085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788128 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_3788128 : Nat := 118140960795 + 3788128 * 2 ^ 59
def prefixEnd_3788128 : Nat := 4983230072969 + 3 ^ 40 * 3788128 * 2
def baseEnd_3788128 : Nat := 1296753629836706776985815

theorem tailTrace_3788128 : CollatzResearch.WordTrace tailWord_3788128 prefixEnd_3788128 1296753629836706776985815 := by
  unfold tailWord_3788128
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082189410133345800166519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92109585880177794400222025 69082189410133345800166519)
  ·
    refine ⟨103623284115200018700249779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69082189410133345800166519 103623284115200018700249779)
    ·
      refine ⟨155434926172800028050374669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103623284115200018700249779 155434926172800028050374669)
      ·
        refine ⟨58288097314800010518890501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155434926172800028050374669 58288097314800010518890501)
        ·
          refine ⟨10929018246525001972291969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58288097314800010518890501 10929018246525001972291969)
          ·
            refine ⟨8196763684893751479218977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10929018246525001972291969 8196763684893751479218977)
            ·
              refine ⟨6147572763670313609414233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8196763684893751479218977 6147572763670313609414233)
              ·
                refine ⟨4610679572752735207060675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6147572763670313609414233 4610679572752735207060675)
                ·
                  refine ⟨6916019359129102810591013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610679572752735207060675 6916019359129102810591013)
                  ·
                    refine ⟨1296753629836706776985815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916019359129102810591013 1296753629836706776985815)
                    ·
                      rfl

theorem cell22_3788128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_3788128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788128 prefixEnd_3788128 := by exact prefixLift 3788128
  have htrace : WordTrace (prefixWord ++ tailWord_3788128) baseStart_3788128 baseEnd_3788128 := by
    simpa [prefixWord, tailWord_3788128, baseEnd_3788128] using wordTrace_append hprefix tailTrace_3788128
  have hstable : (prefixWord ++ tailWord_3788128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788128).length < 2 ^ (prefixWord ++ tailWord_3788128).sum := by decide
  have hdescent : baseEnd_3788128 < baseStart_3788128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788156 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_3788156 : Nat := 118140960795 + 3788156 * 2 ^ 59
def prefixEnd_3788156 : Nat := 4983230072969 + 3 ^ 40 * 3788156 * 2
def baseEnd_3788156 : Nat := 1296763214808924037285729

theorem tailTrace_3788156 : CollatzResearch.WordTrace tailWord_3788156 prefixEnd_3788156 1296763214808924037285729 := by
  unfold tailWord_3788156
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082700032082626191176161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92110266709443501588234881 69082700032082626191176161)
  ·
    refine ⟨51812025024061969643382121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69082700032082626191176161 51812025024061969643382121)
    ·
      refine ⟨38859018768046477232536591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51812025024061969643382121 38859018768046477232536591)
      ·
        refine ⟨58288528152069715848804887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38859018768046477232536591 58288528152069715848804887)
        ·
          refine ⟨87432792228104573773207331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58288528152069715848804887 87432792228104573773207331)
          ·
            refine ⟨131149188342156860659810997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87432792228104573773207331 131149188342156860659810997)
            ·
              refine ⟨12295236407077205686857281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131149188342156860659810997 12295236407077205686857281)
              ·
                refine ⟨9221427305307904265142961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12295236407077205686857281 9221427305307904265142961)
                ·
                  refine ⟨6916070478980928198857221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9221427305307904265142961 6916070478980928198857221)
                  ·
                    refine ⟨1296763214808924037285729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916070478980928198857221 1296763214808924037285729)
                    ·
                      rfl

theorem cell22_3788156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_3788156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788156 prefixEnd_3788156 := by exact prefixLift 3788156
  have htrace : WordTrace (prefixWord ++ tailWord_3788156) baseStart_3788156 baseEnd_3788156 := by
    simpa [prefixWord, tailWord_3788156, baseEnd_3788156] using wordTrace_append hprefix tailTrace_3788156
  have hstable : (prefixWord ++ tailWord_3788156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788156).length < 2 ^ (prefixWord ++ tailWord_3788156).sum := by decide
  have hdescent : baseEnd_3788156 < baseStart_3788156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788216 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_3788216 : Nat := 118140960795 + 3788216 * 2 ^ 59
def prefixEnd_3788216 : Nat := 4983230072969 + 3 ^ 40 * 3788216 * 2
def baseEnd_3788216 : Nat := 432261251345034626928515

theorem tailTrace_3788216 : CollatzResearch.WordTrace tailWord_3788216 prefixEnd_3788216 432261251345034626928515 := by
  unfold tailWord_3788216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69083794221973941314768251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92111725629298588419691001 69083794221973941314768251)
  ·
    refine ⟨103625691332960911972152377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69083794221973941314768251 103625691332960911972152377)
    ·
      refine ⟨77719268499720683979114283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103625691332960911972152377 77719268499720683979114283)
      ·
        refine ⟨116578902749581025968671425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77719268499720683979114283 116578902749581025968671425)
        ·
          refine ⟨87434177062185769476503569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116578902749581025968671425 87434177062185769476503569)
          ·
            refine ⟨65575632796639327107377677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87434177062185769476503569 65575632796639327107377677)
            ·
              refine ⟨24590862298739747665266629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65575632796639327107377677 24590862298739747665266629)
              ·
                refine ⟨4610786681013702687237493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24590862298739747665266629 4610786681013702687237493)
                ·
                  refine ⟨432261251345034626928515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4610786681013702687237493 432261251345034626928515)
                  ·
                    rfl

theorem cell22_3788216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_3788216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788216 prefixEnd_3788216 := by exact prefixLift 3788216
  have htrace : WordTrace (prefixWord ++ tailWord_3788216) baseStart_3788216 baseEnd_3788216 := by
    simpa [prefixWord, tailWord_3788216, baseEnd_3788216] using wordTrace_append hprefix tailTrace_3788216
  have hstable : (prefixWord ++ tailWord_3788216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788216).length < 2 ^ (prefixWord ++ tailWord_3788216).sum := by decide
  have hdescent : baseEnd_3788216 < baseStart_3788216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788231 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3788231 : Nat := 118140960795 + 3788231 * 2 ^ 59
def prefixEnd_3788231 : Nat := 4983230072969 + 3 ^ 40 * 3788231 * 2
def baseEnd_3788231 : Nat := 1296788888841648841660499

theorem tailTrace_3788231 : CollatzResearch.WordTrace tailWord_3788231 prefixEnd_3788231 1296788888841648841660499 := by
  unfold tailWord_3788231
  simp only [CollatzResearch.WordTrace]
  refine ⟨138168135538893540191332547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92112090359262360127555031 138168135538893540191332547)
  ·
    refine ⟨207252203308340310286998821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138168135538893540191332547 207252203308340310286998821)
    ·
      refine ⟨38859788120313808178812279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207252203308340310286998821 38859788120313808178812279)
      ·
        refine ⟨58289682180470712268218419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38859788120313808178812279 58289682180470712268218419)
        ·
          refine ⟨87434523270706068402327629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58289682180470712268218419 87434523270706068402327629)
          ·
            refine ⟨32787946226514775650872861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87434523270706068402327629 32787946226514775650872861)
            ·
              refine ⟨12295479834943040869077323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32787946226514775650872861 12295479834943040869077323)
              ·
                refine ⟨18443219752414561303615985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12295479834943040869077323 18443219752414561303615985)
                ·
                  refine ⟨13832414814310920977711989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18443219752414561303615985 13832414814310920977711989)
                  ·
                    refine ⟨1296788888841648841660499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13832414814310920977711989 1296788888841648841660499)
                    ·
                      rfl

theorem cell22_3788231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3788231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788231 prefixEnd_3788231 := by exact prefixLift 3788231
  have htrace : WordTrace (prefixWord ++ tailWord_3788231) baseStart_3788231 baseEnd_3788231 := by
    simpa [prefixWord, tailWord_3788231, baseEnd_3788231] using wordTrace_append hprefix tailTrace_3788231
  have hstable : (prefixWord ++ tailWord_3788231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788231).length < 2 ^ (prefixWord ++ tailWord_3788231).sum := by decide
  have hdescent : baseEnd_3788231 < baseStart_3788231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788278 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3788278 : Nat := 118140960795 + 3788278 * 2 ^ 59
def prefixEnd_3788278 : Nat := 4983230072969 + 3 ^ 40 * 3788278 * 2
def baseEnd_3788278 : Nat := 432268325967385461911785

theorem tailTrace_3788278 : CollatzResearch.WordTrace tailWord_3788278 prefixEnd_3788278 432268325967385461911785 := by
  unfold tailWord_3788278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635615610607704201143343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92113233179815511478862325 8635615610607704201143343)
  ·
    refine ⟨12953423415911556301715015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635615610607704201143343 12953423415911556301715015)
    ·
      refine ⟨19430135123867334452572523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953423415911556301715015 19430135123867334452572523)
      ·
        refine ⟨29145202685801001678858785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19430135123867334452572523 29145202685801001678858785)
        ·
          refine ⟨21858902014350751259144089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29145202685801001678858785 21858902014350751259144089)
          ·
            refine ⟨16394176510763063444358067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21858902014350751259144089 16394176510763063444358067)
            ·
              refine ⟨24591264766144595166537101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16394176510763063444358067 24591264766144595166537101)
              ·
                refine ⟨9221724287304223187451413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24591264766144595166537101 9221724287304223187451413)
                ·
                  refine ⟨432268325967385461911785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9221724287304223187451413 432268325967385461911785)
                  ·
                    rfl

theorem cell22_3788278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3788278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788278 prefixEnd_3788278 := by exact prefixLift 3788278
  have htrace : WordTrace (prefixWord ++ tailWord_3788278) baseStart_3788278 baseEnd_3788278 := by
    simpa [prefixWord, tailWord_3788278, baseEnd_3788278] using wordTrace_append hprefix tailTrace_3788278
  have hstable : (prefixWord ++ tailWord_3788278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788278).length < 2 ^ (prefixWord ++ tailWord_3788278).sum := by decide
  have hdescent : baseEnd_3788278 < baseStart_3788278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788291 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 6, 4]
def baseStart_3788291 : Nat := 118140960795 + 3788291 * 2 ^ 59
def prefixEnd_3788291 : Nat := 4983230072969 + 3 ^ 40 * 3788291 * 2
def baseEnd_3788291 : Nat := 1296809428067828685160315

theorem tailTrace_3788291 : CollatzResearch.WordTrace tailWord_3788291 prefixEnd_3788291 1296809428067828685160315 := by
  unfold tailWord_3788291
  simp only [CollatzResearch.WordTrace]
  refine ⟨138170323918676170438516727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92113549279117446959011151 138170323918676170438516727)
  ·
    refine ⟨207255485878014255657775091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138170323918676170438516727 207255485878014255657775091)
    ·
      refine ⟨310883228817021383486662637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207255485878014255657775091 310883228817021383486662637)
      ·
        refine ⟨116581210806383018807498489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310883228817021383486662637 116581210806383018807498489)
        ·
          refine ⟨87435908104787264105623867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116581210806383018807498489 87435908104787264105623867)
          ·
            refine ⟨131153862157180896158435801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87435908104787264105623867 131153862157180896158435801)
            ·
              refine ⟨98365396617885672118826851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131153862157180896158435801 98365396617885672118826851)
              ·
                refine ⟨147548094926828508178240277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98365396617885672118826851 147548094926828508178240277)
                ·
                  refine ⟨6916316949695086320855013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147548094926828508178240277 6916316949695086320855013)
                  ·
                    refine ⟨1296809428067828685160315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916316949695086320855013 1296809428067828685160315)
                    ·
                      rfl

theorem cell22_3788291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_3788291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788291 prefixEnd_3788291 := by exact prefixLift 3788291
  have htrace : WordTrace (prefixWord ++ tailWord_3788291) baseStart_3788291 baseEnd_3788291 := by
    simpa [prefixWord, tailWord_3788291, baseEnd_3788291] using wordTrace_append hprefix tailTrace_3788291
  have hstable : (prefixWord ++ tailWord_3788291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788291).length < 2 ^ (prefixWord ++ tailWord_3788291).sum := by decide
  have hdescent : baseEnd_3788291 < baseStart_3788291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788312 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 4]
def baseStart_3788312 : Nat := 118140960795 + 3788312 * 2 ^ 59
def prefixEnd_3788312 : Nat := 4983230072969 + 3 ^ 40 * 3788312 * 2
def baseEnd_3788312 : Nat := 432272205598997210128417

theorem tailTrace_3788312 : CollatzResearch.WordTrace tailWord_3788312 prefixEnd_3788312 432272205598997210128417 := by
  unfold tailWord_3788312
  simp only [CollatzResearch.WordTrace]
  refine ⟨69085544925800045512515595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92114059901066727350020793 69085544925800045512515595)
  ·
    refine ⟨103628317388700068268773393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69085544925800045512515595 103628317388700068268773393)
    ·
      refine ⟨77721238041525051201580045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103628317388700068268773393 77721238041525051201580045)
      ·
        refine ⟨29145464265571894200592517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77721238041525051201580045 29145464265571894200592517)
        ·
          refine ⟨5464774549794730162611097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29145464265571894200592517 5464774549794730162611097)
          ·
            refine ⟨4098580912346047621958323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464774549794730162611097 4098580912346047621958323)
            ·
              refine ⟨6147871368519071432937485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098580912346047621958323 6147871368519071432937485)
              ·
                refine ⟨2305451763194651787351557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6147871368519071432937485 2305451763194651787351557)
                ·
                  refine ⟨432272205598997210128417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305451763194651787351557 432272205598997210128417)
                  ·
                    rfl

theorem cell22_3788312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_3788312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788312 prefixEnd_3788312 := by exact prefixLift 3788312
  have htrace : WordTrace (prefixWord ++ tailWord_3788312) baseStart_3788312 baseEnd_3788312 := by
    simpa [prefixWord, tailWord_3788312, baseEnd_3788312] using wordTrace_append hprefix tailTrace_3788312
  have hstable : (prefixWord ++ tailWord_3788312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788312).length < 2 ^ (prefixWord ++ tailWord_3788312).sum := by decide
  have hdescent : baseEnd_3788312 < baseStart_3788312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788323 : List Nat := [1, 1, 1, 4, 5, 2, 8]
def baseStart_3788323 : Nat := 118140960795 + 3788323 * 2 ^ 59
def prefixEnd_3788323 : Nat := 4983230072969 + 3 ^ 40 * 3788323 * 2
def baseEnd_3788323 : Nat := 48030384530436713642971

theorem tailTrace_3788323 : CollatzResearch.WordTrace tailWord_3788323 prefixEnd_3788323 48030384530436713642971 := by
  unfold tailWord_3788323
  simp only [CollatzResearch.WordTrace]
  refine ⟨138171491054560239903681623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92114327369706826602454415 138171491054560239903681623)
  ·
    refine ⟨207257236581840359855522435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138171491054560239903681623 207257236581840359855522435)
    ·
      refine ⟨310885854872760539783283653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207257236581840359855522435 310885854872760539783283653)
      ·
        refine ⟨58291097788642601209365685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310885854872760539783283653 58291097788642601209365685)
        ·
          refine ⟨5464790417685243863378033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58291097788642601209365685 5464790417685243863378033)
          ·
            refine ⟨4098592813263932897533525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464790417685243863378033 4098592813263932897533525)
            ·
              refine ⟨48030384530436713642971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4098592813263932897533525 48030384530436713642971)
              ·
                rfl

theorem cell22_3788323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 8].length) (baseStart_3788323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788323 prefixEnd_3788323 := by exact prefixLift 3788323
  have htrace : WordTrace (prefixWord ++ tailWord_3788323) baseStart_3788323 baseEnd_3788323 := by
    simpa [prefixWord, tailWord_3788323, baseEnd_3788323] using wordTrace_append hprefix tailTrace_3788323
  have hstable : (prefixWord ++ tailWord_3788323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788323).length < 2 ^ (prefixWord ++ tailWord_3788323).sum := by decide
  have hdescent : baseEnd_3788323 < baseStart_3788323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788336 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_3788336 : Nat := 118140960795 + 3788336 * 2 ^ 59
def prefixEnd_3788336 : Nat := 4983230072969 + 3 ^ 40 * 3788336 * 2
def baseEnd_3788336 : Nat := 1296824832487463567785177

theorem tailTrace_3788336 : CollatzResearch.WordTrace tailWord_3788336 prefixEnd_3788336 1296824832487463567785177 := by
  unfold tailWord_3788336
  simp only [CollatzResearch.WordTrace]
  refine ⟨69085982601756571561952431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92114643469008762082603241 69085982601756571561952431)
  ·
    refine ⟨103628973902634857342928647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69085982601756571561952431 103628973902634857342928647)
    ·
      refine ⟨155443460853952286014392971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103628973902634857342928647 155443460853952286014392971)
      ·
        refine ⟨233165191280928429021589457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155443460853952286014392971 233165191280928429021589457)
        ·
          refine ⟨174873893460696321766192093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233165191280928429021589457 174873893460696321766192093)
          ·
            refine ⟨65577710047761120662322035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174873893460696321766192093 65577710047761120662322035)
            ·
              refine ⟨98366565071641680993483053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65577710047761120662322035 98366565071641680993483053)
              ·
                refine ⟨36887461901865630372556145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98366565071641680993483053 36887461901865630372556145)
                ·
                  refine ⟨27665596426399222779417109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36887461901865630372556145 27665596426399222779417109)
                  ·
                    refine ⟨1296824832487463567785177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27665596426399222779417109 1296824832487463567785177)
                    ·
                      rfl

theorem cell22_3788336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_3788336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788336 prefixEnd_3788336 := by exact prefixLift 3788336
  have htrace : WordTrace (prefixWord ++ tailWord_3788336) baseStart_3788336 baseEnd_3788336 := by
    simpa [prefixWord, tailWord_3788336, baseEnd_3788336] using wordTrace_append hprefix tailTrace_3788336
  have hstable : (prefixWord ++ tailWord_3788336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788336).length < 2 ^ (prefixWord ++ tailWord_3788336).sum := by decide
  have hdescent : baseEnd_3788336 < baseStart_3788336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788372 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3788372 : Nat := 118140960795 + 3788372 * 2 ^ 59
def prefixEnd_3788372 : Nat := 4983230072969 + 3 ^ 40 * 3788372 * 2
def baseEnd_3788372 : Nat := 1296837156023171473885067

theorem tailTrace_3788372 : CollatzResearch.WordTrace tailWord_3788372 prefixEnd_3788372 1296837156023171473885067 := by
  unfold tailWord_3788372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69086639115691360636107685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92115518820921814181476913 69086639115691360636107685)
  ·
    refine ⟨12953744834192130119270191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69086639115691360636107685 12953744834192130119270191)
    ·
      refine ⟨19430617251288195178905287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953744834192130119270191 19430617251288195178905287)
      ·
        refine ⟨29145925876932292768357931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19430617251288195178905287 29145925876932292768357931)
        ·
          refine ⟨43718888815398439152536897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29145925876932292768357931 43718888815398439152536897)
          ·
            refine ⟨32789166611548829364402673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43718888815398439152536897 32789166611548829364402673)
            ·
              refine ⟨24591874958661622023302005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32789166611548829364402673 24591874958661622023302005)
              ·
                refine ⟨2305488277374527064684563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24591874958661622023302005 2305488277374527064684563)
                ·
                  refine ⟨3458232416061790597026845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305488277374527064684563 3458232416061790597026845)
                  ·
                    refine ⟨1296837156023171473885067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458232416061790597026845 1296837156023171473885067)
                    ·
                      rfl

theorem cell22_3788372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3788372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788372 prefixEnd_3788372 := by exact prefixLift 3788372
  have htrace : WordTrace (prefixWord ++ tailWord_3788372) baseStart_3788372 baseEnd_3788372 := by
    simpa [prefixWord, tailWord_3788372, baseEnd_3788372] using wordTrace_append hprefix tailTrace_3788372
  have hstable : (prefixWord ++ tailWord_3788372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788372).length < 2 ^ (prefixWord ++ tailWord_3788372).sum := by decide
  have hdescent : baseEnd_3788372 < baseStart_3788372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788389 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_3788389 : Nat := 118140960795 + 3788389 * 2 ^ 59
def prefixEnd_3788389 : Nat := 4983230072969 + 3 ^ 40 * 3788389 * 2
def baseEnd_3788389 : Nat := 1296842975470589096210015

theorem tailTrace_3788389 : CollatzResearch.WordTrace tailWord_3788389 prefixEnd_3788389 1296842975470589096210015 := by
  unfold tailWord_3788389
  simp only [CollatzResearch.WordTrace]
  refine ⟨138173898272321133175584221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92115932181547422117056147 138173898272321133175584221)
  ·
    refine ⟨51815211852120424940844083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138173898272321133175584221 51815211852120424940844083)
    ·
      refine ⟨77722817778180637411266125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51815211852120424940844083 77722817778180637411266125)
      ·
        refine ⟨29146056666817739029224797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77722817778180637411266125 29146056666817739029224797)
        ·
          refine ⟨10929771250056652135959299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29146056666817739029224797 10929771250056652135959299)
          ·
            refine ⟨16394656875084978203938949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929771250056652135959299 16394656875084978203938949)
            ·
              refine ⟨3073998164078433413238553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16394656875084978203938949 3073998164078433413238553)
              ·
                refine ⟨2305498623058825059928915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073998164078433413238553 2305498623058825059928915)
                ·
                  refine ⟨3458247934588237589893373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305498623058825059928915 3458247934588237589893373)
                  ·
                    refine ⟨1296842975470589096210015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458247934588237589893373 1296842975470589096210015)
                    ·
                      rfl

theorem cell22_3788389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_3788389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788389 prefixEnd_3788389 := by exact prefixLift 3788389
  have htrace : WordTrace (prefixWord ++ tailWord_3788389) baseStart_3788389 baseEnd_3788389 := by
    simpa [prefixWord, tailWord_3788389, baseEnd_3788389] using wordTrace_append hprefix tailTrace_3788389
  have hstable : (prefixWord ++ tailWord_3788389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788389).length < 2 ^ (prefixWord ++ tailWord_3788389).sum := by decide
  have hdescent : baseEnd_3788389 < baseStart_3788389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788413 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 8]
def baseStart_3788413 : Nat := 118140960795 + 3788413 * 2 ^ 59
def prefixEnd_3788413 : Nat := 4983230072969 + 3 ^ 40 * 3788413 * 2
def baseEnd_3788413 : Nat := 432283730387020344536647

theorem tailTrace_3788413 : CollatzResearch.WordTrace tailWord_3788413 prefixEnd_3788413 432283730387020344536647 := by
  unfold tailWord_3788413
  simp only [CollatzResearch.WordTrace]
  refine ⟨138174773624234185274457893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92116515749489456849638595 138174773624234185274457893)
  ·
    refine ⟨25907770054543909738960855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138174773624234185274457893 25907770054543909738960855)
    ·
      refine ⟨38861655081815864608441283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25907770054543909738960855 38861655081815864608441283)
      ·
        refine ⟨58292482622723796912661925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38861655081815864608441283 58292482622723796912661925)
        ·
          refine ⟨10929840491760711921124111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58292482622723796912661925 10929840491760711921124111)
          ·
            refine ⟨16394760737641067881686167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929840491760711921124111 16394760737641067881686167)
            ·
              refine ⟨24592141106461601822529251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16394760737641067881686167 24592141106461601822529251)
              ·
                refine ⟨36888211659692402733793877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24592141106461601822529251 36888211659692402733793877)
                ·
                  refine ⟨432283730387020344536647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36888211659692402733793877 432283730387020344536647)
                  ·
                    rfl

theorem cell22_3788413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_3788413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788413 prefixEnd_3788413 := by exact prefixLift 3788413
  have htrace : WordTrace (prefixWord ++ tailWord_3788413) baseStart_3788413 baseEnd_3788413 := by
    simpa [prefixWord, tailWord_3788413, baseEnd_3788413] using wordTrace_append hprefix tailTrace_3788413
  have hstable : (prefixWord ++ tailWord_3788413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788413).length < 2 ^ (prefixWord ++ tailWord_3788413).sum := by decide
  have hdescent : baseEnd_3788413 < baseStart_3788413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788428 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_3788428 : Nat := 118140960795 + 3788428 * 2 ^ 59
def prefixEnd_3788428 : Nat := 4983230072969 + 3 ^ 40 * 3788428 * 2
def baseEnd_3788428 : Nat := 1296856325967605994484895

theorem tailTrace_3788428 : CollatzResearch.WordTrace tailWord_3788428 prefixEnd_3788428 1296856325967605994484895 := by
  unfold tailWord_3788428
  simp only [CollatzResearch.WordTrace]
  refine ⟨69087660359589921418126969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92116880479453228557502625 69087660359589921418126969)
  ·
    refine ⟨51815745269692441063595227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69087660359589921418126969 51815745269692441063595227)
    ·
      refine ⟨77723617904538661595392841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51815745269692441063595227 77723617904538661595392841)
      ·
        refine ⟨58292713428403996196544631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77723617904538661595392841 58292713428403996196544631)
        ·
          refine ⟨87439070142605994294816947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58292713428403996196544631 87439070142605994294816947)
          ·
            refine ⟨131158605213908991442225421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87439070142605994294816947 131158605213908991442225421)
            ·
              refine ⟨49184476955215871790834533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131158605213908991442225421 49184476955215871790834533)
              ·
                refine ⟨9222089429102975960781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49184476955215871790834533 9222089429102975960781475)
                ·
                  refine ⟨13833134143654463941172213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9222089429102975960781475 13833134143654463941172213)
                  ·
                    refine ⟨1296856325967605994484895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13833134143654463941172213 1296856325967605994484895)
                    ·
                      rfl

theorem cell22_3788428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_3788428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788428 prefixEnd_3788428 := by exact prefixLift 3788428
  have htrace : WordTrace (prefixWord ++ tailWord_3788428) baseStart_3788428 baseEnd_3788428 := by
    simpa [prefixWord, tailWord_3788428, baseEnd_3788428] using wordTrace_append hprefix tailTrace_3788428
  have hstable : (prefixWord ++ tailWord_3788428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788428).length < 2 ^ (prefixWord ++ tailWord_3788428).sum := by decide
  have hdescent : baseEnd_3788428 < baseStart_3788428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788447 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 6]
def baseStart_3788447 : Nat := 118140960795 + 3788447 * 2 ^ 59
def prefixEnd_3788447 : Nat := 4983230072969 + 3 ^ 40 * 3788447 * 2
def baseEnd_3788447 : Nat := 432287610018632092753279

theorem tailTrace_3788447 : CollatzResearch.WordTrace tailWord_3788447 prefixEnd_3788447 432287610018632092753279 := by
  unfold tailWord_3788447
  simp only [CollatzResearch.WordTrace]
  refine ⟨138176013706111009081195595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92117342470740672720797063 138176013706111009081195595)
  ·
    refine ⟨207264020559166513621793393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138176013706111009081195595 207264020559166513621793393)
    ·
      refine ⟨155448015419374885216345045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207264020559166513621793393 155448015419374885216345045)
      ·
        refine ⟨3643312861391598872258087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 155448015419374885216345045 3643312861391598872258087)
        ·
          refine ⟨5464969292087398308387131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643312861391598872258087 5464969292087398308387131)
          ·
            refine ⟨8197453938131097462580697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464969292087398308387131 8197453938131097462580697)
            ·
              refine ⟨6148090453598323096935523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8197453938131097462580697 6148090453598323096935523)
              ·
                refine ⟨9222135680397484645403285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148090453598323096935523 9222135680397484645403285)
                ·
                  refine ⟨432287610018632092753279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9222135680397484645403285 432287610018632092753279)
                  ·
                    rfl

theorem cell22_3788447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 6].length) (baseStart_3788447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788447 prefixEnd_3788447 := by exact prefixLift 3788447
  have htrace : WordTrace (prefixWord ++ tailWord_3788447) baseStart_3788447 baseEnd_3788447 := by
    simpa [prefixWord, tailWord_3788447, baseEnd_3788447] using wordTrace_append hprefix tailTrace_3788447
  have hstable : (prefixWord ++ tailWord_3788447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788447).length < 2 ^ (prefixWord ++ tailWord_3788447).sum := by decide
  have hdescent : baseEnd_3788447 < baseStart_3788447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788492 : List Nat := [2, 2, 1, 5, 3, 1, 8]
def baseStart_3788492 : Nat := 118140960795 + 3788492 * 2 ^ 59
def prefixEnd_3788492 : Nat := 4983230072969 + 3 ^ 40 * 3788492 * 2
def baseEnd_3788492 : Nat := 48032527202797450403137

theorem tailTrace_3788492 : CollatzResearch.WordTrace tailWord_3788492 prefixEnd_3788492 48032527202797450403137 := by
  unfold tailWord_3788492
  simp only [CollatzResearch.WordTrace]
  refine ⟨69088827495473990883291865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92118436660631987844389153 69088827495473990883291865)
  ·
    refine ⟨51816620621605493162468899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69088827495473990883291865 51816620621605493162468899)
    ·
      refine ⟨77724930932408239743703349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51816620621605493162468899 77724930932408239743703349)
      ·
        refine ⟨7286712274913272475972189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77724930932408239743703349 7286712274913272475972189)
        ·
          refine ⟨2732517103092477178489571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7286712274913272475972189 2732517103092477178489571)
          ·
            refine ⟨4098775654638715767734357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732517103092477178489571 4098775654638715767734357)
            ·
              refine ⟨48032527202797450403137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4098775654638715767734357 48032527202797450403137)
              ·
                rfl

theorem cell22_3788492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 8].length) (baseStart_3788492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788492 prefixEnd_3788492 := by exact prefixLift 3788492
  have htrace : WordTrace (prefixWord ++ tailWord_3788492) baseStart_3788492 baseEnd_3788492 := by
    simpa [prefixWord, tailWord_3788492, baseEnd_3788492] using wordTrace_append hprefix tailTrace_3788492
  have hstable : (prefixWord ++ tailWord_3788492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788492).length < 2 ^ (prefixWord ++ tailWord_3788492).sum := by decide
  have hdescent : baseEnd_3788492 < baseStart_3788492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788503 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 7]
def baseStart_3788503 : Nat := 118140960795 + 3788503 * 2 ^ 59
def prefixEnd_3788503 : Nat := 4983230072969 + 3 ^ 40 * 3788503 * 2
def baseEnd_3788503 : Nat := 432294000000110266286555

theorem tailTrace_3788503 : CollatzResearch.WordTrace tailWord_3788503 prefixEnd_3788503 432294000000110266286555 := by
  unfold tailWord_3788503
  simp only [CollatzResearch.WordTrace]
  refine ⟨138178056193908130645234163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92118704129272087096822775 138178056193908130645234163)
  ·
    refine ⟨207267084290862195967851245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138178056193908130645234163 207267084290862195967851245)
    ·
      refine ⟨77725156609073323487944217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207267084290862195967851245 77725156609073323487944217)
      ·
        refine ⟨58293867456804992615958163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77725156609073323487944217 58293867456804992615958163)
        ·
          refine ⟨87440801185207488923937245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58293867456804992615958163 87440801185207488923937245)
          ·
            refine ⟨32790300444452808346476467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87440801185207488923937245 32790300444452808346476467)
            ·
              refine ⟨49185450666679212519714701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32790300444452808346476467 49185450666679212519714701)
              ·
                refine ⟨18444544000004704694893013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49185450666679212519714701 18444544000004704694893013)
                ·
                  refine ⟨432294000000110266286555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18444544000004704694893013 432294000000110266286555)
                  ·
                    rfl

theorem cell22_3788503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_3788503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788503 prefixEnd_3788503 := by exact prefixLift 3788503
  have htrace : WordTrace (prefixWord ++ tailWord_3788503) baseStart_3788503 baseEnd_3788503 := by
    simpa [prefixWord, tailWord_3788503, baseEnd_3788503] using wordTrace_append hprefix tailTrace_3788503
  have hstable : (prefixWord ++ tailWord_3788503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788503).length < 2 ^ (prefixWord ++ tailWord_3788503).sum := by decide
  have hdescent : baseEnd_3788503 < baseStart_3788503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788631 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 2, 3]
def baseStart_3788631 : Nat := 118140960795 + 3788631 * 2 ^ 59
def prefixEnd_3788631 : Nat := 4983230072969 + 3 ^ 40 * 3788631 * 2
def baseEnd_3788631 : Nat := 1296925817016181131659273

theorem tailTrace_3788631 : CollatzResearch.WordTrace tailWord_3788631 prefixEnd_3788631 1296925817016181131659273 := by
  unfold tailWord_3788631
  simp only [CollatzResearch.WordTrace]
  refine ⟨138182724737444408505893747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92121816491629605670595831 138182724737444408505893747)
  ·
    refine ⟨207274087106166612758840621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138182724737444408505893747 207274087106166612758840621)
    ·
      refine ⟨77727782664812479784565233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207274087106166612758840621 77727782664812479784565233)
      ·
        refine ⟨58295836998609359838423925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77727782664812479784565233 58295836998609359838423925)
        ·
          refine ⟨5465234718619627484852243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58295836998609359838423925 5465234718619627484852243)
          ·
            refine ⟨8197852077929441227278365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465234718619627484852243 8197852077929441227278365)
            ·
              refine ⟨3074194529223540460229387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8197852077929441227278365 3074194529223540460229387)
              ·
                refine ⟨4611291793835310690344081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074194529223540460229387 4611291793835310690344081)
                ·
                  refine ⟨3458468845376483017758061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4611291793835310690344081 3458468845376483017758061)
                  ·
                    refine ⟨1296925817016181131659273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458468845376483017758061 1296925817016181131659273)
                    ·
                      rfl

theorem cell22_3788631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_3788631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788631 prefixEnd_3788631 := by exact prefixLift 3788631
  have htrace : WordTrace (prefixWord ++ tailWord_3788631) baseStart_3788631 baseEnd_3788631 := by
    simpa [prefixWord, tailWord_3788631, baseEnd_3788631] using wordTrace_append hprefix tailTrace_3788631
  have hstable : (prefixWord ++ tailWord_3788631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788631).length < 2 ^ (prefixWord ++ tailWord_3788631).sum := by decide
  have hdescent : baseEnd_3788631 < baseStart_3788631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788644 : List Nat := [2, 3, 1, 1, 5, 2, 2, 6]
def baseStart_3788644 : Nat := 118140960795 + 3788644 * 2 ^ 59
def prefixEnd_3788644 : Nat := 4983230072969 + 3 ^ 40 * 3788644 * 2
def baseEnd_3788644 : Nat := 144103363020205936787137

theorem tailTrace_3788644 : CollatzResearch.WordTrace tailWord_3788644 prefixEnd_3788644 144103363020205936787137 := by
  unfold tailWord_3788644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69091599443198655863058493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92122132590931541150744657 69091599443198655863058493)
  ·
    refine ⟨25909349791199495948646935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69091599443198655863058493 25909349791199495948646935)
    ·
      refine ⟨38864024686799243922970403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25909349791199495948646935 38864024686799243922970403)
      ·
        refine ⟨58296037030198865884455605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38864024686799243922970403 58296037030198865884455605)
        ·
          refine ⟨5465253471581143676667713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58296037030198865884455605 5465253471581143676667713)
          ·
            refine ⟨4098940103685857757500785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465253471581143676667713 4098940103685857757500785)
            ·
              refine ⟨3074205077764393318125589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4098940103685857757500785 3074205077764393318125589)
              ·
                refine ⟨144103363020205936787137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3074205077764393318125589 144103363020205936787137)
                ·
                  rfl

theorem cell22_3788644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 6].length) (baseStart_3788644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788644 prefixEnd_3788644 := by exact prefixLift 3788644
  have htrace : WordTrace (prefixWord ++ tailWord_3788644) baseStart_3788644 baseEnd_3788644 := by
    simpa [prefixWord, tailWord_3788644, baseEnd_3788644] using wordTrace_append hprefix tailTrace_3788644
  have hstable : (prefixWord ++ tailWord_3788644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788644).length < 2 ^ (prefixWord ++ tailWord_3788644).sum := by decide
  have hdescent : baseEnd_3788644 < baseStart_3788644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788719 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 1, 4]
def baseStart_3788719 : Nat := 118140960795 + 3788719 * 2 ^ 59
def prefixEnd_3788719 : Nat := 4983230072969 + 3 ^ 40 * 3788719 * 2
def baseEnd_3788719 : Nat := 1296955941214578235459003

theorem tailTrace_3788719 : CollatzResearch.WordTrace tailWord_3788719 prefixEnd_3788719 1296955941214578235459003 := by
  unfold tailWord_3788719
  simp only [CollatzResearch.WordTrace]
  refine ⟨138185934361125599535097211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92123956240750399690064807 138185934361125599535097211)
  ·
    refine ⟨207278901541688399302645817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138185934361125599535097211 207278901541688399302645817)
    ·
      refine ⟨155459176156266299476984363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207278901541688399302645817 155459176156266299476984363)
      ·
        refine ⟨233188764234399449215476545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155459176156266299476984363 233188764234399449215476545)
        ·
          refine ⟨174891573175799586911607409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233188764234399449215476545 174891573175799586911607409)
          ·
            refine ⟨131168679881849690183705557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174891573175799586911607409 131168679881849690183705557)
            ·
              refine ⟨3074265934730852113680599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131168679881849690183705557 3074265934730852113680599)
              ·
                refine ⟨4611398902096278170520899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074265934730852113680599 4611398902096278170520899)
                ·
                  refine ⟨6917098353144417255781349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4611398902096278170520899 6917098353144417255781349)
                  ·
                    refine ⟨1296955941214578235459003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917098353144417255781349 1296955941214578235459003)
                    ·
                      rfl

theorem cell22_3788719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_3788719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788719 prefixEnd_3788719 := by exact prefixLift 3788719
  have htrace : WordTrace (prefixWord ++ tailWord_3788719) baseStart_3788719 baseEnd_3788719 := by
    simpa [prefixWord, tailWord_3788719, baseEnd_3788719] using wordTrace_append hprefix tailTrace_3788719
  have hstable : (prefixWord ++ tailWord_3788719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788719).length < 2 ^ (prefixWord ++ tailWord_3788719).sum := by decide
  have hdescent : baseEnd_3788719 < baseStart_3788719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788770 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3788770 : Nat := 118140960795 + 3788770 * 2 ^ 59
def prefixEnd_3788770 : Nat := 4983230072969 + 3 ^ 40 * 3788770 * 2
def baseEnd_3788770 : Nat := 1296973399556831102433847

theorem tailTrace_3788770 : CollatzResearch.WordTrace tailWord_3788770 prefixEnd_3788770 1296973399556831102433847 := by
  unfold tailWord_3788770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546948620985208811300941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92125196322627223496802509 34546948620985208811300941)
  ·
    refine ⟨12955105732869453304237853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34546948620985208811300941 12955105732869453304237853)
    ·
      refine ⟨4858164649826044989089195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12955105732869453304237853 4858164649826044989089195)
      ·
        refine ⟨7287246974739067483633793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858164649826044989089195 7287246974739067483633793)
        ·
          refine ⟨5465435231054300612725345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7287246974739067483633793 5465435231054300612725345)
          ·
            refine ⟨4099076423290725459544009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465435231054300612725345 4099076423290725459544009)
            ·
              refine ⟨3074307317468044094658007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099076423290725459544009 3074307317468044094658007)
              ·
                refine ⟨4611460976202066141987011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074307317468044094658007 4611460976202066141987011)
                ·
                  refine ⟨6917191464303099212980517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4611460976202066141987011 6917191464303099212980517)
                  ·
                    refine ⟨1296973399556831102433847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917191464303099212980517 1296973399556831102433847)
                    ·
                      rfl

theorem cell22_3788770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3788770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788770 prefixEnd_3788770 := by exact prefixLift 3788770
  have htrace : WordTrace (prefixWord ++ tailWord_3788770) baseStart_3788770 baseEnd_3788770 := by
    simpa [prefixWord, tailWord_3788770, baseEnd_3788770] using wordTrace_append hprefix tailTrace_3788770
  have hstable : (prefixWord ++ tailWord_3788770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788770).length < 2 ^ (prefixWord ++ tailWord_3788770).sum := by decide
  have hdescent : baseEnd_3788770 < baseStart_3788770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788813 : List Nat := [1, 7, 1, 2, 1, 1, 1, 8]
def baseStart_3788813 : Nat := 118140960795 + 3788813 * 2 ^ 59
def prefixEnd_3788813 : Nat := 4983230072969 + 3 ^ 40 * 3788813 * 2
def baseEnd_3788813 : Nat := 144109791037288147067635

theorem tailTrace_3788813 : CollatzResearch.WordTrace tailWord_3788813 prefixEnd_3788813 144109791037288147067635 := by
  unfold tailWord_3788813
  simp only [CollatzResearch.WordTrace]
  refine ⟨138189362822785053589019093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92126241881856702392679395 138189362822785053589019093)
  ·
    refine ⟨3238813191159024693492635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 138189362822785053589019093 3238813191159024693492635)
    ·
      refine ⟨4858219786738537040238953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238813191159024693492635 4858219786738537040238953)
      ·
        refine ⟨3643664840053902780179215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4858219786738537040238953 3643664840053902780179215)
        ·
          refine ⟨5465497260080854170268823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643664840053902780179215 5465497260080854170268823)
          ·
            refine ⟨8198245890121281255403235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465497260080854170268823 8198245890121281255403235)
            ·
              refine ⟨12297368835181921883104853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198245890121281255403235 12297368835181921883104853)
              ·
                refine ⟨144109791037288147067635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12297368835181921883104853 144109791037288147067635)
                ·
                  rfl

theorem cell22_3788813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 8].length) (baseStart_3788813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788813 prefixEnd_3788813 := by exact prefixLift 3788813
  have htrace : WordTrace (prefixWord ++ tailWord_3788813) baseStart_3788813 baseEnd_3788813 := by
    simpa [prefixWord, tailWord_3788813, baseEnd_3788813] using wordTrace_append hprefix tailTrace_3788813
  have hstable : (prefixWord ++ tailWord_3788813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788813).length < 2 ^ (prefixWord ++ tailWord_3788813).sum := by decide
  have hdescent : baseEnd_3788813 < baseStart_3788813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788828 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_3788828 : Nat := 118140960795 + 3788828 * 2 ^ 59
def prefixEnd_3788828 : Nat := 4983230072969 + 3 ^ 40 * 3788828 * 2
def baseEnd_3788828 : Nat := 1296993254142138284483669

theorem tailTrace_3788828 : CollatzResearch.WordTrace tailWord_3788828 prefixEnd_3788828 1296993254142138284483669 := by
  unfold tailWord_3788828
  simp only [CollatzResearch.WordTrace]
  refine ⟨69094954958865355575407569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92126606611820474100543425 69094954958865355575407569)
  ·
    refine ⟨51821216219149016681555677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69094954958865355575407569 51821216219149016681555677)
    ·
      refine ⟨19432956082180881255583379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51821216219149016681555677 19432956082180881255583379)
      ·
        refine ⟨29149434123271321883375069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19432956082180881255583379 29149434123271321883375069)
        ·
          refine ⟨10931037796226745706265651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29149434123271321883375069 10931037796226745706265651)
          ·
            refine ⟨16396556694340118559398477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10931037796226745706265651 16396556694340118559398477)
            ·
              refine ⟨6148708760377544459774429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16396556694340118559398477 6148708760377544459774429)
              ·
                refine ⟨2305765785141579172415411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6148708760377544459774429 2305765785141579172415411)
                ·
                  refine ⟨3458648677712368758623117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305765785141579172415411 3458648677712368758623117)
                  ·
                    refine ⟨1296993254142138284483669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458648677712368758623117 1296993254142138284483669)
                    ·
                      rfl

theorem cell22_3788828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_3788828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788828 prefixEnd_3788828 := by exact prefixLift 3788828
  have htrace : WordTrace (prefixWord ++ tailWord_3788828) baseStart_3788828 baseEnd_3788828 := by
    simpa [prefixWord, tailWord_3788828, baseEnd_3788828] using wordTrace_append hprefix tailTrace_3788828
  have hstable : (prefixWord ++ tailWord_3788828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788828).length < 2 ^ (prefixWord ++ tailWord_3788828).sum := by decide
  have hdescent : baseEnd_3788828 < baseStart_3788828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788899 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 2, 4]
def baseStart_3788899 : Nat := 118140960795 + 3788899 * 2 ^ 59
def prefixEnd_3788899 : Nat := 4983230072969 + 3 ^ 40 * 3788899 * 2
def baseEnd_3788899 : Nat := 1297017558893117765958451

theorem tailTrace_3788899 : CollatzResearch.WordTrace tailWord_3788899 prefixEnd_3788899 1297017558893117765958451 := by
  unfold tailWord_3788899
  simp only [CollatzResearch.WordTrace]
  refine ⟨138192499500473490276649751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92128333000315660184433167 138192499500473490276649751)
  ·
    refine ⟨207288749250710235414974627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138192499500473490276649751 207288749250710235414974627)
    ·
      refine ⟨310933123876065353122461941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207288749250710235414974627 310933123876065353122461941)
      ·
        refine ⟨29149980363381126855230807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310933123876065353122461941 29149980363381126855230807)
        ·
          refine ⟨43724970545071690282846211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29149980363381126855230807 43724970545071690282846211)
          ·
            refine ⟨65587455817607535424269317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43724970545071690282846211 65587455817607535424269317)
            ·
              refine ⟨12297647965801412892050497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65587455817607535424269317 12297647965801412892050497)
              ·
                refine ⟨9223235974351059669037873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12297647965801412892050497 9223235974351059669037873)
                ·
                  refine ⟨6917426980763294751778405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9223235974351059669037873 6917426980763294751778405)
                  ·
                    refine ⟨1297017558893117765958451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917426980763294751778405 1297017558893117765958451)
                    ·
                      rfl

theorem cell22_3788899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_3788899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788899 prefixEnd_3788899 := by exact prefixLift 3788899
  have htrace : WordTrace (prefixWord ++ tailWord_3788899) baseStart_3788899 baseEnd_3788899 := by
    simpa [prefixWord, tailWord_3788899, baseEnd_3788899] using wordTrace_append hprefix tailTrace_3788899
  have hstable : (prefixWord ++ tailWord_3788899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788899).length < 2 ^ (prefixWord ++ tailWord_3788899).sum := by decide
  have hdescent : baseEnd_3788899 < baseStart_3788899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788901 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 2, 3]
def baseStart_3788901 : Nat := 118140960795 + 3788901 * 2 ^ 59
def prefixEnd_3788901 : Nat := 4983230072969 + 3 ^ 40 * 3788901 * 2
def baseEnd_3788901 : Nat := 1297018243533990427408445

theorem tailTrace_3788901 : CollatzResearch.WordTrace tailWord_3788901 prefixEnd_3788901 1297018243533990427408445 := by
  unfold tailWord_3788901
  simp only [CollatzResearch.WordTrace]
  refine ⟨138192572446466244618222557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92128381630977496412148371 138192572446466244618222557)
  ·
    refine ⟨51822214667424841731833459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138192572446466244618222557 51822214667424841731833459)
    ·
      refine ⟨77733322001137262597750189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51822214667424841731833459 77733322001137262597750189)
      ·
        refine ⟨29149995750426473474156321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77733322001137262597750189 29149995750426473474156321)
        ·
          refine ⟨21862496812819855105617241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29149995750426473474156321 21862496812819855105617241)
          ·
            refine ⟨16396872609614891329212931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21862496812819855105617241 16396872609614891329212931)
            ·
              refine ⟨24595308914422336993819397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16396872609614891329212931 24595308914422336993819397)
              ·
                refine ⟨4611620421454188186341137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24595308914422336993819397 4611620421454188186341137)
                ·
                  refine ⟨3458715316090641139755853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4611620421454188186341137 3458715316090641139755853)
                  ·
                    refine ⟨1297018243533990427408445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458715316090641139755853 1297018243533990427408445)
                    ·
                      rfl

theorem cell22_3788901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_3788901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788901 prefixEnd_3788901 := by exact prefixLift 3788901
  have htrace : WordTrace (prefixWord ++ tailWord_3788901) baseStart_3788901 baseEnd_3788901 := by
    simpa [prefixWord, tailWord_3788901, baseEnd_3788901] using wordTrace_append hprefix tailTrace_3788901
  have hstable : (prefixWord ++ tailWord_3788901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788901).length < 2 ^ (prefixWord ++ tailWord_3788901).sum := by decide
  have hdescent : baseEnd_3788901 < baseStart_3788901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788914 : List Nat := [3, 2, 1, 2, 2, 2, 3, 7]
def baseStart_3788914 : Nat := 118140960795 + 3788914 * 2 ^ 59
def prefixEnd_3788914 : Nat := 4983230072969 + 3 ^ 40 * 3788914 * 2
def baseEnd_3788914 : Nat := 144113632633295858537045

theorem tailTrace_3788914 : CollatzResearch.WordTrace tailWord_3788914 prefixEnd_3788914 144113632633295858537045 := by
  unfold tailWord_3788914
  simp only [CollatzResearch.WordTrace]
  refine ⟨34548261648854786959611449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92128697730279431892297197 34548261648854786959611449)
  ·
    refine ⟨25911196236641090219708587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34548261648854786959611449 25911196236641090219708587)
    ·
      refine ⟨38866794354961635329562881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25911196236641090219708587 38866794354961635329562881)
      ·
        refine ⟨29150095766221226497172161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38866794354961635329562881 29150095766221226497172161)
        ·
          refine ⟨21862571824665919872879121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29150095766221226497172161 21862571824665919872879121)
          ·
            refine ⟨16396928868499439904659341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21862571824665919872879121 16396928868499439904659341)
            ·
              refine ⟨6148848325687289964247253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16396928868499439904659341 6148848325687289964247253)
              ·
                refine ⟨144113632633295858537045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6148848325687289964247253 144113632633295858537045)
                ·
                  rfl

theorem cell22_3788914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_3788914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788914 prefixEnd_3788914 := by exact prefixLift 3788914
  have htrace : WordTrace (prefixWord ++ tailWord_3788914) baseStart_3788914 baseEnd_3788914 := by
    simpa [prefixWord, tailWord_3788914, baseEnd_3788914] using wordTrace_append hprefix tailTrace_3788914
  have hstable : (prefixWord ++ tailWord_3788914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788914).length < 2 ^ (prefixWord ++ tailWord_3788914).sum := by decide
  have hdescent : baseEnd_3788914 < baseStart_3788914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788918 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3788918 : Nat := 118140960795 + 3788918 * 2 ^ 59
def prefixEnd_3788918 : Nat := 4983230072969 + 3 ^ 40 * 3788918 * 2
def baseEnd_3788918 : Nat := 1297024062981408049733393

theorem tailTrace_3788918 : CollatzResearch.WordTrace tailWord_3788918 prefixEnd_3788918 1297024062981408049733393 := by
  unfold tailWord_3788918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637074530462791032599463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92128794991603104347727605 8637074530462791032599463)
  ·
    refine ⟨12955611795694186548899195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8637074530462791032599463 12955611795694186548899195)
    ·
      refine ⟨19433417693541279823348793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12955611795694186548899195 19433417693541279823348793)
      ·
        refine ⟨14575063270155959867511595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19433417693541279823348793 14575063270155959867511595)
        ·
          refine ⟨21862594905233939801267393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14575063270155959867511595 21862594905233939801267393)
          ·
            refine ⟨16396946178925454850950545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21862594905233939801267393 16396946178925454850950545)
            ·
              refine ⟨12297709634194091138212909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16396946178925454850950545 12297709634194091138212909)
              ·
                refine ⟨4611641112822784176829841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12297709634194091138212909 4611641112822784176829841)
                ·
                  refine ⟨3458730834617088132622381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4611641112822784176829841 3458730834617088132622381)
                  ·
                    refine ⟨1297024062981408049733393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458730834617088132622381 1297024062981408049733393)
                    ·
                      rfl

theorem cell22_3788918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3788918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788918 prefixEnd_3788918 := by exact prefixLift 3788918
  have htrace : WordTrace (prefixWord ++ tailWord_3788918) baseStart_3788918 baseEnd_3788918 := by
    simpa [prefixWord, tailWord_3788918, baseEnd_3788918] using wordTrace_append hprefix tailTrace_3788918
  have hstable : (prefixWord ++ tailWord_3788918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788918).length < 2 ^ (prefixWord ++ tailWord_3788918).sum := by decide
  have hdescent : baseEnd_3788918 < baseStart_3788918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3788946 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3788946 : Nat := 118140960795 + 3788946 * 2 ^ 59
def prefixEnd_3788946 : Nat := 4983230072969 + 3 ^ 40 * 3788946 * 2
def baseEnd_3788946 : Nat := 1297033647953625310033307

theorem tailTrace_3788946 : CollatzResearch.WordTrace tailWord_3788946 prefixEnd_3788946 1297033647953625310033307 := by
  unfold tailWord_3788946
  simp only [CollatzResearch.WordTrace]
  refine ⟨34548553432825804325902673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92129475820868811535740461 34548553432825804325902673)
  ·
    refine ⟨25911415074619353244427005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34548553432825804325902673 25911415074619353244427005)
    ·
      refine ⟨9716780652982257466660127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25911415074619353244427005 9716780652982257466660127)
      ·
        refine ⟨14575170979473386199990191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716780652982257466660127 14575170979473386199990191)
        ·
          refine ⟨21862756469210079299985287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14575170979473386199990191 21862756469210079299985287)
          ·
            refine ⟨32794134703815118949977931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21862756469210079299985287 32794134703815118949977931)
            ·
              refine ⟨49191202055722678424966897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32794134703815118949977931 49191202055722678424966897)
              ·
                refine ⟨36893401541792008818725173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49191202055722678424966897 36893401541792008818725173)
                ·
                  refine ⟨3458756394543000826755485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36893401541792008818725173 3458756394543000826755485)
                  ·
                    refine ⟨1297033647953625310033307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458756394543000826755485 1297033647953625310033307)
                    ·
                      rfl

theorem cell22_3788946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3788946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3788946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3788946 prefixEnd_3788946 := by exact prefixLift 3788946
  have htrace : WordTrace (prefixWord ++ tailWord_3788946) baseStart_3788946 baseEnd_3788946 := by
    simpa [prefixWord, tailWord_3788946, baseEnd_3788946] using wordTrace_append hprefix tailTrace_3788946
  have hstable : (prefixWord ++ tailWord_3788946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3788946).length < 2 ^ (prefixWord ++ tailWord_3788946).sum := by decide
  have hdescent : baseEnd_3788946 < baseStart_3788946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3788946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789014 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3789014 : Nat := 118140960795 + 3789014 * 2 ^ 59
def prefixEnd_3789014 : Nat := 4983230072969 + 3 ^ 40 * 3789014 * 2
def baseEnd_3789014 : Nat := 1297056925743295799333099

theorem tailTrace_3789014 : CollatzResearch.WordTrace tailWord_3789014 prefixEnd_3789014 1297056925743295799333099 := by
  unfold tailWord_3789014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637293368441054057317881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92131129263371243278057397 8637293368441054057317881)
  ·
    refine ⟨6477970026330790542988411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8637293368441054057317881 6477970026330790542988411)
    ·
      refine ⟨9716955039496185814482617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6477970026330790542988411 9716955039496185814482617)
      ·
        refine ⟨7287716279622139360861963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9716955039496185814482617 7287716279622139360861963)
        ·
          refine ⟨10931574419433209041292945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287716279622139360861963 10931574419433209041292945)
          ·
            refine ⟨8198680814574906780969709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10931574419433209041292945 8198680814574906780969709)
            ·
              refine ⟨3074505305465590042863641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8198680814574906780969709 3074505305465590042863641)
              ·
                refine ⟨2305878979099192532147731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074505305465590042863641 2305878979099192532147731)
                ·
                  refine ⟨3458818468648788798221597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305878979099192532147731 3458818468648788798221597)
                  ·
                    refine ⟨1297056925743295799333099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458818468648788798221597 1297056925743295799333099)
                    ·
                      rfl

theorem cell22_3789014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3789014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789014 prefixEnd_3789014 := by exact prefixLift 3789014
  have htrace : WordTrace (prefixWord ++ tailWord_3789014) baseStart_3789014 baseEnd_3789014 := by
    simpa [prefixWord, tailWord_3789014, baseEnd_3789014] using wordTrace_append hprefix tailTrace_3789014
  have hstable : (prefixWord ++ tailWord_3789014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789014).length < 2 ^ (prefixWord ++ tailWord_3789014).sum := by decide
  have hdescent : baseEnd_3789014 < baseStart_3789014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789027 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 5]
def baseStart_3789027 : Nat := 118140960795 + 3789027 * 2 ^ 59
def prefixEnd_3789027 : Nat := 4983230072969 + 3 ^ 40 * 3789027 * 2
def baseEnd_3789027 : Nat := 432353791969656032919353

theorem tailTrace_3789027 : CollatzResearch.WordTrace tailWord_3789027 prefixEnd_3789027 432353791969656032919353 := by
  unfold tailWord_3789027
  simp only [CollatzResearch.WordTrace]
  refine ⟨138197168044009768137309335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92131445362673178758206223 138197168044009768137309335)
  ·
    refine ⟨207295752066014652205964003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138197168044009768137309335 207295752066014652205964003)
    ·
      refine ⟨310943628099021978308946005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207295752066014652205964003 310943628099021978308946005)
      ·
        refine ⟨3643870641785413808307961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 310943628099021978308946005 3643870641785413808307961)
        ·
          refine ⟨2732902981339060356230971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3643870641785413808307961 2732902981339060356230971)
          ·
            refine ⟨4099354472008590534346457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732902981339060356230971 4099354472008590534346457)
            ·
              refine ⟨3074515854006442900759843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099354472008590534346457 3074515854006442900759843)
              ·
                refine ⟨4611773781009664351139765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074515854006442900759843 4611773781009664351139765)
                ·
                  refine ⟨432353791969656032919353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4611773781009664351139765 432353791969656032919353)
                  ·
                    rfl

theorem cell22_3789027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 5].length) (baseStart_3789027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789027 prefixEnd_3789027 := by exact prefixLift 3789027
  have htrace : WordTrace (prefixWord ++ tailWord_3789027) baseStart_3789027 baseEnd_3789027 := by
    simpa [prefixWord, tailWord_3789027, baseEnd_3789027] using wordTrace_append hprefix tailTrace_3789027
  have hstable : (prefixWord ++ tailWord_3789027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789027).length < 2 ^ (prefixWord ++ tailWord_3789027).sum := by decide
  have hdescent : baseEnd_3789027 < baseStart_3789027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789102 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3789102 : Nat := 118140960795 + 3789102 * 2 ^ 59
def prefixEnd_3789102 : Nat := 4983230072969 + 3 ^ 40 * 3789102 * 2
def baseEnd_3789102 : Nat := 1297087049941692903132829

theorem tailTrace_3789102 : CollatzResearch.WordTrace tailWord_3789102 prefixEnd_3789102 1297087049941692903132829 := by
  unfold tailWord_3789102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17274987939842256993286195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92133269012492037297526373 17274987939842256993286195)
  ·
    refine ⟨25912481909763385489929293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17274987939842256993286195 25912481909763385489929293)
    ·
      refine ⟨9717180716161269558723485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25912481909763385489929293 9717180716161269558723485)
      ·
        refine ⟨3643942768560476084521307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9717180716161269558723485 3643942768560476084521307)
        ·
          refine ⟨5465914152840714126781961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643942768560476084521307 5465914152840714126781961)
          ·
            refine ⟨4099435614630535595086471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465914152840714126781961 4099435614630535595086471)
            ·
              refine ⟨6149153421945803392629707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099435614630535595086471 6149153421945803392629707)
              ·
                refine ⟨9223730132918705088944561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149153421945803392629707 9223730132918705088944561)
                ·
                  refine ⟨6917797599689028816708421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9223730132918705088944561 6917797599689028816708421)
                  ·
                    refine ⟨1297087049941692903132829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917797599689028816708421 1297087049941692903132829)
                    ·
                      rfl

theorem cell22_3789102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3789102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789102 prefixEnd_3789102 := by exact prefixLift 3789102
  have htrace : WordTrace (prefixWord ++ tailWord_3789102) baseStart_3789102 baseEnd_3789102 := by
    simpa [prefixWord, tailWord_3789102, baseEnd_3789102] using wordTrace_append hprefix tailTrace_3789102
  have hstable : (prefixWord ++ tailWord_3789102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789102).length < 2 ^ (prefixWord ++ tailWord_3789102).sum := by decide
  have hdescent : baseEnd_3789102 < baseStart_3789102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3789156 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_3789156 : Nat := 118140960795 + 3789156 * 2 ^ 59
def prefixEnd_3789156 : Nat := 4983230072969 + 3 ^ 40 * 3789156 * 2
def baseEnd_3789156 : Nat := 432368511748418254094221

theorem tailTrace_3789156 : CollatzResearch.WordTrace tailWord_3789156 prefixEnd_3789156 432368511748418254094221 := by
  unfold tailWord_3789156
  simp only [CollatzResearch.WordTrace]
  refine ⟨69100936530271211584377661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92134582040361615445836881 69100936530271211584377661)
  ·
    refine ⟨25912851198851704344141623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69100936530271211584377661 25912851198851704344141623)
    ·
      refine ⟨38869276798277556516212435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25912851198851704344141623 38869276798277556516212435)
      ·
        refine ⟨58303915197416334774318653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38869276798277556516212435 58303915197416334774318653)
        ·
          refine ⟨21863968199031125540369495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58303915197416334774318653 21863968199031125540369495)
          ·
            refine ⟨32795952298546688310554243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21863968199031125540369495 32795952298546688310554243)
            ·
              refine ⟨49193928447820032465831365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32795952298546688310554243 49193928447820032465831365)
              ·
                refine ⟨9223861583966256087343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49193928447820032465831365 9223861583966256087343381)
                ·
                  refine ⟨432368511748418254094221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9223861583966256087343381 432368511748418254094221)
                  ·
                    rfl

theorem cell22_3789156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_3789156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3789156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3789156 prefixEnd_3789156 := by exact prefixLift 3789156
  have htrace : WordTrace (prefixWord ++ tailWord_3789156) baseStart_3789156 baseEnd_3789156 := by
    simpa [prefixWord, tailWord_3789156, baseEnd_3789156] using wordTrace_append hprefix tailTrace_3789156
  have hstable : (prefixWord ++ tailWord_3789156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3789156).length < 2 ^ (prefixWord ++ tailWord_3789156).sum := by decide
  have hdescent : baseEnd_3789156 < baseStart_3789156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3789156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
