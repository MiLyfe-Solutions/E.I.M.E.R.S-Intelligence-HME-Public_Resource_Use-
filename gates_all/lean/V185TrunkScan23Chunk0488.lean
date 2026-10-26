import V185TrunkScan23Chunk0487

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2886589 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2886589 : Nat := 118140960795 + 2886589 * 2 ^ 59
def prefixEnd_2886589 : Nat := 4983230072969 + 3 ^ 40 * 2886589 * 2
def baseEnd_2886589 : Nat := 1482207608981311940962325

theorem tailTrace_2886589 : CollatzResearch.WordTrace tailWord_2886589 prefixEnd_2886589 1482207608981311940962325 := by
  unfold tailWord_2886589
  simp only [CollatzResearch.WordTrace]
  refine ⟨105282550139388517997358821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70188366759592345331572547 105282550139388517997358821)
  ·
    refine ⟨19740478151135347124504779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105282550139388517997358821 19740478151135347124504779)
    ·
      refine ⟨29610717226703020686757169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19740478151135347124504779 29610717226703020686757169)
      ·
        refine ⟨22208037920027265515067877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29610717226703020686757169 22208037920027265515067877)
        ·
          refine ⟨4164007110005112284075227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22208037920027265515067877 4164007110005112284075227)
          ·
            refine ⟨6246010665007668426112841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164007110005112284075227 6246010665007668426112841)
            ·
              refine ⟨4684507998755751319584631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246010665007668426112841 4684507998755751319584631)
              ·
                refine ⟨7026761998133626979376947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684507998755751319584631 7026761998133626979376947)
                ·
                  refine ⟨10540142997200440469065421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026761998133626979376947 10540142997200440469065421)
                  ·
                    refine ⟨3952553623950165175899533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10540142997200440469065421 3952553623950165175899533)
                    ·
                      refine ⟨1482207608981311940962325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952553623950165175899533 1482207608981311940962325)
                      ·
                        rfl

theorem cell23_2886589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2886589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886589 prefixEnd_2886589 := by exact prefixLift 2886589
  have htrace : WordTrace (prefixWord ++ tailWord_2886589) baseStart_2886589 baseEnd_2886589 := by
    simpa [prefixWord, tailWord_2886589, baseEnd_2886589] using wordTrace_append hprefix tailTrace_2886589
  have hstable : (prefixWord ++ tailWord_2886589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886589).length < 2 ^ (prefixWord ++ tailWord_2886589).sum := by decide
  have hdescent : baseEnd_2886589 < baseStart_2886589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886615 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_2886615 : Nat := 118140960795 + 2886615 * 2 ^ 59
def prefixEnd_2886615 : Nat := 4983230072969 + 3 ^ 40 * 2886615 * 2
def baseEnd_2886615 : Nat := 1482220959478328839237205

theorem tailTrace_2886615 : CollatzResearch.WordTrace tailWord_2886615 prefixEnd_2886615 1482220959478328839237205 := by
  unfold tailWord_2886615
  simp only [CollatzResearch.WordTrace]
  refine ⟨105283498437294324437805299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70188998958196216291870199 105283498437294324437805299)
  ·
    refine ⟨157925247655941486656707949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105283498437294324437805299 157925247655941486656707949)
    ·
      refine ⟨59221967870978057496265481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157925247655941486656707949 59221967870978057496265481)
      ·
        refine ⟨44416475903233543122199111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59221967870978057496265481 44416475903233543122199111)
        ·
          refine ⟨66624713854850314683298667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44416475903233543122199111 66624713854850314683298667)
          ·
            refine ⟨99937070782275472024948001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66624713854850314683298667 99937070782275472024948001)
            ·
              refine ⟨74952803086706604018711001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99937070782275472024948001 74952803086706604018711001)
              ·
                refine ⟨56214602315029953014033251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74952803086706604018711001 56214602315029953014033251)
                ·
                  refine ⟨84321903472544929521049877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56214602315029953014033251 84321903472544929521049877)
                  ·
                    refine ⟨3952589225275543571299213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84321903472544929521049877 3952589225275543571299213)
                    ·
                      refine ⟨1482220959478328839237205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952589225275543571299213 1482220959478328839237205)
                      ·
                        rfl

theorem cell23_2886615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_2886615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886615 prefixEnd_2886615 := by exact prefixLift 2886615
  have htrace : WordTrace (prefixWord ++ tailWord_2886615) baseStart_2886615 baseEnd_2886615 := by
    simpa [prefixWord, tailWord_2886615, baseEnd_2886615] using wordTrace_append hprefix tailTrace_2886615
  have hstable : (prefixWord ++ tailWord_2886615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886615).length < 2 ^ (prefixWord ++ tailWord_2886615).sum := by decide
  have hdescent : baseEnd_2886615 < baseStart_2886615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886616 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 1, 3, 2]
def baseStart_2886616 : Nat := 118140960795 + 2886616 * 2 ^ 59
def prefixEnd_2886616 : Nat := 4983230072969 + 3 ^ 40 * 2886616 * 2
def baseEnd_2886616 : Nat := 1482221472958983335324701

theorem tailTrace_2886616 : CollatzResearch.WordTrace tailWord_2886616 prefixEnd_2886616 1482221472958983335324701 := by
  unfold tailWord_2886616
  simp only [CollatzResearch.WordTrace]
  refine ⟨52641767455145350804295851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70189023273527134405727801 52641767455145350804295851)
  ·
    refine ⟨78962651182718026206443777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52641767455145350804295851 78962651182718026206443777)
    ·
      refine ⟨59221988387038519654832833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78962651182718026206443777 59221988387038519654832833)
      ·
        refine ⟨44416491290278889741124625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59221988387038519654832833 44416491290278889741124625)
        ·
          refine ⟨33312368467709167305843469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44416491290278889741124625 33312368467709167305843469)
          ·
            refine ⟨12492138175390937739691301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33312368467709167305843469 12492138175390937739691301)
            ·
              refine ⟨2342275907885800826192119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12492138175390937739691301 2342275907885800826192119)
              ·
                refine ⟨3513413861828701239288179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342275907885800826192119 3513413861828701239288179)
                ·
                  refine ⟨5270120792743051858932269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513413861828701239288179 5270120792743051858932269)
                  ·
                    refine ⟨1976295297278644447099601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5270120792743051858932269 1976295297278644447099601)
                    ·
                      refine ⟨1482221472958983335324701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976295297278644447099601 1482221472958983335324701)
                      ·
                        rfl

theorem cell23_2886616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_2886616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886616 prefixEnd_2886616 := by exact prefixLift 2886616
  have htrace : WordTrace (prefixWord ++ tailWord_2886616) baseStart_2886616 baseEnd_2886616 := by
    simpa [prefixWord, tailWord_2886616, baseEnd_2886616] using wordTrace_append hprefix tailTrace_2886616
  have hstable : (prefixWord ++ tailWord_2886616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886616).length < 2 ^ (prefixWord ++ tailWord_2886616).sum := by decide
  have hdescent : baseEnd_2886616 < baseStart_2886616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886623 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 2, 1, 3]
def baseStart_2886623 : Nat := 118140960795 + 2886623 * 2 ^ 59
def prefixEnd_2886623 : Nat := 4983230072969 + 3 ^ 40 * 2886623 * 2
def baseEnd_2886623 : Nat := 1482225067323564807937169

theorem tailTrace_2886623 : CollatzResearch.WordTrace tailWord_2886623 prefixEnd_2886623 1482225067323564807937169 := by
  unfold tailWord_2886623
  simp only [CollatzResearch.WordTrace]
  refine ⟨105283790221265341804096523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70189193480843561202731015 105283790221265341804096523)
  ·
    refine ⟨157925685331898012706144785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105283790221265341804096523 157925685331898012706144785)
    ·
      refine ⟨118444263998923509529608589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157925685331898012706144785 118444263998923509529608589)
      ·
        refine ⟨44416598999596316073603221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118444263998923509529608589 44416598999596316073603221)
        ·
          refine ⟨2082028078106077315950151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44416598999596316073603221 2082028078106077315950151)
          ·
            refine ⟨3123042117159115973925227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082028078106077315950151 3123042117159115973925227)
            ·
              refine ⟨4684563175738673960887841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123042117159115973925227 4684563175738673960887841)
              ·
                refine ⟨3513422381804005470665881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4684563175738673960887841 3513422381804005470665881)
                ·
                  refine ⟨2635066786353004102999411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513422381804005470665881 2635066786353004102999411)
                  ·
                    refine ⟨3952600179529506154499117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635066786353004102999411 3952600179529506154499117)
                    ·
                      refine ⟨1482225067323564807937169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952600179529506154499117 1482225067323564807937169)
                      ·
                        rfl

theorem cell23_2886623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_2886623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886623 prefixEnd_2886623 := by exact prefixLift 2886623
  have htrace : WordTrace (prefixWord ++ tailWord_2886623) baseStart_2886623 baseEnd_2886623 := by
    simpa [prefixWord, tailWord_2886623, baseEnd_2886623] using wordTrace_append hprefix tailTrace_2886623
  have hstable : (prefixWord ++ tailWord_2886623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886623).length < 2 ^ (prefixWord ++ tailWord_2886623).sum := by decide
  have hdescent : baseEnd_2886623 < baseStart_2886623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886646 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_2886646 : Nat := 118140960795 + 2886646 * 2 ^ 59
def prefixEnd_2886646 : Nat := 4983230072969 + 3 ^ 40 * 2886646 * 2
def baseEnd_2886646 : Nat := 1482236877378618217949563

theorem tailTrace_2886646 : CollatzResearch.WordTrace tailWord_2886646 prefixEnd_2886646 1482236877378618217949563 := by
  unfold tailWord_2886646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580289318761376045761487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70189752733454677821455861 6580289318761376045761487)
  ·
    refine ⟨9870433978142064068642231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6580289318761376045761487 9870433978142064068642231)
    ·
      refine ⟨14805650967213096102963347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9870433978142064068642231 14805650967213096102963347)
      ·
        refine ⟨22208476450819644154445021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14805650967213096102963347 22208476450819644154445021)
        ·
          refine ⟨8328178669057366557916883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22208476450819644154445021 8328178669057366557916883)
          ·
            refine ⟨12492268003586049836875325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328178669057366557916883 12492268003586049836875325)
            ·
              refine ⟨4684600501344768688828247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12492268003586049836875325 4684600501344768688828247)
              ·
                refine ⟨7026900752017153033242371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684600501344768688828247 7026900752017153033242371)
                ·
                  refine ⟨10540351128025729549863557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026900752017153033242371 10540351128025729549863557)
                  ·
                    refine ⟨1976315836504824290599417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10540351128025729549863557 1976315836504824290599417)
                    ·
                      refine ⟨1482236877378618217949563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976315836504824290599417 1482236877378618217949563)
                      ·
                        rfl

theorem cell23_2886646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_2886646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886646 prefixEnd_2886646 := by exact prefixLift 2886646
  have htrace : WordTrace (prefixWord ++ tailWord_2886646) baseStart_2886646 baseEnd_2886646 := by
    simpa [prefixWord, tailWord_2886646, baseEnd_2886646] using wordTrace_append hprefix tailTrace_2886646
  have hstable : (prefixWord ++ tailWord_2886646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886646).length < 2 ^ (prefixWord ++ tailWord_2886646).sum := by decide
  have hdescent : baseEnd_2886646 < baseStart_2886646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886665 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 6, 5]
def baseStart_2886665 : Nat := 118140960795 + 2886665 * 2 ^ 59
def prefixEnd_2886665 : Nat := 4983230072969 + 3 ^ 40 * 2886665 * 2
def baseEnd_2886665 : Nat := 494082211170351214537325

theorem tailTrace_2886665 : CollatzResearch.WordTrace tailWord_2886665 prefixEnd_2886665 494082211170351214537325 := by
  unfold tailWord_2886665
  simp only [CollatzResearch.WordTrace]
  refine ⟨105285322087113182977125449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70190214724742121984750299 105285322087113182977125449)
  ·
    refine ⟨78963991565334887232844087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105285322087113182977125449 78963991565334887232844087)
    ·
      refine ⟨118445987348002330849266131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78963991565334887232844087 118445987348002330849266131)
      ·
        refine ⟨177668981022003496273899197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118445987348002330849266131 177668981022003496273899197)
        ·
          refine ⟨66625867883251311102712199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177668981022003496273899197 66625867883251311102712199)
          ·
            refine ⟨99938801824876966654068299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66625867883251311102712199 99938801824876966654068299)
            ·
              refine ⟨149908202737315449981102449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99938801824876966654068299 149908202737315449981102449)
              ·
                refine ⟨112431152052986587485826837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149908202737315449981102449 112431152052986587485826837)
                ·
                  refine ⟨5270210252483746288398133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112431152052986587485826837 5270210252483746288398133)
                  ·
                    refine ⟨494082211170351214537325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5270210252483746288398133 494082211170351214537325)
                    ·
                      rfl

theorem cell23_2886665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 5].length) (baseStart_2886665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886665 prefixEnd_2886665 := by exact prefixLift 2886665
  have htrace : WordTrace (prefixWord ++ tailWord_2886665) baseStart_2886665 baseEnd_2886665 := by
    simpa [prefixWord, tailWord_2886665, baseEnd_2886665] using wordTrace_append hprefix tailTrace_2886665
  have hstable : (prefixWord ++ tailWord_2886665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886665).length < 2 ^ (prefixWord ++ tailWord_2886665).sum := by decide
  have hdescent : baseEnd_2886665 < baseStart_2886665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886675 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5]
def baseStart_2886675 : Nat := 118140960795 + 2886675 * 2 ^ 59
def prefixEnd_2886675 : Nat := 4983230072969 + 3 ^ 40 * 2886675 * 2
def baseEnd_2886675 : Nat := 1482251768317598604486929

theorem tailTrace_2886675 : CollatzResearch.WordTrace tailWord_2886675 prefixEnd_2886675 1482251768317598604486929 := by
  unfold tailWord_2886675
  simp only [CollatzResearch.WordTrace]
  refine ⟨105285686817076954684989479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70190457878051303123326319 105285686817076954684989479)
  ·
    refine ⟨157928530225615432027484219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105285686817076954684989479 157928530225615432027484219)
    ·
      refine ⟨236892795338423148041226329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157928530225615432027484219 236892795338423148041226329)
      ·
        refine ⟨177669596503817361030919747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236892795338423148041226329 177669596503817361030919747)
        ·
          refine ⟨266504394755726041546379621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177669596503817361030919747 266504394755726041546379621)
          ·
            refine ⟨49969574016698632789946179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266504394755726041546379621 49969574016698632789946179)
            ·
              refine ⟨74954361025047949184919269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49969574016698632789946179 74954361025047949184919269)
              ·
                refine ⟨14053942692196490472172363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74954361025047949184919269 14053942692196490472172363)
                ·
                  refine ⟨21080914038294735708258545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14053942692196490472172363 21080914038294735708258545)
                  ·
                    refine ⟨15810685528721051781193909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21080914038294735708258545 15810685528721051781193909)
                    ·
                      refine ⟨1482251768317598604486929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15810685528721051781193909 1482251768317598604486929)
                      ·
                        rfl

theorem cell23_2886675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_2886675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886675 prefixEnd_2886675 := by exact prefixLift 2886675
  have htrace : WordTrace (prefixWord ++ tailWord_2886675) baseStart_2886675 baseEnd_2886675 := by
    simpa [prefixWord, tailWord_2886675, baseEnd_2886675] using wordTrace_append hprefix tailTrace_2886675
  have hstable : (prefixWord ++ tailWord_2886675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886675).length < 2 ^ (prefixWord ++ tailWord_2886675).sum := by decide
  have hdescent : baseEnd_2886675 < baseStart_2886675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886682 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_2886682 : Nat := 118140960795 + 2886682 * 2 ^ 59
def prefixEnd_2886682 : Nat := 4983230072969 + 3 ^ 40 * 2886682 * 2
def baseEnd_2886682 : Nat := 494085120894060025699799

theorem tailTrace_2886682 : CollatzResearch.WordTrace tailWord_2886682 prefixEnd_2886682 494085120894060025699799 := by
  unfold tailWord_2886682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26321485532012898720123575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70190628085367729920329533 26321485532012898720123575)
  ·
    refine ⟨39482228298019348080185363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26321485532012898720123575 39482228298019348080185363)
    ·
      refine ⟨59223342447029022120278045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39482228298019348080185363 59223342447029022120278045)
      ·
        refine ⟨22208753417635883295104267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59223342447029022120278045 22208753417635883295104267)
        ·
          refine ⟨33313130126453824942656401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22208753417635883295104267 33313130126453824942656401)
          ·
            refine ⟨24984847594840368706992301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33313130126453824942656401 24984847594840368706992301)
            ·
              refine ⟨9369317848065138265122113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24984847594840368706992301 9369317848065138265122113)
              ·
                refine ⟨7026988386048853698841585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9369317848065138265122113 7026988386048853698841585)
                ·
                  refine ⟨5270241289536640274131189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7026988386048853698841585 5270241289536640274131189)
                  ·
                    refine ⟨494085120894060025699799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5270241289536640274131189 494085120894060025699799)
                    ·
                      rfl

theorem cell23_2886682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_2886682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886682 prefixEnd_2886682 := by exact prefixLift 2886682
  have htrace : WordTrace (prefixWord ++ tailWord_2886682) baseStart_2886682 baseEnd_2886682 := by
    simpa [prefixWord, tailWord_2886682, baseEnd_2886682] using wordTrace_append hprefix tailTrace_2886682
  have hstable : (prefixWord ++ tailWord_2886682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886682).length < 2 ^ (prefixWord ++ tailWord_2886682).sum := by decide
  have hdescent : baseEnd_2886682 < baseStart_2886682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886692 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2886692 : Nat := 118140960795 + 2886692 * 2 ^ 59
def prefixEnd_2886692 : Nat := 4983230072969 + 3 ^ 40 * 2886692 * 2
def baseEnd_2886692 : Nat := 1482260497488725037974351

theorem tailTrace_2886692 : CollatzResearch.WordTrace tailWord_2886692 prefixEnd_2886692 1482260497488725037974351 := by
  unfold tailWord_2886692
  simp only [CollatzResearch.WordTrace]
  refine ⟨52643153429007683294179165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70190871238676911058905553 52643153429007683294179165)
  ·
    refine ⟨19741182535877881235317187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52643153429007683294179165 19741182535877881235317187)
    ·
      refine ⟨29611773803816821852975781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19741182535877881235317187 29611773803816821852975781)
      ·
        refine ⟨5552207588215654097432959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29611773803816821852975781 5552207588215654097432959)
        ·
          refine ⟨8328311382323481146149439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552207588215654097432959 8328311382323481146149439)
          ·
            refine ⟨12492467073485221719224159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328311382323481146149439 12492467073485221719224159)
            ·
              refine ⟨18738700610227832578836239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12492467073485221719224159 18738700610227832578836239)
              ·
                refine ⟨28108050915341748868254359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18738700610227832578836239 28108050915341748868254359)
                ·
                  refine ⟨42162076373012623302381539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28108050915341748868254359 42162076373012623302381539)
                  ·
                    refine ⟨63243114559518934953572309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42162076373012623302381539 63243114559518934953572309)
                    ·
                      refine ⟨1482260497488725037974351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63243114559518934953572309 1482260497488725037974351)
                      ·
                        rfl

theorem cell23_2886692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2886692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886692 prefixEnd_2886692 := by exact prefixLift 2886692
  have htrace : WordTrace (prefixWord ++ tailWord_2886692) baseStart_2886692 baseEnd_2886692 := by
    simpa [prefixWord, tailWord_2886692, baseEnd_2886692] using wordTrace_append hprefix tailTrace_2886692
  have hstable : (prefixWord ++ tailWord_2886692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886692).length < 2 ^ (prefixWord ++ tailWord_2886692).sum := by decide
  have hdescent : baseEnd_2886692 < baseStart_2886692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886725 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 10]
def baseStart_2886725 : Nat := 118140960795 + 2886725 * 2 ^ 59
def prefixEnd_2886725 : Nat := 4983230072969 + 3 ^ 40 * 2886725 * 2
def baseEnd_2886725 : Nat := 164697493594480378762411

theorem tailTrace_2886725 : CollatzResearch.WordTrace tailWord_2886725 prefixEnd_2886725 164697493594480378762411 := by
  unfold tailWord_2886725
  simp only [CollatzResearch.WordTrace]
  refine ⟨105287510466895813224309629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70191673644597208816206419 105287510466895813224309629)
  ·
    refine ⟨39482816425085929959116111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105287510466895813224309629 39482816425085929959116111)
    ·
      refine ⟨59224224637628894938674167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39482816425085929959116111 59224224637628894938674167)
      ·
        refine ⟨88836336956443342408011251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59224224637628894938674167 88836336956443342408011251)
        ·
          refine ⟨133254505434665013612016877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88836336956443342408011251 133254505434665013612016877)
          ·
            refine ⟨49970439537999380104506329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133254505434665013612016877 49970439537999380104506329)
            ·
              refine ⟨37477829653499535078379747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49970439537999380104506329 37477829653499535078379747)
              ·
                refine ⟨56216744480249302617569621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37477829653499535078379747 56216744480249302617569621)
                ·
                  refine ⟨164697493594480378762411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56216744480249302617569621 164697493594480378762411)
                  ·
                    rfl

theorem cell23_2886725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_2886725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886725 prefixEnd_2886725 := by exact prefixLift 2886725
  have htrace : WordTrace (prefixWord ++ tailWord_2886725) baseStart_2886725 baseEnd_2886725 := by
    simpa [prefixWord, tailWord_2886725, baseEnd_2886725] using wordTrace_append hprefix tailTrace_2886725
  have hstable : (prefixWord ++ tailWord_2886725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886725).length < 2 ^ (prefixWord ++ tailWord_2886725).sum := by decide
  have hdescent : baseEnd_2886725 < baseStart_2886725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886819 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 2, 4]
def baseStart_2886819 : Nat := 118140960795 + 2886819 * 2 ^ 59
def prefixEnd_2886819 : Nat := 4983230072969 + 3 ^ 40 * 2886819 * 2
def baseEnd_2886819 : Nat := 494108569843948680362089

theorem tailTrace_2886819 : CollatzResearch.WordTrace tailWord_2886819 prefixEnd_2886819 494108569843948680362089 := by
  unfold tailWord_2886819
  simp only [CollatzResearch.WordTrace]
  refine ⟨105290938928555267278231511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70193959285703511518821007 105290938928555267278231511)
  ·
    refine ⟨157936408392832900917347267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105290938928555267278231511 157936408392832900917347267)
    ·
      refine ⟨236904612589249351376020901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157936408392832900917347267 236904612589249351376020901)
      ·
        refine ⟨44419614860484253383003919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236904612589249351376020901 44419614860484253383003919)
        ·
          refine ⟨66629422290726380074505879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44419614860484253383003919 66629422290726380074505879)
          ·
            refine ⟨99944133436089570111758819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66629422290726380074505879 99944133436089570111758819)
            ·
              refine ⟨149916200154134355167638229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99944133436089570111758819 149916200154134355167638229)
              ·
                refine ⟨3513660941112523949241521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149916200154134355167638229 3513660941112523949241521)
                ·
                  refine ⟨2635245705834392961931141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513660941112523949241521 2635245705834392961931141)
                  ·
                    refine ⟨494108569843948680362089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635245705834392961931141 494108569843948680362089)
                    ·
                      rfl

theorem cell23_2886819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 4].length) (baseStart_2886819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886819 prefixEnd_2886819 := by exact prefixLift 2886819
  have htrace : WordTrace (prefixWord ++ tailWord_2886819) baseStart_2886819 baseEnd_2886819 := by
    simpa [prefixWord, tailWord_2886819, baseEnd_2886819] using wordTrace_append hprefix tailTrace_2886819
  have hstable : (prefixWord ++ tailWord_2886819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886819).length < 2 ^ (prefixWord ++ tailWord_2886819).sum := by decide
  have hdescent : baseEnd_2886819 < baseStart_2886819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886843 : List Nat := [1, 1, 1, 1, 1, 2, 4, 7, 1, 2, 2]
def baseStart_2886843 : Nat := 118140960795 + 2886843 * 2 ^ 59
def prefixEnd_2886843 : Nat := 4983230072969 + 3 ^ 40 * 2886843 * 2
def baseEnd_2886843 : Nat := 1482338033067553947186157

theorem tailTrace_2886843 : CollatzResearch.WordTrace tailWord_2886843 prefixEnd_2886843 1482338033067553947186157 := by
  unfold tailWord_2886843
  simp only [CollatzResearch.WordTrace]
  refine ⟨105291814280468319377105183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70194542853645546251403455 105291814280468319377105183)
  ·
    refine ⟨157937721420702479065657775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105291814280468319377105183 157937721420702479065657775)
    ·
      refine ⟨236906582131053718598486663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157937721420702479065657775 236906582131053718598486663)
      ·
        refine ⟨355359873196580577897729995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236906582131053718598486663 355359873196580577897729995)
        ·
          refine ⟨533039809794870866846594993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355359873196580577897729995 533039809794870866846594993)
          ·
            refine ⟨399779857346153150134946245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533039809794870866846594993 399779857346153150134946245)
            ·
              refine ⟨74958723252403715650302421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399779857346153150134946245 74958723252403715650302421)
              ·
                refine ⟨1756845076228212085553963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74958723252403715650302421 1756845076228212085553963)
                ·
                  refine ⟨2635267614342318128330945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756845076228212085553963 2635267614342318128330945)
                  ·
                    refine ⟨1976450710756738596248209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2635267614342318128330945 1976450710756738596248209)
                    ·
                      refine ⟨1482338033067553947186157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976450710756738596248209 1482338033067553947186157)
                      ·
                        rfl

theorem cell23_2886843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 7, 1, 2, 2].length) (baseStart_2886843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886843 prefixEnd_2886843 := by exact prefixLift 2886843
  have htrace : WordTrace (prefixWord ++ tailWord_2886843) baseStart_2886843 baseEnd_2886843 := by
    simpa [prefixWord, tailWord_2886843, baseEnd_2886843] using wordTrace_append hprefix tailTrace_2886843
  have hstable : (prefixWord ++ tailWord_2886843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886843).length < 2 ^ (prefixWord ++ tailWord_2886843).sum := by decide
  have hdescent : baseEnd_2886843 < baseStart_2886843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886846 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2886846 : Nat := 118140960795 + 2886846 * 2 ^ 59
def prefixEnd_2886846 : Nat := 4983230072969 + 3 ^ 40 * 2886846 * 2
def baseEnd_2886846 : Nat := 1482339573509517435448643

theorem tailTrace_2886846 : CollatzResearch.WordTrace tailWord_2886846 prefixEnd_2886846 1482339573509517435448643 := by
  unfold tailWord_2886846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13161490462432181361183049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70194615799638300592976261 13161490462432181361183049)
  ·
    refine ⟨9871117846824136020887287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13161490462432181361183049 9871117846824136020887287)
    ·
      refine ⟨14806676770236204031330931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871117846824136020887287 14806676770236204031330931)
      ·
        refine ⟨22210015155354306046996397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14806676770236204031330931 22210015155354306046996397)
        ·
          refine ⟨8328755683257864767623649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22210015155354306046996397 8328755683257864767623649)
          ·
            refine ⟨6246566762443398575717737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328755683257864767623649 6246566762443398575717737)
            ·
              refine ⟨4684925071832548931788303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246566762443398575717737 4684925071832548931788303)
              ·
                refine ⟨7027387607748823397682455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684925071832548931788303 7027387607748823397682455)
                ·
                  refine ⟨10541081411623235096523683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7027387607748823397682455 10541081411623235096523683)
                  ·
                    refine ⟨15811622117434852644785525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10541081411623235096523683 15811622117434852644785525)
                    ·
                      refine ⟨1482339573509517435448643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15811622117434852644785525 1482339573509517435448643)
                      ·
                        rfl

theorem cell23_2886846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2886846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886846 prefixEnd_2886846 := by exact prefixLift 2886846
  have htrace : WordTrace (prefixWord ++ tailWord_2886846) baseStart_2886846 baseEnd_2886846 := by
    simpa [prefixWord, tailWord_2886846, baseEnd_2886846] using wordTrace_append hprefix tailTrace_2886846
  have hstable : (prefixWord ++ tailWord_2886846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886846).length < 2 ^ (prefixWord ++ tailWord_2886846).sum := by decide
  have hdescent : baseEnd_2886846 < baseStart_2886846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886849 : List Nat := [1, 2, 6, 1, 1, 1, 11]
def baseStart_2886849 : Nat := 118140960795 + 2886849 * 2 ^ 59
def prefixEnd_2886849 : Nat := 4983230072969 + 3 ^ 40 * 2886849 * 2
def baseEnd_2886849 : Nat := 18300507579647912638409

theorem tailTrace_2886849 : CollatzResearch.WordTrace tailWord_2886849 prefixEnd_2886849 18300507579647912638409 := by
  unfold tailWord_2886849
  simp only [CollatzResearch.WordTrace]
  refine ⟨105292033118446582401823601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70194688745631054934549067 105292033118446582401823601)
  ·
    refine ⟨78969024838834936801367701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105292033118446582401823601 78969024838834936801367701)
    ·
      refine ⟨3701673039320387662564111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78969024838834936801367701 3701673039320387662564111)
      ·
        refine ⟨5552509558980581493846167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701673039320387662564111 5552509558980581493846167)
        ·
          refine ⟨8328764338470872240769251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552509558980581493846167 8328764338470872240769251)
          ·
            refine ⟨12493146507706308361153877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328764338470872240769251 12493146507706308361153877)
            ·
              refine ⟨18300507579647912638409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12493146507706308361153877 18300507579647912638409)
              ·
                rfl

theorem cell23_2886849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 11].length) (baseStart_2886849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886849 prefixEnd_2886849 := by exact prefixLift 2886849
  have htrace : WordTrace (prefixWord ++ tailWord_2886849) baseStart_2886849 baseEnd_2886849 := by
    simpa [prefixWord, tailWord_2886849, baseEnd_2886849] using wordTrace_append hprefix tailTrace_2886849
  have hstable : (prefixWord ++ tailWord_2886849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886849).length < 2 ^ (prefixWord ++ tailWord_2886849).sum := by decide
  have hdescent : baseEnd_2886849 < baseStart_2886849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886854 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2886854 : Nat := 118140960795 + 2886854 * 2 ^ 59
def prefixEnd_2886854 : Nat := 4983230072969 + 3 ^ 40 * 2886854 * 2
def baseEnd_2886854 : Nat := 1482343681354753404148607

theorem tailTrace_2886854 : CollatzResearch.WordTrace tailWord_2886854 prefixEnd_2886854 1482343681354753404148607 := by
  unfold tailWord_2886854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3290381733857139632992363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70194810322285645503837077 3290381733857139632992363)
  ·
    refine ⟨4935572600785709449488545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3290381733857139632992363 4935572600785709449488545)
    ·
      refine ⟨3701679450589282087116409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4935572600785709449488545 3701679450589282087116409)
      ·
        refine ⟨2776259587941961565337307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3701679450589282087116409 2776259587941961565337307)
        ·
          refine ⟨4164389381912942348005961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776259587941961565337307 4164389381912942348005961)
          ·
            refine ⟨3123292036434706761004471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4164389381912942348005961 3123292036434706761004471)
            ·
              refine ⟨4684938054652060141506707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123292036434706761004471 4684938054652060141506707)
              ·
                refine ⟨7027407081978090212260061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684938054652060141506707 7027407081978090212260061)
                ·
                  refine ⟨2635277655741783829597523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7027407081978090212260061 2635277655741783829597523)
                  ·
                    refine ⟨3952916483612675744396285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635277655741783829597523 3952916483612675744396285)
                    ·
                      refine ⟨1482343681354753404148607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952916483612675744396285 1482343681354753404148607)
                      ·
                        rfl

theorem cell23_2886854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2886854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886854 prefixEnd_2886854 := by exact prefixLift 2886854
  have htrace : WordTrace (prefixWord ++ tailWord_2886854) baseStart_2886854 baseEnd_2886854 := by
    simpa [prefixWord, tailWord_2886854, baseEnd_2886854] using wordTrace_append hprefix tailTrace_2886854
  have hstable : (prefixWord ++ tailWord_2886854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886854).length < 2 ^ (prefixWord ++ tailWord_2886854).sum := by decide
  have hdescent : baseEnd_2886854 < baseStart_2886854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886870 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2886870 : Nat := 118140960795 + 2886870 * 2 ^ 59
def prefixEnd_2886870 : Nat := 4983230072969 + 3 ^ 40 * 2886870 * 2
def baseEnd_2886870 : Nat := 494117299015075113849511

theorem tailTrace_2886870 : CollatzResearch.WordTrace tailWord_2886870 prefixEnd_2886870 494117299015075113849511 := by
  unfold tailWord_2886870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580799940710656436771129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70195199367580335325558709 6580799940710656436771129)
  ·
    refine ⟨4935599955532992327578347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6580799940710656436771129 4935599955532992327578347)
    ·
      refine ⟨7403399933299488491367521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935599955532992327578347 7403399933299488491367521)
      ·
        refine ⟨5552549949974616368525641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7403399933299488491367521 5552549949974616368525641)
        ·
          refine ⟨4164412462480962276394231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5552549949974616368525641 4164412462480962276394231)
          ·
            refine ⟨6246618693721443414591347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164412462480962276394231 6246618693721443414591347)
            ·
              refine ⟨9369928040582165121887021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246618693721443414591347 9369928040582165121887021)
              ·
                refine ⟨3513723015218311920707633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9369928040582165121887021 3513723015218311920707633)
                ·
                  refine ⟨2635292261413733940530725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513723015218311920707633 2635292261413733940530725)
                  ·
                    refine ⟨494117299015075113849511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635292261413733940530725 494117299015075113849511)
                    ·
                      rfl

theorem cell23_2886870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2886870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886870 prefixEnd_2886870 := by exact prefixLift 2886870
  have htrace : WordTrace (prefixWord ++ tailWord_2886870) baseStart_2886870 baseEnd_2886870 := by
    simpa [prefixWord, tailWord_2886870, baseEnd_2886870] using wordTrace_append hprefix tailTrace_2886870
  have hstable : (prefixWord ++ tailWord_2886870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886870).length < 2 ^ (prefixWord ++ tailWord_2886870).sum := by decide
  have hdescent : baseEnd_2886870 < baseStart_2886870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886910 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2886910 : Nat := 118140960795 + 2886910 * 2 ^ 59
def prefixEnd_2886910 : Nat := 4983230072969 + 3 ^ 40 * 2886910 * 2
def baseEnd_2886910 : Nat := 1482372436271405185048349

theorem tailTrace_2886910 : CollatzResearch.WordTrace tailWord_2886910 prefixEnd_2886910 1482372436271405185048349 := by
  unfold tailWord_2886910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13161782246403198727474273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70196171980817059879862789 13161782246403198727474273)
  ·
    refine ⟨9871336684802399045605705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13161782246403198727474273 9871336684802399045605705)
    ·
      refine ⟨7403502513601799284204279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9871336684802399045605705 7403502513601799284204279)
      ·
        refine ⟨11105253770402698926306419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403502513601799284204279 11105253770402698926306419)
        ·
          refine ⟨16657880655604048389459629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105253770402698926306419 16657880655604048389459629)
          ·
            refine ⟨6246705245851518146047361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16657880655604048389459629 6246705245851518146047361)
            ·
              refine ⟨4685028934388638609535521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246705245851518146047361 4685028934388638609535521)
              ·
                refine ⟨3513771700791478957151641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685028934388638609535521 3513771700791478957151641)
                ·
                  refine ⟨2635328775593609217863731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513771700791478957151641 2635328775593609217863731)
                  ·
                    refine ⟨3952993163390413826795597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635328775593609217863731 3952993163390413826795597)
                    ·
                      refine ⟨1482372436271405185048349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3952993163390413826795597 1482372436271405185048349)
                      ·
                        rfl

theorem cell23_2886910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2886910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886910 prefixEnd_2886910 := by exact prefixLift 2886910
  have htrace : WordTrace (prefixWord ++ tailWord_2886910) baseStart_2886910 baseEnd_2886910 := by
    simpa [prefixWord, tailWord_2886910, baseEnd_2886910] using wordTrace_append hprefix tailTrace_2886910
  have hstable : (prefixWord ++ tailWord_2886910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886910).length < 2 ^ (prefixWord ++ tailWord_2886910).sum := by decide
  have hdescent : baseEnd_2886910 < baseStart_2886910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886912 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_2886912 : Nat := 118140960795 + 2886912 * 2 ^ 59
def prefixEnd_2886912 : Nat := 4983230072969 + 3 ^ 40 * 2886912 * 2
def baseEnd_2886912 : Nat := 1482373463232714177223339

theorem tailTrace_2886912 : CollatzResearch.WordTrace tailWord_2886912 prefixEnd_2886912 1482373463232714177223339 := by
  unfold tailWord_2886912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52647165458609172080683495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70196220611478896107577993 52647165458609172080683495)
  ·
    refine ⟨78970748187913758121025243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52647165458609172080683495 78970748187913758121025243)
    ·
      refine ⟨118456122281870637181537865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78970748187913758121025243 118456122281870637181537865)
      ·
        refine ⟨88842091711402977886153399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118456122281870637181537865 88842091711402977886153399)
        ·
          refine ⟨133263137567104466829230099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88842091711402977886153399 133263137567104466829230099)
          ·
            refine ⟨199894706350656700243845149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133263137567104466829230099 199894706350656700243845149)
            ·
              refine ⟨74960514881496262591441931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199894706350656700243845149 74960514881496262591441931)
              ·
                refine ⟨112440772322244393887162897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74960514881496262591441931 112440772322244393887162897)
                ·
                  refine ⟨84330579241683295415372173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112440772322244393887162897 84330579241683295415372173)
                  ·
                    refine ⟨31623967215631235780764565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84330579241683295415372173 31623967215631235780764565)
                    ·
                      refine ⟨1482373463232714177223339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31623967215631235780764565 1482373463232714177223339)
                      ·
                        rfl

theorem cell23_2886912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_2886912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886912 prefixEnd_2886912 := by exact prefixLift 2886912
  have htrace : WordTrace (prefixWord ++ tailWord_2886912) baseStart_2886912 baseEnd_2886912 := by
    simpa [prefixWord, tailWord_2886912, baseEnd_2886912] using wordTrace_append hprefix tailTrace_2886912
  have hstable : (prefixWord ++ tailWord_2886912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886912).length < 2 ^ (prefixWord ++ tailWord_2886912).sum := by decide
  have hdescent : baseEnd_2886912 < baseStart_2886912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886929 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2886929 : Nat := 118140960795 + 2886929 * 2 ^ 59
def prefixEnd_2886929 : Nat := 4983230072969 + 3 ^ 40 * 2886929 * 2
def baseEnd_2886929 : Nat := 1482382192403840610710761

theorem tailTrace_2886929 : CollatzResearch.WordTrace tailWord_2886929 prefixEnd_2886929 1482382192403840610710761 := by
  unfold tailWord_2886929
  simp only [CollatzResearch.WordTrace]
  refine ⟨105294950958156756064735841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70196633972104504043157227 105294950958156756064735841)
  ·
    refine ⟨78971213218617567048551881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105294950958156756064735841 78971213218617567048551881)
    ·
      refine ⟨59228409913963175286413911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78971213218617567048551881 59228409913963175286413911)
      ·
        refine ⟨88842614870944762929620867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59228409913963175286413911 88842614870944762929620867)
        ·
          refine ⟨133263922306417144394431301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88842614870944762929620867 133263922306417144394431301)
          ·
            refine ⟨24986985432453214573955869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133263922306417144394431301 24986985432453214573955869)
            ·
              refine ⟨9370119537169955465233451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24986985432453214573955869 9370119537169955465233451)
              ·
                refine ⟨14055179305754933197850177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9370119537169955465233451 14055179305754933197850177)
                ·
                  refine ⟨10541384479316199898387633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14055179305754933197850177 10541384479316199898387633)
                  ·
                    refine ⟨7906038359487149923790725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10541384479316199898387633 7906038359487149923790725)
                    ·
                      refine ⟨1482382192403840610710761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7906038359487149923790725 1482382192403840610710761)
                      ·
                        rfl

theorem cell23_2886929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2886929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886929 prefixEnd_2886929 := by exact prefixLift 2886929
  have htrace : WordTrace (prefixWord ++ tailWord_2886929) baseStart_2886929 baseEnd_2886929 := by
    simpa [prefixWord, tailWord_2886929, baseEnd_2886929] using wordTrace_append hprefix tailTrace_2886929
  have hstable : (prefixWord ++ tailWord_2886929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886929).length < 2 ^ (prefixWord ++ tailWord_2886929).sum := by decide
  have hdescent : baseEnd_2886929 < baseStart_2886929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886973 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 7]
def baseStart_2886973 : Nat := 118140960795 + 2886973 * 2 ^ 59
def prefixEnd_2886973 : Nat := 4983230072969 + 3 ^ 40 * 2886973 * 2
def baseEnd_2886973 : Nat := 164711642839182048728951

theorem tailTrace_2886973 : CollatzResearch.WordTrace tailWord_2886973 prefixEnd_2886973 164711642839182048728951 := by
  unfold tailWord_2886973
  simp only [CollatzResearch.WordTrace]
  refine ⟨105296555769997351579337573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70197703846664901052891715 105296555769997351579337573)
  ·
    refine ⟨19743104206874503421125795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105296555769997351579337573 19743104206874503421125795)
    ·
      refine ⟨29614656310311755131688693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19743104206874503421125795 29614656310311755131688693)
      ·
        refine ⟨2776374029091727043595815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29614656310311755131688693 2776374029091727043595815)
        ·
          refine ⟨4164561043637590565393723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776374029091727043595815 4164561043637590565393723)
          ·
            refine ⟨6246841565456385848090585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164561043637590565393723 6246841565456385848090585)
            ·
              refine ⟨4685131174092289386067939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246841565456385848090585 4685131174092289386067939)
              ·
                refine ⟨7027696761138434079101909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685131174092289386067939 7027696761138434079101909)
                ·
                  refine ⟨164711642839182048728951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7027696761138434079101909 164711642839182048728951)
                  ·
                    rfl

theorem cell23_2886973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_2886973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2886973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2886973 prefixEnd_2886973 := by exact prefixLift 2886973
  have htrace : WordTrace (prefixWord ++ tailWord_2886973) baseStart_2886973 baseEnd_2886973 := by
    simpa [prefixWord, tailWord_2886973, baseEnd_2886973] using wordTrace_append hprefix tailTrace_2886973
  have hstable : (prefixWord ++ tailWord_2886973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886973).length < 2 ^ (prefixWord ++ tailWord_2886973).sum := by decide
  have hdescent : baseEnd_2886973 < baseStart_2886973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887033 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 1, 4]
def baseStart_2887033 : Nat := 118140960795 + 2887033 * 2 ^ 59
def prefixEnd_2887033 : Nat := 4983230072969 + 3 ^ 40 * 2887033 * 2
def baseEnd_2887033 : Nat := 494145198130636067936761

theorem tailTrace_2887033 : CollatzResearch.WordTrace tailWord_2887033 prefixEnd_2887033 494145198130636067936761 := by
  unfold tailWord_2887033
  simp only [CollatzResearch.WordTrace]
  refine ⟨105298744149779981826521753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70199162766519987884347835 105298744149779981826521753)
  ·
    refine ⟨78974058112334986369891315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105298744149779981826521753 78974058112334986369891315)
    ·
      refine ⟨118461087168502479554836973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78974058112334986369891315 118461087168502479554836973)
      ·
        refine ⟨44422907688188429833063865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118461087168502479554836973 44422907688188429833063865)
        ·
          refine ⟨33317180766141322374797899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44422907688188429833063865 33317180766141322374797899)
          ·
            refine ⟨49975771149211983562196849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33317180766141322374797899 49975771149211983562196849)
            ·
              refine ⟨37481828361908987671647637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49975771149211983562196849 37481828361908987671647637)
              ·
                refine ⟨1756960704464483797108483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37481828361908987671647637 1756960704464483797108483)
                ·
                  refine ⟨2635441056696725695662725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756960704464483797108483 2635441056696725695662725)
                  ·
                    refine ⟨494145198130636067936761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635441056696725695662725 494145198130636067936761)
                    ·
                      rfl

theorem cell23_2887033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 4].length) (baseStart_2887033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887033 prefixEnd_2887033 := by exact prefixLift 2887033
  have htrace : WordTrace (prefixWord ++ tailWord_2887033) baseStart_2887033 baseEnd_2887033 := by
    simpa [prefixWord, tailWord_2887033, baseEnd_2887033] using wordTrace_append hprefix tailTrace_2887033
  have hstable : (prefixWord ++ tailWord_2887033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887033).length < 2 ^ (prefixWord ++ tailWord_2887033).sum := by decide
  have hdescent : baseEnd_2887033 < baseStart_2887033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887060 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2887060 : Nat := 118140960795 + 2887060 * 2 ^ 59
def prefixEnd_2887060 : Nat := 4983230072969 + 3 ^ 40 * 2887060 * 2
def baseEnd_2887060 : Nat := 1482449458369579598172659

theorem tailTrace_2887060 : CollatzResearch.WordTrace tailWord_2887060 prefixEnd_2887060 1482449458369579598172659 := by
  unfold tailWord_2887060
  simp only [CollatzResearch.WordTrace]
  refine ⟨52649864460341082718877317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70199819280454776958503089 52649864460341082718877317)
  ·
    refine ⟨9871849586313953009789497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52649864460341082718877317 9871849586313953009789497)
    ·
      refine ⟨7403887189735464757342123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9871849586313953009789497 7403887189735464757342123)
      ·
        refine ⟨11105830784603197136013185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403887189735464757342123 11105830784603197136013185)
        ·
          refine ⟨8329373088452397852009889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11105830784603197136013185 8329373088452397852009889)
          ·
            refine ⟨6247029816339298389007417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8329373088452397852009889 6247029816339298389007417)
            ·
              refine ⟨4685272362254473791755563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247029816339298389007417 4685272362254473791755563)
              ·
                refine ⟨7027908543381710687633345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685272362254473791755563 7027908543381710687633345)
                ·
                  refine ⟨5270931407536283015725009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7027908543381710687633345 5270931407536283015725009)
                  ·
                    refine ⟨3953198555652212261793757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5270931407536283015725009 3953198555652212261793757)
                    ·
                      refine ⟨1482449458369579598172659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953198555652212261793757 1482449458369579598172659)
                      ·
                        rfl

theorem cell23_2887060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2887060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887060 prefixEnd_2887060 := by exact prefixLift 2887060
  have htrace : WordTrace (prefixWord ++ tailWord_2887060) baseStart_2887060 baseEnd_2887060 := by
    simpa [prefixWord, tailWord_2887060, baseEnd_2887060] using wordTrace_append hprefix tailTrace_2887060
  have hstable : (prefixWord ++ tailWord_2887060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887060).length < 2 ^ (prefixWord ++ tailWord_2887060).sum := by decide
  have hdescent : baseEnd_2887060 < baseStart_2887060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887080 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 6]
def baseStart_2887080 : Nat := 118140960795 + 2887080 * 2 ^ 59
def prefixEnd_2887080 : Nat := 4983230072969 + 3 ^ 40 * 2887080 * 2
def baseEnd_2887080 : Nat := 164717747553629946658063

theorem tailTrace_2887080 : CollatzResearch.WordTrace tailWord_2887080 prefixEnd_2887080 164717747553629946658063 := by
  unfold tailWord_2887080
  simp only [CollatzResearch.WordTrace]
  refine ⟨52650229190304854426741347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70200305587073139235655129 52650229190304854426741347)
  ·
    refine ⟨78975343785457281640112021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52650229190304854426741347 78975343785457281640112021)
    ·
      refine ⟨3701969239943310076880251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78975343785457281640112021 3701969239943310076880251)
      ·
        refine ⟨5552953859914965115320377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701969239943310076880251 5552953859914965115320377)
        ·
          refine ⟨4164715394936223836490283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5552953859914965115320377 4164715394936223836490283)
          ·
            refine ⟨6247073092404335754735425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164715394936223836490283 6247073092404335754735425)
            ·
              refine ⟨4685304819303251816051569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247073092404335754735425 4685304819303251816051569)
              ·
                refine ⟨3513978614477438862038677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685304819303251816051569 3513978614477438862038677)
                ·
                  refine ⟨164717747553629946658063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3513978614477438862038677 164717747553629946658063)
                  ·
                    rfl

theorem cell23_2887080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 6].length) (baseStart_2887080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887080 prefixEnd_2887080 := by exact prefixLift 2887080
  have htrace : WordTrace (prefixWord ++ tailWord_2887080) baseStart_2887080 baseEnd_2887080 := by
    simpa [prefixWord, tailWord_2887080, baseEnd_2887080] using wordTrace_append hprefix tailTrace_2887080
  have hstable : (prefixWord ++ tailWord_2887080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887080).length < 2 ^ (prefixWord ++ tailWord_2887080).sum := by decide
  have hdescent : baseEnd_2887080 < baseStart_2887080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887096 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_2887096 : Nat := 118140960795 + 2887096 * 2 ^ 59
def prefixEnd_2887096 : Nat := 4983230072969 + 3 ^ 40 * 2887096 * 2
def baseEnd_2887096 : Nat := 1482467943673141457322493

theorem tailTrace_2887096 : CollatzResearch.WordTrace tailWord_2887096 prefixEnd_2887096 1482467943673141457322493 := by
  unfold tailWord_2887096
  simp only [CollatzResearch.WordTrace]
  refine ⟨52650520974275871793032571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70200694632367829057376761 52650520974275871793032571)
  ·
    refine ⟨78975781461413807689548857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52650520974275871793032571 78975781461413807689548857)
    ·
      refine ⟨59231836096060355767161643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78975781461413807689548857 59231836096060355767161643)
      ·
        refine ⟨88847754144090533650742465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59231836096060355767161643 88847754144090533650742465)
        ·
          refine ⟨66635815608067900238056849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88847754144090533650742465 66635815608067900238056849)
          ·
            refine ⟨49976861706050925178542637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66635815608067900238056849 49976861706050925178542637)
            ·
              refine ⟨18741323139769096941953489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49976861706050925178542637 18741323139769096941953489)
              ·
                refine ⟨14055992354826822706465117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18741323139769096941953489 14055992354826822706465117)
                ·
                  refine ⟨5270997133060058514924419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14055992354826822706465117 5270997133060058514924419)
                  ·
                    refine ⟨7906495699590087772386629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270997133060058514924419 7906495699590087772386629)
                    ·
                      refine ⟨1482467943673141457322493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7906495699590087772386629 1482467943673141457322493)
                      ·
                        rfl

theorem cell23_2887096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_2887096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887096 prefixEnd_2887096 := by exact prefixLift 2887096
  have htrace : WordTrace (prefixWord ++ tailWord_2887096) baseStart_2887096 baseEnd_2887096 := by
    simpa [prefixWord, tailWord_2887096, baseEnd_2887096] using wordTrace_append hprefix tailTrace_2887096
  have hstable : (prefixWord ++ tailWord_2887096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887096).length < 2 ^ (prefixWord ++ tailWord_2887096).sum := by decide
  have hdescent : baseEnd_2887096 < baseStart_2887096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887119 : List Nat := [1, 1, 2, 1, 1, 4, 2, 11]
def baseStart_2887119 : Nat := 118140960795 + 2887119 * 2 ^ 59
def prefixEnd_2887119 : Nat := 4983230072969 + 3 ^ 40 * 2887119 * 2
def baseEnd_2887119 : Nat := 54906657545488698790181

theorem tailTrace_2887119 : CollatzResearch.WordTrace tailWord_2887119 prefixEnd_2887119 54906657545488698790181 := by
  unfold tailWord_2887119
  simp only [CollatzResearch.WordTrace]
  refine ⟨105301880827468418514152411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70201253884978945676101607 105301880827468418514152411)
  ·
    refine ⟨157952821241202627771228617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105301880827468418514152411 157952821241202627771228617)
    ·
      refine ⟨118464615930901970828421463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157952821241202627771228617 118464615930901970828421463)
      ·
        refine ⟨177696923896352956242632195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118464615930901970828421463 177696923896352956242632195)
        ·
          refine ⟨266545385844529434363948293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177696923896352956242632195 266545385844529434363948293)
          ·
            refine ⟨49977259845849268943240305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266545385844529434363948293 49977259845849268943240305)
            ·
              refine ⟨37482944884386951707430229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49977259845849268943240305 37482944884386951707430229)
              ·
                refine ⟨54906657545488698790181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37482944884386951707430229 54906657545488698790181)
                ·
                  rfl

theorem cell23_2887119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 11].length) (baseStart_2887119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887119 prefixEnd_2887119 := by exact prefixLift 2887119
  have htrace : WordTrace (prefixWord ++ tailWord_2887119) baseStart_2887119 baseEnd_2887119 := by
    simpa [prefixWord, tailWord_2887119, baseEnd_2887119] using wordTrace_append hprefix tailTrace_2887119
  have hstable : (prefixWord ++ tailWord_2887119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887119).length < 2 ^ (prefixWord ++ tailWord_2887119).sum := by decide
  have hdescent : baseEnd_2887119 < baseStart_2887119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887124 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_2887124 : Nat := 118140960795 + 2887124 * 2 ^ 59
def prefixEnd_2887124 : Nat := 4983230072969 + 3 ^ 40 * 2887124 * 2
def baseEnd_2887124 : Nat := 1482482321131467347772365

theorem tailTrace_2887124 : CollatzResearch.WordTrace tailWord_2887124 prefixEnd_2887124 1482482321131467347772365 := by
  unfold tailWord_2887124
  simp only [CollatzResearch.WordTrace]
  refine ⟨52651031596225152184042213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70201375461633536245389617 52651031596225152184042213)
  ·
    refine ⟨9872068424292216034507915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52651031596225152184042213 9872068424292216034507915)
    ·
      refine ⟨14808102636438324051761873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9872068424292216034507915 14808102636438324051761873)
      ·
        refine ⟨11106076977328743038821405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14808102636438324051761873 11106076977328743038821405)
        ·
          refine ⟨4164778866498278639558027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11106076977328743038821405 4164778866498278639558027)
          ·
            refine ⟨6247168299747417959337041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164778866498278639558027 6247168299747417959337041)
            ·
              refine ⟨4685376224810563469502781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247168299747417959337041 4685376224810563469502781)
              ·
                refine ⟨1757016084303961301063543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4685376224810563469502781 1757016084303961301063543)
                ·
                  refine ⟨2635524126455941951595315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757016084303961301063543 2635524126455941951595315)
                  ·
                    refine ⟨3953286189683912927392973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635524126455941951595315 3953286189683912927392973)
                    ·
                      refine ⟨1482482321131467347772365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953286189683912927392973 1482482321131467347772365)
                      ·
                        rfl

theorem cell23_2887124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_2887124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887124 prefixEnd_2887124 := by exact prefixLift 2887124
  have htrace : WordTrace (prefixWord ++ tailWord_2887124) baseStart_2887124 baseEnd_2887124 := by
    simpa [prefixWord, tailWord_2887124, baseEnd_2887124] using wordTrace_append hprefix tailTrace_2887124
  have hstable : (prefixWord ++ tailWord_2887124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887124).length < 2 ^ (prefixWord ++ tailWord_2887124).sum := by decide
  have hdescent : baseEnd_2887124 < baseStart_2887124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887130 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4]
def baseStart_2887130 : Nat := 118140960795 + 2887130 * 2 ^ 59
def prefixEnd_2887130 : Nat := 4983230072969 + 3 ^ 40 * 2887130 * 2
def baseEnd_2887130 : Nat := 1482485402015394324297337

theorem tailTrace_2887130 : CollatzResearch.WordTrace tailWord_2887130 prefixEnd_2887130 1482485402015394324297337 := by
  unfold tailWord_2887130
  simp only [CollatzResearch.WordTrace]
  refine ⟨26325570507607141848200711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70201521353619044928535229 26325570507607141848200711)
  ·
    refine ⟨39488355761410712772301067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26325570507607141848200711 39488355761410712772301067)
    ·
      refine ⟨59232533642116069158451601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39488355761410712772301067 59232533642116069158451601)
      ·
        refine ⟨44424400231587051868838701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59232533642116069158451601 44424400231587051868838701)
        ·
          refine ⟨16659150086845144450814513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44424400231587051868838701 16659150086845144450814513)
          ·
            refine ⟨12494362565133858338110885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16659150086845144450814513 12494362565133858338110885)
            ·
              refine ⟨2342692980962598438395791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12494362565133858338110885 2342692980962598438395791)
              ·
                refine ⟨3514039471443897657593687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342692980962598438395791 3514039471443897657593687)
                ·
                  refine ⟨5271059207165846486390531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514039471443897657593687 5271059207165846486390531)
                  ·
                    refine ⟨7906588810748769729585797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5271059207165846486390531 7906588810748769729585797)
                    ·
                      refine ⟨1482485402015394324297337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7906588810748769729585797 1482485402015394324297337)
                      ·
                        rfl

theorem cell23_2887130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_2887130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887130 prefixEnd_2887130 := by exact prefixLift 2887130
  have htrace : WordTrace (prefixWord ++ tailWord_2887130) baseStart_2887130 baseEnd_2887130 := by
    simpa [prefixWord, tailWord_2887130, baseEnd_2887130] using wordTrace_append hprefix tailTrace_2887130
  have hstable : (prefixWord ++ tailWord_2887130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887130).length < 2 ^ (prefixWord ++ tailWord_2887130).sum := by decide
  have hdescent : baseEnd_2887130 < baseStart_2887130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887170 : List Nat := [3, 4, 1, 2, 1, 1, 4, 7]
def baseStart_2887170 : Nat := 118140960795 + 2887170 * 2 ^ 59
def prefixEnd_2887170 : Nat := 4983230072969 + 3 ^ 40 * 2887170 * 2
def baseEnd_2887170 : Nat := 54907627453391635844339

theorem tailTrace_2887170 : CollatzResearch.WordTrace tailWord_2887170 prefixEnd_2887170 54907627453391635844339 := by
  unfold tailWord_2887170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26325935237570913556064741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70202493966855769482839309 26325935237570913556064741)
  ·
    refine ⟨4936112857044546291762139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26325935237570913556064741 4936112857044546291762139)
    ·
      refine ⟨7404169285566819437643209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936112857044546291762139 7404169285566819437643209)
      ·
        refine ⟨5553126964175114578232407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7404169285566819437643209 5553126964175114578232407)
        ·
          refine ⟨8329690446262671867348611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5553126964175114578232407 8329690446262671867348611)
          ·
            refine ⟨12494535669394007801022917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329690446262671867348611 12494535669394007801022917)
            ·
              refine ⟨2342725438011376462691797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12494535669394007801022917 2342725438011376462691797)
              ·
                refine ⟨54907627453391635844339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2342725438011376462691797 54907627453391635844339)
                ·
                  rfl

theorem cell23_2887170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_2887170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887170 prefixEnd_2887170 := by exact prefixLift 2887170
  have htrace : WordTrace (prefixWord ++ tailWord_2887170) baseStart_2887170 baseEnd_2887170 := by
    simpa [prefixWord, tailWord_2887170, baseEnd_2887170] using wordTrace_append hprefix tailTrace_2887170
  have hstable : (prefixWord ++ tailWord_2887170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887170).length < 2 ^ (prefixWord ++ tailWord_2887170).sum := by decide
  have hdescent : baseEnd_2887170 < baseStart_2887170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887176 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2887176 : Nat := 118140960795 + 2887176 * 2 ^ 59
def prefixEnd_2887176 : Nat := 4983230072969 + 3 ^ 40 * 2887176 * 2
def baseEnd_2887176 : Nat := 1482509022125501144322125

theorem tailTrace_2887176 : CollatzResearch.WordTrace tailWord_2887176 prefixEnd_2887176 1482509022125501144322125 := by
  unfold tailWord_2887176
  simp only [CollatzResearch.WordTrace]
  refine ⟨52651979894130958624488691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70202639858841278165984921 52651979894130958624488691)
  ·
    refine ⟨78977969841196437936733037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52651979894130958624488691 78977969841196437936733037)
    ·
      refine ⟨29616738690448664226274889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78977969841196437936733037 29616738690448664226274889)
      ·
        refine ⟨22212554017836498169706167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29616738690448664226274889 22212554017836498169706167)
        ·
          refine ⟨33318831026754747254559251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22212554017836498169706167 33318831026754747254559251)
          ·
            refine ⟨49978246540132120881838877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33318831026754747254559251 49978246540132120881838877)
            ·
              refine ⟨18741842452549545330689579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49978246540132120881838877 18741842452549545330689579)
              ·
                refine ⟨28112763678824317996034369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18741842452549545330689579 28112763678824317996034369)
                ·
                  refine ⟨21084572759118238497025777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28112763678824317996034369 21084572759118238497025777)
                  ·
                    refine ⟨15813429569338678872769333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21084572759118238497025777 15813429569338678872769333)
                    ·
                      refine ⟨1482509022125501144322125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15813429569338678872769333 1482509022125501144322125)
                      ·
                        rfl

theorem cell23_2887176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2887176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887176 prefixEnd_2887176 := by exact prefixLift 2887176
  have htrace : WordTrace (prefixWord ++ tailWord_2887176) baseStart_2887176 baseEnd_2887176 := by
    simpa [prefixWord, tailWord_2887176, baseEnd_2887176] using wordTrace_append hprefix tailTrace_2887176
  have hstable : (prefixWord ++ tailWord_2887176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887176).length < 2 ^ (prefixWord ++ tailWord_2887176).sum := by decide
  have hdescent : baseEnd_2887176 < baseStart_2887176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887214 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_2887214 : Nat := 118140960795 + 2887214 * 2 ^ 59
def prefixEnd_2887214 : Nat := 4983230072969 + 3 ^ 40 * 2887214 * 2
def baseEnd_2887214 : Nat := 1482528534390371995646951

theorem tailTrace_2887214 : CollatzResearch.WordTrace tailWord_2887214 prefixEnd_2887214 1482528534390371995646951 := by
  unfold tailWord_2887214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13163168220265531217357587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70203563841416166492573797 13163168220265531217357587)
  ·
    refine ⟨19744752330398296826036381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13163168220265531217357587 19744752330398296826036381)
    ·
      refine ⟨7404282123899361309763643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19744752330398296826036381 7404282123899361309763643)
      ·
        refine ⟨11106423185849041964645465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404282123899361309763643 11106423185849041964645465)
        ·
          refine ⟨8329817389386781473484099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11106423185849041964645465 8329817389386781473484099)
          ·
            refine ⟨12494726084080172210226149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329817389386781473484099 12494726084080172210226149)
            ·
              refine ⟨2342761140765032289417403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12494726084080172210226149 2342761140765032289417403)
              ·
                refine ⟨3514141711147548434126105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342761140765032289417403 3514141711147548434126105)
                ·
                  refine ⟨2635606283360661325594579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514141711147548434126105 2635606283360661325594579)
                  ·
                    refine ⟨3953409425040991988391869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635606283360661325594579 3953409425040991988391869)
                    ·
                      refine ⟨1482528534390371995646951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953409425040991988391869 1482528534390371995646951)
                      ·
                        rfl

theorem cell23_2887214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_2887214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887214 prefixEnd_2887214 := by exact prefixLift 2887214
  have htrace : WordTrace (prefixWord ++ tailWord_2887214) baseStart_2887214 baseEnd_2887214 := by
    simpa [prefixWord, tailWord_2887214, baseEnd_2887214] using wordTrace_append hprefix tailTrace_2887214
  have hstable : (prefixWord ++ tailWord_2887214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887214).length < 2 ^ (prefixWord ++ tailWord_2887214).sum := by decide
  have hdescent : baseEnd_2887214 < baseStart_2887214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887216 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_2887216 : Nat := 118140960795 + 2887216 * 2 ^ 59
def prefixEnd_2887216 : Nat := 4983230072969 + 3 ^ 40 * 2887216 * 2
def baseEnd_2887216 : Nat := 1482529561351680987821941

theorem tailTrace_2887216 : CollatzResearch.WordTrace tailWord_2887216 prefixEnd_2887216 1482529561351680987821941 := by
  unfold tailWord_2887216
  simp only [CollatzResearch.WordTrace]
  refine ⟨52652709354058502040216751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70203612472078002720289001 52652709354058502040216751)
  ·
    refine ⟨78979064031087753060325127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52652709354058502040216751 78979064031087753060325127)
    ·
      refine ⟨118468596046631629590487691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78979064031087753060325127 118468596046631629590487691)
      ·
        refine ⟨177702894069947444385731537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118468596046631629590487691 177702894069947444385731537)
        ·
          refine ⟨133277170552460583289298653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177702894069947444385731537 133277170552460583289298653)
          ·
            refine ⟨49978938957172718733486995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133277170552460583289298653 49978938957172718733486995)
            ·
              refine ⟨74968408435759078100230493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49978938957172718733486995 74968408435759078100230493)
              ·
                refine ⟨28113153163409654287586435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74968408435759078100230493 28113153163409654287586435)
                ·
                  refine ⟨42169729745114481431379653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28113153163409654287586435 42169729745114481431379653)
                  ·
                    refine ⟨7906824327208965268383685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42169729745114481431379653 7906824327208965268383685)
                    ·
                      refine ⟨1482529561351680987821941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7906824327208965268383685 1482529561351680987821941)
                      ·
                        rfl

theorem cell23_2887216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_2887216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887216 prefixEnd_2887216 := by exact prefixLift 2887216
  have htrace : WordTrace (prefixWord ++ tailWord_2887216) baseStart_2887216 baseEnd_2887216 := by
    simpa [prefixWord, tailWord_2887216, baseEnd_2887216] using wordTrace_append hprefix tailTrace_2887216
  have hstable : (prefixWord ++ tailWord_2887216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887216).length < 2 ^ (prefixWord ++ tailWord_2887216).sum := by decide
  have hdescent : baseEnd_2887216 < baseStart_2887216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887226 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_2887226 : Nat := 118140960795 + 2887226 * 2 ^ 59
def prefixEnd_2887226 : Nat := 4983230072969 + 3 ^ 40 * 2887226 * 2
def baseEnd_2887226 : Nat := 164726077350913994299655

theorem tailTrace_2887226 : CollatzResearch.WordTrace tailWord_2887226 prefixEnd_2887226 164726077350913994299655 := by
  unfold tailWord_2887226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326445859520193947074383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70203855625387183858865021 26326445859520193947074383)
  ·
    refine ⟨39489668789280290920611575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26326445859520193947074383 39489668789280290920611575)
    ·
      refine ⟨59234503183920436380917363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39489668789280290920611575 59234503183920436380917363)
      ·
        refine ⟨88851754775880654571376045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59234503183920436380917363 88851754775880654571376045)
        ·
          refine ⟨33319408040955245464266017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88851754775880654571376045 33319408040955245464266017)
          ·
            refine ⟨24989556030716434098199513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33319408040955245464266017 24989556030716434098199513)
            ·
              refine ⟨18742167023037325573649635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24989556030716434098199513 18742167023037325573649635)
              ·
                refine ⟨28113250534555988360474453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18742167023037325573649635 28113250534555988360474453)
                ·
                  refine ⟨164726077350913994299655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28113250534555988360474453 164726077350913994299655)
                  ·
                    rfl

theorem cell23_2887226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_2887226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887226 prefixEnd_2887226 := by exact prefixLift 2887226
  have htrace : WordTrace (prefixWord ++ tailWord_2887226) baseStart_2887226 baseEnd_2887226 := by
    simpa [prefixWord, tailWord_2887226, baseEnd_2887226] using wordTrace_append hprefix tailTrace_2887226
  have hstable : (prefixWord ++ tailWord_2887226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887226).length < 2 ^ (prefixWord ++ tailWord_2887226).sum := by decide
  have hdescent : baseEnd_2887226 < baseStart_2887226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887243 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 5]
def baseStart_2887243 : Nat := 118140960795 + 2887243 * 2 ^ 59
def prefixEnd_2887243 : Nat := 4983230072969 + 3 ^ 40 * 2887243 * 2
def baseEnd_2887243 : Nat := 164727047258816931353813

theorem tailTrace_2887243 : CollatzResearch.WordTrace tailWord_2887243 prefixEnd_2887243 164727047258816931353813 := by
  unfold tailWord_2887243
  simp only [CollatzResearch.WordTrace]
  refine ⟨105306403479019187691666383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70204268986012791794444255 105306403479019187691666383)
  ·
    refine ⟨157959605218528781537499575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105306403479019187691666383 157959605218528781537499575)
    ·
      refine ⟨236939407827793172306249363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157959605218528781537499575 236939407827793172306249363)
      ·
        refine ⟨355409111741689758459374045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236939407827793172306249363 355409111741689758459374045)
        ·
          refine ⟨133278416903133659422265267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355409111741689758459374045 133278416903133659422265267)
          ·
            refine ⟨199917625354700489133397901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133278416903133659422265267 199917625354700489133397901)
            ·
              refine ⟨74969109508012683425024213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199917625354700489133397901 74969109508012683425024213)
              ·
                refine ⟨1757088504094047267774005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74969109508012683425024213 1757088504094047267774005)
                ·
                  refine ⟨164727047258816931353813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1757088504094047267774005 164727047258816931353813)
                  ·
                    rfl

theorem cell23_2887243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 5].length) (baseStart_2887243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887243 prefixEnd_2887243 := by exact prefixLift 2887243
  have htrace : WordTrace (prefixWord ++ tailWord_2887243) baseStart_2887243 baseEnd_2887243 := by
    simpa [prefixWord, tailWord_2887243, baseEnd_2887243] using wordTrace_append hprefix tailTrace_2887243
  have hstable : (prefixWord ++ tailWord_2887243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887243).length < 2 ^ (prefixWord ++ tailWord_2887243).sum := by decide
  have hdescent : baseEnd_2887243 < baseStart_2887243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887253 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2887253 : Nat := 118140960795 + 2887253 * 2 ^ 59
def prefixEnd_2887253 : Nat := 4983230072969 + 3 ^ 40 * 2887253 * 2
def baseEnd_2887253 : Nat := 1482548560135897343059271

theorem tailTrace_2887253 : CollatzResearch.WordTrace tailWord_2887253 prefixEnd_2887253 1482548560135897343059271 := by
  unfold tailWord_2887253
  simp only [CollatzResearch.WordTrace]
  refine ⟨105306768208982959399530413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70204512139321972933020275 105306768208982959399530413)
  ·
    refine ⟨39490038078368609774823905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105306768208982959399530413 39490038078368609774823905)
    ·
      refine ⟨29617528558776457331117929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39490038078368609774823905 29617528558776457331117929)
      ·
        refine ⟨22213146419082342998338447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29617528558776457331117929 22213146419082342998338447)
        ·
          refine ⟨33319719628623514497507671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22213146419082342998338447 33319719628623514497507671)
          ·
            refine ⟨49979579442935271746261507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33319719628623514497507671 49979579442935271746261507)
            ·
              refine ⟨74969369164402907619392261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49979579442935271746261507 74969369164402907619392261)
              ·
                refine ⟨14056756718325545178636049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74969369164402907619392261 14056756718325545178636049)
                ·
                  refine ⟨10542567538744158883977037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14056756718325545178636049 10542567538744158883977037)
                  ·
                    refine ⟨3953462827029059581491389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10542567538744158883977037 3953462827029059581491389)
                    ·
                      refine ⟨1482548560135897343059271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953462827029059581491389 1482548560135897343059271)
                      ·
                        rfl

theorem cell23_2887253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2887253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887253 prefixEnd_2887253 := by exact prefixLift 2887253
  have htrace : WordTrace (prefixWord ++ tailWord_2887253) baseStart_2887253 baseEnd_2887253 := by
    simpa [prefixWord, tailWord_2887253, baseEnd_2887253] using wordTrace_append hprefix tailTrace_2887253
  have hstable : (prefixWord ++ tailWord_2887253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887253).length < 2 ^ (prefixWord ++ tailWord_2887253).sum := by decide
  have hdescent : baseEnd_2887253 < baseStart_2887253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887256 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_2887256 : Nat := 118140960795 + 2887256 * 2 ^ 59
def prefixEnd_2887256 : Nat := 4983230072969 + 3 ^ 40 * 2887256 * 2
def baseEnd_2887256 : Nat := 494183366859286943773919

theorem tailTrace_2887256 : CollatzResearch.WordTrace tailWord_2887256 prefixEnd_2887256 494183366859286943773919 := by
  unfold tailWord_2887256
  simp only [CollatzResearch.WordTrace]
  refine ⟨52653438813986045455944811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70204585085314727274593081 52653438813986045455944811)
  ·
    refine ⟨78980158220979068183917217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52653438813986045455944811 78980158220979068183917217)
    ·
      refine ⟨59235118665734301137937913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78980158220979068183917217 59235118665734301137937913)
      ·
        refine ⟨44426338999300725853453435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59235118665734301137937913 44426338999300725853453435)
        ·
          refine ⟨66639508498951088780180153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44426338999300725853453435 66639508498951088780180153)
          ·
            refine ⟨49979631374213316585135115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66639508498951088780180153 49979631374213316585135115)
            ·
              refine ⟨74969447061319974877702673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49979631374213316585135115 74969447061319974877702673)
              ·
                refine ⟨56227085295989981158277005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74969447061319974877702673 56227085295989981158277005)
                ·
                  refine ⟨21085156985996242934353877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56227085295989981158277005 21085156985996242934353877)
                  ·
                    refine ⟨494183366859286943773919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21085156985996242934353877 494183366859286943773919)
                    ·
                      rfl

theorem cell23_2887256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_2887256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887256 prefixEnd_2887256 := by exact prefixLift 2887256
  have htrace : WordTrace (prefixWord ++ tailWord_2887256) baseStart_2887256 baseEnd_2887256 := by
    simpa [prefixWord, tailWord_2887256, baseEnd_2887256] using wordTrace_append hprefix tailTrace_2887256
  have hstable : (prefixWord ++ tailWord_2887256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887256).length < 2 ^ (prefixWord ++ tailWord_2887256).sum := by decide
  have hdescent : baseEnd_2887256 < baseStart_2887256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887320 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 3, 4]
def baseStart_2887320 : Nat := 118140960795 + 2887320 * 2 ^ 59
def prefixEnd_2887320 : Nat := 4983230072969 + 3 ^ 40 * 2887320 * 2
def baseEnd_2887320 : Nat := 494194321113249526973821

theorem tailTrace_2887320 : CollatzResearch.WordTrace tailWord_2887320 prefixEnd_2887320 494194321113249526973821 := by
  unfold tailWord_2887320
  simp only [CollatzResearch.WordTrace]
  refine ⟨52654605949870114921109707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70206141266493486561479609 52654605949870114921109707)
  ·
    refine ⟨78981908924805172381664561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52654605949870114921109707 78981908924805172381664561)
    ·
      refine ⟨59236431693603879286248421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78981908924805172381664561 59236431693603879286248421)
      ·
        refine ⟨11106830942550727366171579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59236431693603879286248421 11106830942550727366171579)
        ·
          refine ⟨16660246413826091049257369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11106830942550727366171579 16660246413826091049257369)
          ·
            refine ⟨12495184810369568286943027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16660246413826091049257369 12495184810369568286943027)
            ·
              refine ⟨18742777215554352430414541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12495184810369568286943027 18742777215554352430414541)
              ·
                refine ⟨7028541455832882161405453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18742777215554352430414541 7028541455832882161405453)
                ·
                  refine ⟨2635703045937330810527045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7028541455832882161405453 2635703045937330810527045)
                  ·
                    refine ⟨494194321113249526973821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635703045937330810527045 494194321113249526973821)
                    ·
                      rfl

theorem cell23_2887320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_2887320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887320 prefixEnd_2887320 := by exact prefixLift 2887320
  have htrace : WordTrace (prefixWord ++ tailWord_2887320) baseStart_2887320 baseEnd_2887320 := by
    simpa [prefixWord, tailWord_2887320, baseEnd_2887320] using wordTrace_append hprefix tailTrace_2887320
  have hstable : (prefixWord ++ tailWord_2887320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887320).length < 2 ^ (prefixWord ++ tailWord_2887320).sum := by decide
  have hdescent : baseEnd_2887320 < baseStart_2887320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887333 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 6]
def baseStart_2887333 : Nat := 118140960795 + 2887333 * 2 ^ 59
def prefixEnd_2887333 : Nat := 4983230072969 + 3 ^ 40 * 2887333 * 2
def baseEnd_2887333 : Nat := 164732182065361892228767

theorem tailTrace_2887333 : CollatzResearch.WordTrace tailWord_2887333 prefixEnd_2887333 164732182065361892228767 := by
  unfold tailWord_2887333
  simp only [CollatzResearch.WordTrace]
  refine ⟨105309686048693133062442653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70206457365795422041628435 105309686048693133062442653)
  ·
    refine ⟨39491132268259924898415995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105309686048693133062442653 39491132268259924898415995)
    ·
      refine ⟨59236698402389887347623993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39491132268259924898415995 59236698402389887347623993)
      ·
        refine ⟨44427523801792415510717995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59236698402389887347623993 44427523801792415510717995)
        ·
          refine ⟨66641285702688623266076993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44427523801792415510717995 66641285702688623266076993)
          ·
            refine ⟨49980964277016467449557745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66641285702688623266076993 49980964277016467449557745)
            ·
              refine ⟨37485723207762350587168309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49980964277016467449557745 37485723207762350587168309)
              ·
                refine ⟨3514286550727720367547029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37485723207762350587168309 3514286550727720367547029)
                ·
                  refine ⟨164732182065361892228767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3514286550727720367547029 164732182065361892228767)
                  ·
                    rfl

theorem cell23_2887333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_2887333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887333 prefixEnd_2887333 := by exact prefixLift 2887333
  have htrace : WordTrace (prefixWord ++ tailWord_2887333) baseStart_2887333 baseEnd_2887333 := by
    simpa [prefixWord, tailWord_2887333, baseEnd_2887333] using wordTrace_append hprefix tailTrace_2887333
  have hstable : (prefixWord ++ tailWord_2887333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887333).length < 2 ^ (prefixWord ++ tailWord_2887333).sum := by decide
  have hdescent : baseEnd_2887333 < baseStart_2887333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887343 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 3]
def baseStart_2887343 : Nat := 118140960795 + 2887343 * 2 ^ 59
def prefixEnd_2887343 : Nat := 4983230072969 + 3 ^ 40 * 2887343 * 2
def baseEnd_2887343 : Nat := 1482594773394801990933857

theorem tailTrace_2887343 : CollatzResearch.WordTrace tailWord_2887343 prefixEnd_2887343 1482594773394801990933857 := by
  unfold tailWord_2887343
  simp only [CollatzResearch.WordTrace]
  refine ⟨105310050778656904770306683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70206700519104603180204455 105310050778656904770306683)
  ·
    refine ⟨157965076167985357155460025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105310050778656904770306683 157965076167985357155460025)
    ·
      refine ⟨118473807125989017866595019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157965076167985357155460025 118473807125989017866595019)
      ·
        refine ⟨177710710688983526799892529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118473807125989017866595019 177710710688983526799892529)
        ·
          refine ⟨133283033016737645099919397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177710710688983526799892529 133283033016737645099919397)
          ·
            refine ⟨24990568690638308456234887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133283033016737645099919397 24990568690638308456234887)
            ·
              refine ⟨37485853035957462684352331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24990568690638308456234887 37485853035957462684352331)
              ·
                refine ⟨56228779553936194026528497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37485853035957462684352331 56228779553936194026528497)
                ·
                  refine ⟨42171584665452145519896373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56228779553936194026528497 42171584665452145519896373)
                  ·
                    refine ⟨3953586062386138642490285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42171584665452145519896373 3953586062386138642490285)
                    ·
                      refine ⟨1482594773394801990933857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953586062386138642490285 1482594773394801990933857)
                      ·
                        rfl

theorem cell23_2887343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_2887343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887343 prefixEnd_2887343 := by exact prefixLift 2887343
  have htrace : WordTrace (prefixWord ++ tailWord_2887343) baseStart_2887343 baseEnd_2887343 := by
    simpa [prefixWord, tailWord_2887343, baseEnd_2887343] using wordTrace_append hprefix tailTrace_2887343
  have hstable : (prefixWord ++ tailWord_2887343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887343).length < 2 ^ (prefixWord ++ tailWord_2887343).sum := by decide
  have hdescent : baseEnd_2887343 < baseStart_2887343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887354 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_2887354 : Nat := 118140960795 + 2887354 * 2 ^ 59
def prefixEnd_2887354 : Nat := 4983230072969 + 3 ^ 40 * 2887354 * 2
def baseEnd_2887354 : Nat := 494200140560667149298769

theorem tailTrace_2887354 : CollatzResearch.WordTrace tailWord_2887354 prefixEnd_2887354 494200140560667149298769 := by
  unfold tailWord_2887354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26327612995404263412239279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70206967987744702432638077 26327612995404263412239279)
  ·
    refine ⟨39491419493106395118358919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26327612995404263412239279 39491419493106395118358919)
    ·
      refine ⟨59237129239659592677538379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39491419493106395118358919 59237129239659592677538379)
      ·
        refine ⟨88855693859489389016307569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59237129239659592677538379 88855693859489389016307569)
        ·
          refine ⟨66641770394617041762230677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88855693859489389016307569 66641770394617041762230677)
          ·
            refine ⟨3123832987247673832604563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66641770394617041762230677 3123832987247673832604563)
            ·
              refine ⟨4685749480871510748906845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123832987247673832604563 4685749480871510748906845)
              ·
                refine ⟨1757156055326816530840067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4685749480871510748906845 1757156055326816530840067)
                ·
                  refine ⟨2635734082990224796260101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757156055326816530840067 2635734082990224796260101)
                  ·
                    refine ⟨494200140560667149298769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635734082990224796260101 494200140560667149298769)
                    ·
                      rfl

theorem cell23_2887354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_2887354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887354 prefixEnd_2887354 := by exact prefixLift 2887354
  have htrace : WordTrace (prefixWord ++ tailWord_2887354) baseStart_2887354 baseEnd_2887354 := by
    simpa [prefixWord, tailWord_2887354, baseEnd_2887354] using wordTrace_append hprefix tailTrace_2887354
  have hstable : (prefixWord ++ tailWord_2887354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887354).length < 2 ^ (prefixWord ++ tailWord_2887354).sum := by decide
  have hdescent : baseEnd_2887354 < baseStart_2887354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887377 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_2887377 : Nat := 118140960795 + 2887377 * 2 ^ 59
def prefixEnd_2887377 : Nat := 4983230072969 + 3 ^ 40 * 2887377 * 2
def baseEnd_2887377 : Nat := 1482612231737054857908701

theorem tailTrace_2887377 : CollatzResearch.WordTrace tailWord_2887377 prefixEnd_2887377 1482612231737054857908701 := by
  unfold tailWord_2887377
  simp only [CollatzResearch.WordTrace]
  refine ⟨105311290860533728577044385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70207527240355819051362923 105311290860533728577044385)
  ·
    refine ⟨78983468145400296432783289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105311290860533728577044385 78983468145400296432783289)
    ·
      refine ⟨59237601109050222324587467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78983468145400296432783289 59237601109050222324587467)
      ·
        refine ⟨88856401663575333486881201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59237601109050222324587467 88856401663575333486881201)
        ·
          refine ⟨66642301247681500115160901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88856401663575333486881201 66642301247681500115160901)
          ·
            refine ⟨12495431483940281271592669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66642301247681500115160901 12495431483940281271592669)
            ·
              refine ⟨4685786806477605476847251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12495431483940281271592669 4685786806477605476847251)
              ·
                refine ⟨7028680209716408215270877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685786806477605476847251 7028680209716408215270877)
                ·
                  refine ⟨2635755078643653080726579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7028680209716408215270877 2635755078643653080726579)
                  ·
                    refine ⟨3953632617965479621089869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635755078643653080726579 3953632617965479621089869)
                    ·
                      refine ⟨1482612231737054857908701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953632617965479621089869 1482612231737054857908701)
                      ·
                        rfl

theorem cell23_2887377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_2887377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887377 prefixEnd_2887377 := by exact prefixLift 2887377
  have htrace : WordTrace (prefixWord ++ tailWord_2887377) baseStart_2887377 baseEnd_2887377 := by
    simpa [prefixWord, tailWord_2887377, baseEnd_2887377] using wordTrace_append hprefix tailTrace_2887377
  have hstable : (prefixWord ++ tailWord_2887377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887377).length < 2 ^ (prefixWord ++ tailWord_2887377).sum := by decide
  have hdescent : baseEnd_2887377 < baseStart_2887377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887403 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5]
def baseStart_2887403 : Nat := 118140960795 + 2887403 * 2 ^ 59
def prefixEnd_2887403 : Nat := 4983230072969 + 3 ^ 40 * 2887403 * 2
def baseEnd_2887403 : Nat := 1482625582234071756183581

theorem tailTrace_2887403 : CollatzResearch.WordTrace tailWord_2887403 prefixEnd_2887403 1482625582234071756183581 := by
  unfold tailWord_2887403
  simp only [CollatzResearch.WordTrace]
  refine ⟨105312239158439535017490863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70208159438959690011660575 105312239158439535017490863)
  ·
    refine ⟨157968358737659302526236295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105312239158439535017490863 157968358737659302526236295)
    ·
      refine ⟨236952538106488953789354443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157968358737659302526236295 236952538106488953789354443)
      ·
        refine ⟨355428807159733430684031665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236952538106488953789354443 355428807159733430684031665)
        ·
          refine ⟨266571605369800073013023749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355428807159733430684031665 266571605369800073013023749)
          ·
            refine ⟨49982176006837513689941953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266571605369800073013023749 49982176006837513689941953)
            ·
              refine ⟨37486632005128135267456465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49982176006837513689941953 37486632005128135267456465)
              ·
                refine ⟨28114974003846101450592349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37486632005128135267456465 28114974003846101450592349)
                ·
                  refine ⟨10543115251442288043972131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28114974003846101450592349 10543115251442288043972131)
                  ·
                    refine ⟨15814672877163432065958197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10543115251442288043972131 15814672877163432065958197)
                    ·
                      refine ⟨1482625582234071756183581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15814672877163432065958197 1482625582234071756183581)
                      ·
                        rfl

theorem cell23_2887403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_2887403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887403 prefixEnd_2887403 := by exact prefixLift 2887403
  have htrace : WordTrace (prefixWord ++ tailWord_2887403) baseStart_2887403 baseEnd_2887403 := by
    simpa [prefixWord, tailWord_2887403, baseEnd_2887403] using wordTrace_append hprefix tailTrace_2887403
  have hstable : (prefixWord ++ tailWord_2887403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887403).length < 2 ^ (prefixWord ++ tailWord_2887403).sum := by decide
  have hdescent : baseEnd_2887403 < baseStart_2887403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887410 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_2887410 : Nat := 118140960795 + 2887410 * 2 ^ 59
def prefixEnd_2887410 : Nat := 4983230072969 + 3 ^ 40 * 2887410 * 2
def baseEnd_2887410 : Nat := 494209725532884409598683

theorem tailTrace_2887410 : CollatzResearch.WordTrace tailWord_2887410 prefixEnd_2887410 494209725532884409598683 := by
  unfold tailWord_2887410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26328123617353543803248921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70208329646276116808663789 26328123617353543803248921)
  ·
    refine ⟨19746092713015157852436691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26328123617353543803248921 19746092713015157852436691)
    ·
      refine ⟨29619139069522736778655037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19746092713015157852436691 29619139069522736778655037)
      ·
        refine ⟨11107177151071026291995639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29619139069522736778655037 11107177151071026291995639)
        ·
          refine ⟨16660765726606539437993459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11107177151071026291995639 16660765726606539437993459)
          ·
            refine ⟨24991148589909809156990189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16660765726606539437993459 24991148589909809156990189)
            ·
              refine ⟨9371680721216178433871321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24991148589909809156990189 9371680721216178433871321)
              ·
                refine ⟨7028760540912133825403491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9371680721216178433871321 7028760540912133825403491)
                ·
                  refine ⟨10543140811368200738105237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7028760540912133825403491 10543140811368200738105237)
                  ·
                    refine ⟨494209725532884409598683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10543140811368200738105237 494209725532884409598683)
                    ·
                      rfl

theorem cell23_2887410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_2887410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887410 prefixEnd_2887410 := by exact prefixLift 2887410
  have htrace : WordTrace (prefixWord ++ tailWord_2887410) baseStart_2887410 baseEnd_2887410 := by
    simpa [prefixWord, tailWord_2887410, baseEnd_2887410] using wordTrace_append hprefix tailTrace_2887410
  have hstable : (prefixWord ++ tailWord_2887410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887410).length < 2 ^ (prefixWord ++ tailWord_2887410).sum := by decide
  have hdescent : baseEnd_2887410 < baseStart_2887410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887414 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2887414 : Nat := 118140960795 + 2887414 * 2 ^ 59
def prefixEnd_2887414 : Nat := 4983230072969 + 3 ^ 40 * 2887414 * 2
def baseEnd_2887414 : Nat := 494210410173757071048677

theorem tailTrace_2887414 : CollatzResearch.WordTrace tailWord_2887414 prefixEnd_2887414 494210410173757071048677 := by
  unfold tailWord_2887414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582040022587480243508831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70208426907599789264094197 6582040022587480243508831)
  ·
    refine ⟨9873060033881220365263247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582040022587480243508831 9873060033881220365263247)
    ·
      refine ⟨14809590050821830547894871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9873060033881220365263247 14809590050821830547894871)
      ·
        refine ⟨22214385076232745821842307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14809590050821830547894871 22214385076232745821842307)
        ·
          refine ⟨33321577614349118732763461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22214385076232745821842307 33321577614349118732763461)
          ·
            refine ⟨6247795802690459762393149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33321577614349118732763461 6247795802690459762393149)
            ·
              refine ⟨2342923426008922410897431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6247795802690459762393149 2342923426008922410897431)
              ·
                refine ⟨3514385139013383616346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342923426008922410897431 3514385139013383616346147)
                ·
                  refine ⟨5271577708520075424519221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514385139013383616346147 5271577708520075424519221)
                  ·
                    refine ⟨494210410173757071048677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5271577708520075424519221 494210410173757071048677)
                    ·
                      rfl

theorem cell23_2887414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2887414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887414 prefixEnd_2887414 := by exact prefixLift 2887414
  have htrace : WordTrace (prefixWord ++ tailWord_2887414) baseStart_2887414 baseEnd_2887414 := by
    simpa [prefixWord, tailWord_2887414, baseEnd_2887414] using wordTrace_append hprefix tailTrace_2887414
  have hstable : (prefixWord ++ tailWord_2887414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887414).length < 2 ^ (prefixWord ++ tailWord_2887414).sum := by decide
  have hdescent : baseEnd_2887414 < baseStart_2887414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887428 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2887428 : Nat := 118140960795 + 2887428 * 2 ^ 59
def prefixEnd_2887428 : Nat := 4983230072969 + 3 ^ 40 * 2887428 * 2
def baseEnd_2887428 : Nat := 1482638419250434158370967

theorem tailTrace_2887428 : CollatzResearch.WordTrace tailWord_2887428 prefixEnd_2887428 1482638419250434158370967 := by
  unfold tailWord_2887428
  simp only [CollatzResearch.WordTrace]
  refine ⟨52656575491674482143575469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70208767322232642858100625 52656575491674482143575469)
  ·
    refine ⟨19746215809377930803840801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52656575491674482143575469 19746215809377930803840801)
    ·
      refine ⟨14809661857033448102880601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19746215809377930803840801 14809661857033448102880601)
      ·
        refine ⟨11107246392775086077160451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14809661857033448102880601 11107246392775086077160451)
        ·
          refine ⟨16660869589162629115740677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11107246392775086077160451 16660869589162629115740677)
          ·
            refine ⟨3123913047967992959201377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16660869589162629115740677 3123913047967992959201377)
            ·
              refine ⟨2342934785975994719401033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3123913047967992959201377 2342934785975994719401033)
              ·
                refine ⟨1757201089481996039550775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342934785975994719401033 1757201089481996039550775)
                ·
                  refine ⟨2635801634222994059326163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757201089481996039550775 2635801634222994059326163)
                  ·
                    refine ⟨3953702451334491088989245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635801634222994059326163 3953702451334491088989245)
                    ·
                      refine ⟨1482638419250434158370967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953702451334491088989245 1482638419250434158370967)
                      ·
                        rfl

theorem cell23_2887428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2887428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887428 prefixEnd_2887428 := by exact prefixLift 2887428
  have htrace : WordTrace (prefixWord ++ tailWord_2887428) baseStart_2887428 baseEnd_2887428 := by
    simpa [prefixWord, tailWord_2887428, baseEnd_2887428] using wordTrace_append hprefix tailTrace_2887428
  have hstable : (prefixWord ++ tailWord_2887428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887428).length < 2 ^ (prefixWord ++ tailWord_2887428).sum := by decide
  have hdescent : baseEnd_2887428 < baseStart_2887428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887447 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2887447 : Nat := 118140960795 + 2887447 * 2 ^ 59
def prefixEnd_2887447 : Nat := 4983230072969 + 3 ^ 40 * 2887447 * 2
def baseEnd_2887447 : Nat := 1482648175382869584033379

theorem tailTrace_2887447 : CollatzResearch.WordTrace tailWord_2887447 prefixEnd_2887447 1482648175382869584033379 := by
  unfold tailWord_2887447
  simp only [CollatzResearch.WordTrace]
  refine ⟨105313843970280130532092595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70209229313520087021395063 105313843970280130532092595)
  ·
    refine ⟨157970765955420195798138893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105313843970280130532092595 157970765955420195798138893)
    ·
      refine ⟨59239037233282573424302085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157970765955420195798138893 59239037233282573424302085)
      ·
        refine ⟨11107319481240482517056641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59239037233282573424302085 11107319481240482517056641)
        ·
          refine ⟨8330489610930361887792481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11107319481240482517056641 8330489610930361887792481)
          ·
            refine ⟨6247867208197771415844361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8330489610930361887792481 6247867208197771415844361)
            ·
              refine ⟨4685900406148328561883271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247867208197771415844361 4685900406148328561883271)
              ·
                refine ⟨7028850609222492842824907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685900406148328561883271 7028850609222492842824907)
                ·
                  refine ⟨10543275913833739264237361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7028850609222492842824907 10543275913833739264237361)
                  ·
                    refine ⟨7907456935375304448178021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10543275913833739264237361 7907456935375304448178021)
                    ·
                      refine ⟨1482648175382869584033379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7907456935375304448178021 1482648175382869584033379)
                      ·
                        rfl

theorem cell23_2887447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2887447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887447 prefixEnd_2887447 := by exact prefixLift 2887447
  have htrace : WordTrace (prefixWord ++ tailWord_2887447) baseStart_2887447 baseEnd_2887447 := by
    simpa [prefixWord, tailWord_2887447, baseEnd_2887447] using wordTrace_append hprefix tailTrace_2887447
  have hstable : (prefixWord ++ tailWord_2887447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887447).length < 2 ^ (prefixWord ++ tailWord_2887447).sum := by decide
  have hdescent : baseEnd_2887447 < baseStart_2887447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887484 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_2887484 : Nat := 118140960795 + 2887484 * 2 ^ 59
def prefixEnd_2887484 : Nat := 4983230072969 + 3 ^ 40 * 2887484 * 2
def baseEnd_2887484 : Nat := 1482667174167085939270709

theorem tailTrace_2887484 : CollatzResearch.WordTrace tailWord_2887484 prefixEnd_2887484 1482667174167085939270709 := by
  unfold tailWord_2887484
  simp only [CollatzResearch.WordTrace]
  refine ⟨52657596735573042925594753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70210128980764057234126337 52657596735573042925594753)
  ·
    refine ⟨39493197551679782194196065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52657596735573042925594753 39493197551679782194196065)
    ·
      refine ⟨29619898163759836645647049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39493197551679782194196065 29619898163759836645647049)
      ·
        refine ⟨22214923622819877484235287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29619898163759836645647049 22214923622819877484235287)
        ·
          refine ⟨33322385434229816226352931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22214923622819877484235287 33322385434229816226352931)
          ·
            refine ⟨49983578151344724339529397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33322385434229816226352931 49983578151344724339529397)
            ·
              refine ⟨4685960451688567906830881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49983578151344724339529397 4685960451688567906830881)
              ·
                refine ⟨3514470338766425930123161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685960451688567906830881 3514470338766425930123161)
                ·
                  refine ⟨2635852754074819447592371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514470338766425930123161 2635852754074819447592371)
                  ·
                    refine ⟨3953779131112229171388557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2635852754074819447592371 3953779131112229171388557)
                    ·
                      refine ⟨1482667174167085939270709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953779131112229171388557 1482667174167085939270709)
                      ·
                        rfl

theorem cell23_2887484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_2887484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887484 prefixEnd_2887484 := by exact prefixLift 2887484
  have htrace : WordTrace (prefixWord ++ tailWord_2887484) baseStart_2887484 baseEnd_2887484 := by
    simpa [prefixWord, tailWord_2887484, baseEnd_2887484] using wordTrace_append hprefix tailTrace_2887484
  have hstable : (prefixWord ++ tailWord_2887484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887484).length < 2 ^ (prefixWord ++ tailWord_2887484).sum := by decide
  have hdescent : baseEnd_2887484 < baseStart_2887484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887501 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2887501 : Nat := 118140960795 + 2887501 * 2 ^ 59
def prefixEnd_2887501 : Nat := 4983230072969 + 3 ^ 40 * 2887501 * 2
def baseEnd_2887501 : Nat := 1482675903338212372758131

theorem tailTrace_2887501 : CollatzResearch.WordTrace tailWord_2887501 prefixEnd_2887501 1482675903338212372758131 := by
  unfold tailWord_2887501
  simp only [CollatzResearch.WordTrace]
  refine ⟨105315813512084497754558357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70210542341389665169705571 105315813512084497754558357)
  ·
    refine ⟨4936678758378960832244923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105315813512084497754558357 4936678758378960832244923)
    ·
      refine ⟨7405018137568441248367385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936678758378960832244923 7405018137568441248367385)
      ·
        refine ⟨5553763603176330936275539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7405018137568441248367385 5553763603176330936275539)
        ·
          refine ⟨8330645404764496404413309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5553763603176330936275539 8330645404764496404413309)
          ·
            refine ⟨3123992026786686151654991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8330645404764496404413309 3123992026786686151654991)
            ·
              refine ⟨4685988040180029227482487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123992026786686151654991 4685988040180029227482487)
              ·
                refine ⟨7028982060270043841223731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685988040180029227482487 7028982060270043841223731)
                ·
                  refine ⟨10543473090405065761835597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7028982060270043841223731 10543473090405065761835597)
                  ·
                    refine ⟨3953802408901899660688349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10543473090405065761835597 3953802408901899660688349)
                    ·
                      refine ⟨1482675903338212372758131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3953802408901899660688349 1482675903338212372758131)
                      ·
                        rfl

theorem cell23_2887501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2887501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887501 prefixEnd_2887501 := by exact prefixLift 2887501
  have htrace : WordTrace (prefixWord ++ tailWord_2887501) baseStart_2887501 baseEnd_2887501 := by
    simpa [prefixWord, tailWord_2887501, baseEnd_2887501] using wordTrace_append hprefix tailTrace_2887501
  have hstable : (prefixWord ++ tailWord_2887501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887501).length < 2 ^ (prefixWord ++ tailWord_2887501).sum := by decide
  have hdescent : baseEnd_2887501 < baseStart_2887501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887503 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 10]
def baseStart_2887503 : Nat := 118140960795 + 2887503 * 2 ^ 59
def prefixEnd_2887503 : Nat := 4983230072969 + 3 ^ 40 * 2887503 * 2
def baseEnd_2887503 : Nat := 1482676930299521364933121

theorem tailTrace_2887503 : CollatzResearch.WordTrace tailWord_2887503 prefixEnd_2887503 1482676930299521364933121 := by
  unfold tailWord_2887503
  simp only [CollatzResearch.WordTrace]
  refine ⟨105315886458077252096131163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70210590972051501397420775 105315886458077252096131163)
  ·
    refine ⟨157973829687115878144196745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105315886458077252096131163 157973829687115878144196745)
    ·
      refine ⟨118480372265336908608147559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157973829687115878144196745 118480372265336908608147559)
      ·
        refine ⟨177720558398005362912221339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118480372265336908608147559 177720558398005362912221339)
        ·
          refine ⟨266580837597008044368332009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177720558398005362912221339 266580837597008044368332009)
          ·
            refine ⟨199935628197756033276249007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266580837597008044368332009 199935628197756033276249007)
            ·
              refine ⟨299903442296634049914373511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199935628197756033276249007 299903442296634049914373511)
              ·
                refine ⟨449855163444951074871560267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299903442296634049914373511 449855163444951074871560267)
                ·
                  refine ⟨674782745167426612307340401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449855163444951074871560267 674782745167426612307340401)
                  ·
                    refine ⟨506087058875569959230505301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 674782745167426612307340401 506087058875569959230505301)
                    ·
                      refine ⟨1482676930299521364933121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 506087058875569959230505301 1482676930299521364933121)
                      ·
                        rfl

theorem cell23_2887503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_2887503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887503 prefixEnd_2887503 := by exact prefixLift 2887503
  have htrace : WordTrace (prefixWord ++ tailWord_2887503) baseStart_2887503 baseEnd_2887503 := by
    simpa [prefixWord, tailWord_2887503, baseEnd_2887503] using wordTrace_append hprefix tailTrace_2887503
  have hstable : (prefixWord ++ tailWord_2887503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887503).length < 2 ^ (prefixWord ++ tailWord_2887503).sum := by decide
  have hdescent : baseEnd_2887503 < baseStart_2887503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887511 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 1, 3, 2]
def baseStart_2887511 : Nat := 118140960795 + 2887511 * 2 ^ 59
def prefixEnd_2887511 : Nat := 4983230072969 + 3 ^ 40 * 2887511 * 2
def baseEnd_2887511 : Nat := 1482681038144757333633085

theorem tailTrace_2887511 : CollatzResearch.WordTrace tailWord_2887511 prefixEnd_2887511 1482681038144757333633085 := by
  unfold tailWord_2887511
  simp only [CollatzResearch.WordTrace]
  refine ⟨105316178242048269462422387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70210785494698846308281591 105316178242048269462422387)
  ·
    refine ⟨157974267363072404193633581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105316178242048269462422387 157974267363072404193633581)
    ·
      refine ⟨59240350261152151572612593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157974267363072404193633581 59240350261152151572612593)
      ·
        refine ⟨44430262695864113679459445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59240350261152151572612593 44430262695864113679459445)
        ·
          refine ⟨4165337127737260657449323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44430262695864113679459445 4165337127737260657449323)
          ·
            refine ⟨6248005691605890986173985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165337127737260657449323 6248005691605890986173985)
            ·
              refine ⟨4686004268704418239630489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6248005691605890986173985 4686004268704418239630489)
              ·
                refine ⟨3514503201528313679722867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686004268704418239630489 3514503201528313679722867)
                ·
                  refine ⟨5271754802292470519584301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514503201528313679722867 5271754802292470519584301)
                  ·
                    refine ⟨1976908050859676444844113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5271754802292470519584301 1976908050859676444844113)
                    ·
                      refine ⟨1482681038144757333633085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976908050859676444844113 1482681038144757333633085)
                      ·
                        rfl

theorem cell23_2887511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_2887511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887511 prefixEnd_2887511 := by exact prefixLift 2887511
  have htrace : WordTrace (prefixWord ++ tailWord_2887511) baseStart_2887511 baseEnd_2887511 := by
    simpa [prefixWord, tailWord_2887511, baseEnd_2887511] using wordTrace_append hprefix tailTrace_2887511
  have hstable : (prefixWord ++ tailWord_2887511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887511).length < 2 ^ (prefixWord ++ tailWord_2887511).sum := by decide
  have hdescent : baseEnd_2887511 < baseStart_2887511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887541 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_2887541 : Nat := 118140960795 + 2887541 * 2 ^ 59
def prefixEnd_2887541 : Nat := 4983230072969 + 3 ^ 40 * 2887541 * 2
def baseEnd_2887541 : Nat := 1482696442564392216257947

theorem tailTrace_2887541 : CollatzResearch.WordTrace tailWord_2887541 prefixEnd_2887541 1482696442564392216257947 := by
  unfold tailWord_2887541
  simp only [CollatzResearch.WordTrace]
  refine ⟨105317272431939584586014477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70211514954626389724009651 105317272431939584586014477)
  ·
    refine ⟨39493977161977344219755429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105317272431939584586014477 39493977161977344219755429)
    ·
      refine ⟨7405120717870752041204143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39493977161977344219755429 7405120717870752041204143)
      ·
        refine ⟨11107681076806128061806215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7405120717870752041204143 11107681076806128061806215)
        ·
          refine ⟨16661521615209192092709323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11107681076806128061806215 16661521615209192092709323)
          ·
            refine ⟨24992282422813788139063985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16661521615209192092709323 24992282422813788139063985)
            ·
              refine ⟨18744211817110341104297989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24992282422813788139063985 18744211817110341104297989)
              ·
                refine ⟨3514539715708188957055873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18744211817110341104297989 3514539715708188957055873)
                ·
                  refine ⟨2635904786781141717791905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514539715708188957055873 2635904786781141717791905)
                  ·
                    refine ⟨1976928590085856288343929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2635904786781141717791905 1976928590085856288343929)
                    ·
                      refine ⟨1482696442564392216257947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976928590085856288343929 1482696442564392216257947)
                      ·
                        rfl

theorem cell23_2887541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_2887541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887541 prefixEnd_2887541 := by exact prefixLift 2887541
  have htrace : WordTrace (prefixWord ++ tailWord_2887541) baseStart_2887541 baseEnd_2887541 := by
    simpa [prefixWord, tailWord_2887541, baseEnd_2887541] using wordTrace_append hprefix tailTrace_2887541
  have hstable : (prefixWord ++ tailWord_2887541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887541).length < 2 ^ (prefixWord ++ tailWord_2887541).sum := by decide
  have hdescent : baseEnd_2887541 < baseStart_2887541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887607 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 3, 4]
def baseStart_2887607 : Nat := 118140960795 + 2887607 * 2 ^ 59
def prefixEnd_2887607 : Nat := 4983230072969 + 3 ^ 40 * 2887607 * 2
def baseEnd_2887607 : Nat := 494243444095862986010881

theorem tailTrace_2887607 : CollatzResearch.WordTrace tailWord_2887607 prefixEnd_2887607 494243444095862986010881 := by
  unfold tailWord_2887607
  simp only [CollatzResearch.WordTrace]
  refine ⟨105319679649700477857917075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70213119766466985238611383 105319679649700477857917075)
  ·
    refine ⟨157979519474550716786875613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105319679649700477857917075 157979519474550716786875613)
    ·
      refine ⟨59242319802956518795078355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157979519474550716786875613 59242319802956518795078355)
      ·
        refine ⟨88863479704434778192617533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59242319802956518795078355 88863479704434778192617533)
        ·
          refine ⟨33323804889163041822231575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88863479704434778192617533 33323804889163041822231575)
          ·
            refine ⟨49985707333744562733347363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33323804889163041822231575 49985707333744562733347363)
            ·
              refine ⟨74978561000616844100021045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49985707333744562733347363 74978561000616844100021045)
              ·
                refine ⟨7029240093807829134376973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74978561000616844100021045 7029240093807829134376973)
                ·
                  refine ⟨2635965035177935925391365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7029240093807829134376973 2635965035177935925391365)
                  ·
                    refine ⟨494243444095862986010881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635965035177935925391365 494243444095862986010881)
                    ·
                      rfl

theorem cell23_2887607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_2887607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887607 prefixEnd_2887607 := by exact prefixLift 2887607
  have htrace : WordTrace (prefixWord ++ tailWord_2887607) baseStart_2887607 baseEnd_2887607 := by
    simpa [prefixWord, tailWord_2887607, baseEnd_2887607] using wordTrace_append hprefix tailTrace_2887607
  have hstable : (prefixWord ++ tailWord_2887607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887607).length < 2 ^ (prefixWord ++ tailWord_2887607).sum := by decide
  have hdescent : baseEnd_2887607 < baseStart_2887607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887610 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_2887610 : Nat := 118140960795 + 2887610 * 2 ^ 59
def prefixEnd_2887610 : Nat := 4983230072969 + 3 ^ 40 * 2887610 * 2
def baseEnd_2887610 : Nat := 1482731872729552446295129

theorem tailTrace_2887610 : CollatzResearch.WordTrace tailWord_2887610 prefixEnd_2887610 1482731872729552446295129 := by
  unfold tailWord_2887610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329947267172402342569071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70213192712459739580184189 26329947267172402342569071)
  ·
    refine ⟨39494920900758603513853607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26329947267172402342569071 39494920900758603513853607)
    ·
      refine ⟨59242381351137905270780411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39494920900758603513853607 59242381351137905270780411)
      ·
        refine ⟨88863572026706857906170617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59242381351137905270780411 88863572026706857906170617)
        ·
          refine ⟨66647679020030143429627963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88863572026706857906170617 66647679020030143429627963)
          ·
            refine ⟨99971518530045215144441945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66647679020030143429627963 99971518530045215144441945)
            ·
              refine ⟨74978638897533911358331459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99971518530045215144441945 74978638897533911358331459)
              ·
                refine ⟨112467958346300867037497189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74978638897533911358331459 112467958346300867037497189)
                ·
                  refine ⟨21087742189931412569530723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112467958346300867037497189 21087742189931412569530723)
                  ·
                    refine ⟨31631613284897118854296085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21087742189931412569530723 31631613284897118854296085)
                    ·
                      refine ⟨1482731872729552446295129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31631613284897118854296085 1482731872729552446295129)
                      ·
                        rfl

theorem cell23_2887610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_2887610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887610 prefixEnd_2887610 := by exact prefixLift 2887610
  have htrace : WordTrace (prefixWord ++ tailWord_2887610) baseStart_2887610 baseEnd_2887610 := by
    simpa [prefixWord, tailWord_2887610, baseEnd_2887610] using wordTrace_append hprefix tailTrace_2887610
  have hstable : (prefixWord ++ tailWord_2887610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887610).length < 2 ^ (prefixWord ++ tailWord_2887610).sum := by decide
  have hdescent : baseEnd_2887610 < baseStart_2887610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887614 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_2887614 : Nat := 118140960795 + 2887614 * 2 ^ 59
def prefixEnd_2887614 : Nat := 4983230072969 + 3 ^ 40 * 2887614 * 2
def baseEnd_2887614 : Nat := 1482733926652170430645111

theorem tailTrace_2887614 : CollatzResearch.WordTrace tailWord_2887614 prefixEnd_2887614 1482733926652170430645111 := by
  unfold tailWord_2887614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164991870084389756677737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70213289973783412035614597 13164991870084389756677737)
  ·
    refine ⟨9873743902563292317508303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13164991870084389756677737 9873743902563292317508303)
    ·
      refine ⟨14810615853844938476262455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9873743902563292317508303 14810615853844938476262455)
      ·
        refine ⟨22215923780767407714393683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14810615853844938476262455 22215923780767407714393683)
        ·
          refine ⟨33323885671151111571590525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22215923780767407714393683 33323885671151111571590525)
          ·
            refine ⟨12496457126681666839346447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33323885671151111571590525 12496457126681666839346447)
            ·
              refine ⟨18744685690022500259019671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12496457126681666839346447 18744685690022500259019671)
              ·
                refine ⟨28117028535033750388529507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18744685690022500259019671 28117028535033750388529507)
                ·
                  refine ⟨42175542802550625582794261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28117028535033750388529507 42175542802550625582794261)
                  ·
                    refine ⟨1976978568869560574193481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42175542802550625582794261 1976978568869560574193481)
                    ·
                      refine ⟨1482733926652170430645111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1976978568869560574193481 1482733926652170430645111)
                      ·
                        rfl

theorem cell23_2887614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_2887614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887614 prefixEnd_2887614 := by exact prefixLift 2887614
  have htrace : WordTrace (prefixWord ++ tailWord_2887614) baseStart_2887614 baseEnd_2887614 := by
    simpa [prefixWord, tailWord_2887614, baseEnd_2887614] using wordTrace_append hprefix tailTrace_2887614
  have hstable : (prefixWord ++ tailWord_2887614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887614).length < 2 ^ (prefixWord ++ tailWord_2887614).sum := by decide
  have hdescent : baseEnd_2887614 < baseStart_2887614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887624 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 3, 4]
def baseStart_2887624 : Nat := 118140960795 + 2887624 * 2 ^ 59
def prefixEnd_2887624 : Nat := 4983230072969 + 3 ^ 40 * 2887624 * 2
def baseEnd_2887624 : Nat := 494246353819571797173355

theorem tailTrace_2887624 : CollatzResearch.WordTrace tailWord_2887624 prefixEnd_2887624 494246353819571797173355 := by
  unfold tailWord_2887624
  simp only [CollatzResearch.WordTrace]
  refine ⟨52660149845319444880642963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70213533127092593174190617 52660149845319444880642963)
  ·
    refine ⟨78990224767979167320964445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52660149845319444880642963 78990224767979167320964445)
    ·
      refine ⟨29621334287992187745361667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78990224767979167320964445 29621334287992187745361667)
      ·
        refine ⟨44432001431988281618042501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29621334287992187745361667 44432001431988281618042501)
        ·
          refine ⟨8331000268497802803382969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44432001431988281618042501 8331000268497802803382969)
          ·
            refine ⟨6248250201373352102537227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8331000268497802803382969 6248250201373352102537227)
            ·
              refine ⟨9372375302060028153805841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248250201373352102537227 9372375302060028153805841)
              ·
                refine ⟨7029281476545021115354381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9372375302060028153805841 7029281476545021115354381)
                ·
                  refine ⟨2635980553704382918257893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7029281476545021115354381 2635980553704382918257893)
                  ·
                    refine ⟨494246353819571797173355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2635980553704382918257893 494246353819571797173355)
                    ·
                      rfl

theorem cell23_2887624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_2887624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887624 prefixEnd_2887624 := by exact prefixLift 2887624
  have htrace : WordTrace (prefixWord ++ tailWord_2887624) baseStart_2887624 baseEnd_2887624 := by
    simpa [prefixWord, tailWord_2887624, baseEnd_2887624] using wordTrace_append hprefix tailTrace_2887624
  have hstable : (prefixWord ++ tailWord_2887624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887624).length < 2 ^ (prefixWord ++ tailWord_2887624).sum := by decide
  have hdescent : baseEnd_2887624 < baseStart_2887624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887664 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 3, 1, 3]
def baseStart_2887664 : Nat := 118140960795 + 2887664 * 2 ^ 59
def prefixEnd_2887664 : Nat := 4983230072969 + 3 ^ 40 * 2887664 * 2
def baseEnd_2887664 : Nat := 1482759600684895235019881

theorem tailTrace_2887664 : CollatzResearch.WordTrace tailWord_2887664 prefixEnd_2887664 1482759600684895235019881 := by
  unfold tailWord_2887664
  simp only [CollatzResearch.WordTrace]
  refine ⟨52660879305246988296371023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70214505740329317728494697 52660879305246988296371023)
  ·
    refine ⟨78991318957870482444556535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52660879305246988296371023 78991318957870482444556535)
    ·
      refine ⟨118486978436805723666834803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78991318957870482444556535 118486978436805723666834803)
      ·
        refine ⟨177730467655208585500252205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118486978436805723666834803 177730467655208585500252205)
        ·
          refine ⟨66648925370703219562594577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177730467655208585500252205 66648925370703219562594577)
          ·
            refine ⟨49986694028027414671945933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66648925370703219562594577 49986694028027414671945933)
            ·
              refine ⟨18745010260510280501979725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49986694028027414671945933 18745010260510280501979725)
              ·
                refine ⟨7029378847691355188242397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18745010260510280501979725 7029378847691355188242397)
                ·
                  refine ⟨2636017067884258195590899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7029378847691355188242397 2636017067884258195590899)
                  ·
                    refine ⟨3954025601826387293386349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636017067884258195590899 3954025601826387293386349)
                    ·
                      refine ⟨1482759600684895235019881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954025601826387293386349 1482759600684895235019881)
                      ·
                        rfl

theorem cell23_2887664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_2887664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887664 prefixEnd_2887664 := by exact prefixLift 2887664
  have htrace : WordTrace (prefixWord ++ tailWord_2887664) baseStart_2887664 baseEnd_2887664 := by
    simpa [prefixWord, tailWord_2887664, baseEnd_2887664] using wordTrace_append hprefix tailTrace_2887664
  have hstable : (prefixWord ++ tailWord_2887664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887664).length < 2 ^ (prefixWord ++ tailWord_2887664).sum := by decide
  have hdescent : baseEnd_2887664 < baseStart_2887664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887704 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_2887704 : Nat := 118140960795 + 2887704 * 2 ^ 59
def prefixEnd_2887704 : Nat := 4983230072969 + 3 ^ 40 * 2887704 * 2
def baseEnd_2887704 : Nat := 1482780139911075078519697

theorem tailTrace_2887704 : CollatzResearch.WordTrace tailWord_2887704 prefixEnd_2887704 1482780139911075078519697 := by
  unfold tailWord_2887704
  simp only [CollatzResearch.WordTrace]
  refine ⟨52661608765174531712099083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70215478353566042282798777 52661608765174531712099083)
  ·
    refine ⟨78992413147761797568148625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52661608765174531712099083 78992413147761797568148625)
    ·
      refine ⟨59244309860821348176111469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78992413147761797568148625 59244309860821348176111469)
      ·
        refine ⟨22216616197808005566041801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59244309860821348176111469 22216616197808005566041801)
        ·
          refine ⟨16662462148356004174531351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22216616197808005566041801 16662462148356004174531351)
          ·
            refine ⟨24993693222534006261797027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16662462148356004174531351 24993693222534006261797027)
            ·
              refine ⟨37490539833801009392695541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24993693222534006261797027 37490539833801009392695541)
              ·
                refine ⟨3514738109418844630565207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37490539833801009392695541 3514738109418844630565207)
                ·
                  refine ⟨5272107164128266945847811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514738109418844630565207 5272107164128266945847811)
                  ·
                    refine ⟨7908160746192400418771717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5272107164128266945847811 7908160746192400418771717)
                    ·
                      refine ⟨1482780139911075078519697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7908160746192400418771717 1482780139911075078519697)
                      ·
                        rfl

theorem cell23_2887704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_2887704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887704 prefixEnd_2887704 := by exact prefixLift 2887704
  have htrace : WordTrace (prefixWord ++ tailWord_2887704) baseStart_2887704 baseEnd_2887704 := by
    simpa [prefixWord, tailWord_2887704, baseEnd_2887704] using wordTrace_append hprefix tailTrace_2887704
  have hstable : (prefixWord ++ tailWord_2887704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887704).length < 2 ^ (prefixWord ++ tailWord_2887704).sum := by decide
  have hdescent : baseEnd_2887704 < baseStart_2887704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887714 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2887714 : Nat := 118140960795 + 2887714 * 2 ^ 59
def prefixEnd_2887714 : Nat := 4983230072969 + 3 ^ 40 * 2887714 * 2
def baseEnd_2887714 : Nat := 494261758239206679798217

theorem tailTrace_2887714 : CollatzResearch.WordTrace tailWord_2887714 prefixEnd_2887714 494261758239206679798217 := by
  unfold tailWord_2887714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26330895565078208783015549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70215721506875223421374797 26330895565078208783015549)
  ·
    refine ⟨9874085836904328293630831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26330895565078208783015549 9874085836904328293630831)
    ·
      refine ⟨14811128755356492440446247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874085836904328293630831 14811128755356492440446247)
      ·
        refine ⟨22216693133034738660669371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14811128755356492440446247 22216693133034738660669371)
        ·
          refine ⟨33325039699552107991004057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22216693133034738660669371 33325039699552107991004057)
          ·
            refine ⟨24993779774664080993253043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33325039699552107991004057 24993779774664080993253043)
            ·
              refine ⟨37490669661996121489879565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24993779774664080993253043 37490669661996121489879565)
              ·
                refine ⟨14059001123248545558704837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37490669661996121489879565 14059001123248545558704837)
                ·
                  refine ⟨2636062710609102292257157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14059001123248545558704837 2636062710609102292257157)
                  ·
                    refine ⟨494261758239206679798217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636062710609102292257157 494261758239206679798217)
                    ·
                      rfl

theorem cell23_2887714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2887714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887714 prefixEnd_2887714 := by exact prefixLift 2887714
  have htrace : WordTrace (prefixWord ++ tailWord_2887714) baseStart_2887714 baseEnd_2887714 := by
    simpa [prefixWord, tailWord_2887714, baseEnd_2887714] using wordTrace_append hprefix tailTrace_2887714
  have hstable : (prefixWord ++ tailWord_2887714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887714).length < 2 ^ (prefixWord ++ tailWord_2887714).sum := by decide
  have hdescent : baseEnd_2887714 < baseStart_2887714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887717 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2887717 : Nat := 118140960795 + 2887717 * 2 ^ 59
def prefixEnd_2887717 : Nat := 4983230072969 + 3 ^ 40 * 2887717 * 2
def baseEnd_2887717 : Nat := 1482786815159583527657137

theorem tailTrace_2887717 : CollatzResearch.WordTrace tailWord_2887717 prefixEnd_2887717 1482786815159583527657137 := by
  unfold tailWord_2887717
  simp only [CollatzResearch.WordTrace]
  refine ⟨105323691679301966644421405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70215794452867977762947603 105323691679301966644421405)
  ·
    refine ⟨39496384379738237491658027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105323691679301966644421405 39496384379738237491658027)
    ·
      refine ⟨59244576569607356237487041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39496384379738237491658027 59244576569607356237487041)
      ·
        refine ⟨44433432427205517178115281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59244576569607356237487041 44433432427205517178115281)
        ·
          refine ⟨33325074320404137883586461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44433432427205517178115281 33325074320404137883586461)
          ·
            refine ⟨12496902870151551706344923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33325074320404137883586461 12496902870151551706344923)
            ·
              refine ⟨18745354305227327559517385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12496902870151551706344923 18745354305227327559517385)
              ·
                refine ⟨14059015728920495669638039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18745354305227327559517385 14059015728920495669638039)
                ·
                  refine ⟨21088523593380743504457059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14059015728920495669638039 21088523593380743504457059)
                  ·
                    refine ⟨31632785390071115256685589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21088523593380743504457059 31632785390071115256685589)
                    ·
                      refine ⟨1482786815159583527657137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31632785390071115256685589 1482786815159583527657137)
                      ·
                        rfl

theorem cell23_2887717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2887717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887717 prefixEnd_2887717 := by exact prefixLift 2887717
  have htrace : WordTrace (prefixWord ++ tailWord_2887717) baseStart_2887717 baseEnd_2887717 := by
    simpa [prefixWord, tailWord_2887717, baseEnd_2887717] using wordTrace_append hprefix tailTrace_2887717
  have hstable : (prefixWord ++ tailWord_2887717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887717).length < 2 ^ (prefixWord ++ tailWord_2887717).sum := by decide
  have hdescent : baseEnd_2887717 < baseStart_2887717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887731 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 2, 4]
def baseStart_2887731 : Nat := 118140960795 + 2887731 * 2 ^ 59
def prefixEnd_2887731 : Nat := 4983230072969 + 3 ^ 40 * 2887731 * 2
def baseEnd_2887731 : Nat := 494264667962915490960691

theorem tailTrace_2887731 : CollatzResearch.WordTrace tailWord_2887731 prefixEnd_2887731 494264667962915490960691 := by
  unfold tailWord_2887731
  simp only [CollatzResearch.WordTrace]
  refine ⟨105324202301251247035431047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70216134867500831356954031 105324202301251247035431047)
  ·
    refine ⟨157986303451876870553146571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105324202301251247035431047 157986303451876870553146571)
    ·
      refine ⟨236979455177815305829719857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157986303451876870553146571 236979455177815305829719857)
      ·
        refine ⟨177734591383361479372289893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236979455177815305829719857 177734591383361479372289893)
        ·
          refine ⟨33325235884380277382304355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177734591383361479372289893 33325235884380277382304355)
          ·
            refine ⟨49987853826570416073456533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33325235884380277382304355 49987853826570416073456533)
            ·
              refine ⟨2343180648120488253443275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49987853826570416073456533 2343180648120488253443275)
              ·
                refine ⟨3514770972180732380164913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343180648120488253443275 3514770972180732380164913)
                ·
                  refine ⟨2636078229135549285123685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514770972180732380164913 2636078229135549285123685)
                  ·
                    refine ⟨494264667962915490960691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636078229135549285123685 494264667962915490960691)
                    ·
                      rfl

theorem cell23_2887731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 4].length) (baseStart_2887731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887731 prefixEnd_2887731 := by exact prefixLift 2887731
  have htrace : WordTrace (prefixWord ++ tailWord_2887731) baseStart_2887731 baseEnd_2887731 := by
    simpa [prefixWord, tailWord_2887731, baseEnd_2887731] using wordTrace_append hprefix tailTrace_2887731
  have hstable : (prefixWord ++ tailWord_2887731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887731).length < 2 ^ (prefixWord ++ tailWord_2887731).sum := by decide
  have hdescent : baseEnd_2887731 < baseStart_2887731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887734 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2887734 : Nat := 118140960795 + 2887734 * 2 ^ 59
def prefixEnd_2887734 : Nat := 4983230072969 + 3 ^ 40 * 2887734 * 2
def baseEnd_2887734 : Nat := 1482795544330709961144559

theorem tailTrace_2887734 : CollatzResearch.WordTrace tailWord_2887734 prefixEnd_2887734 1482795544330709961144559 := by
  unfold tailWord_2887734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582769482515023659236891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70216207813493585698526837 6582769482515023659236891)
  ·
    refine ⟨9874154223772535488855337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582769482515023659236891 9874154223772535488855337)
    ·
      refine ⟨7405615667829401616641503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9874154223772535488855337 7405615667829401616641503)
      ·
        refine ⟨11108423501744102424962255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7405615667829401616641503 11108423501744102424962255)
        ·
          refine ⟨16662635252616153637443383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11108423501744102424962255 16662635252616153637443383)
          ·
            refine ⟨24993952878924230456165075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16662635252616153637443383 24993952878924230456165075)
            ·
              refine ⟨37490929318386345684247613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24993952878924230456165075 37490929318386345684247613)
              ·
                refine ⟨14059098494394879631592855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37490929318386345684247613 14059098494394879631592855)
                ·
                  refine ⟨21088647741592319447389283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14059098494394879631592855 21088647741592319447389283)
                  ·
                    refine ⟨31632971612388479171083925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21088647741592319447389283 31632971612388479171083925)
                    ·
                      refine ⟨1482795544330709961144559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31632971612388479171083925 1482795544330709961144559)
                      ·
                        rfl

theorem cell23_2887734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2887734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887734 prefixEnd_2887734 := by exact prefixLift 2887734
  have htrace : WordTrace (prefixWord ++ tailWord_2887734) baseStart_2887734 baseEnd_2887734 := by
    simpa [prefixWord, tailWord_2887734, baseEnd_2887734] using wordTrace_append hprefix tailTrace_2887734
  have hstable : (prefixWord ++ tailWord_2887734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887734).length < 2 ^ (prefixWord ++ tailWord_2887734).sum := by decide
  have hdescent : baseEnd_2887734 < baseStart_2887734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887758 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_2887758 : Nat := 118140960795 + 2887758 * 2 ^ 59
def prefixEnd_2887758 : Nat := 4983230072969 + 3 ^ 40 * 2887758 * 2
def baseEnd_2887758 : Nat := 1482807867866417867244449

theorem tailTrace_2887758 : CollatzResearch.WordTrace tailWord_2887758 prefixEnd_2887758 1482807867866417867244449 := by
  unfold tailWord_2887758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13165648384019178830832991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70216791381435620431109285 13165648384019178830832991)
  ·
    refine ⟨19748472576028768246249487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13165648384019178830832991 19748472576028768246249487)
    ·
      refine ⟨29622708864043152369374231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19748472576028768246249487 29622708864043152369374231)
      ·
        refine ⟨44434063296064728554061347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29622708864043152369374231 44434063296064728554061347)
        ·
          refine ⟨66651094944097092831092021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44434063296064728554061347 66651094944097092831092021)
          ·
            refine ⟨6248540151009102452914877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66651094944097092831092021 6248540151009102452914877)
            ·
              refine ⟨2343202556628413419843079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6248540151009102452914877 2343202556628413419843079)
              ·
                refine ⟨3514803834942620129764619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343202556628413419843079 3514803834942620129764619)
                ·
                  refine ⟨5272205752413930194646929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514803834942620129764619 5272205752413930194646929)
                  ·
                    refine ⟨3954154314310447645985197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272205752413930194646929 3954154314310447645985197)
                    ·
                      refine ⟨1482807867866417867244449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954154314310447645985197 1482807867866417867244449)
                      ·
                        rfl

theorem cell23_2887758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_2887758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887758 prefixEnd_2887758 := by exact prefixLift 2887758
  have htrace : WordTrace (prefixWord ++ tailWord_2887758) baseStart_2887758 baseEnd_2887758 := by
    simpa [prefixWord, tailWord_2887758, baseEnd_2887758] using wordTrace_append hprefix tailTrace_2887758
  have hstable : (prefixWord ++ tailWord_2887758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887758).length < 2 ^ (prefixWord ++ tailWord_2887758).sum := by decide
  have hdescent : baseEnd_2887758 < baseStart_2887758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887767 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2887767 : Nat := 118140960795 + 2887767 * 2 ^ 59
def prefixEnd_2887767 : Nat := 4983230072969 + 3 ^ 40 * 2887767 * 2
def baseEnd_2887767 : Nat := 1482812489192308332031907

theorem tailTrace_2887767 : CollatzResearch.WordTrace tailWord_2887767 prefixEnd_2887767 1482812489192308332031907 := by
  unfold tailWord_2887767
  simp only [CollatzResearch.WordTrace]
  refine ⟨105325515329120825183741555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70217010219413883455827703 105325515329120825183741555)
  ·
    refine ⟨157988272993681237775612333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105325515329120825183741555 157988272993681237775612333)
    ·
      refine ⟨59245602372630464165854625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157988272993681237775612333 59245602372630464165854625)
      ·
        refine ⟨44434201779472848124390969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59245602372630464165854625 44434201779472848124390969)
        ·
          refine ⟨33325651334604636093293227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44434201779472848124390969 33325651334604636093293227)
          ·
            refine ⟨49988477001906954139939841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33325651334604636093293227 49988477001906954139939841)
            ·
              refine ⟨37491357751430215604954881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49988477001906954139939841 37491357751430215604954881)
              ·
                refine ⟨28118518313572661703716161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37491357751430215604954881 28118518313572661703716161)
                ·
                  refine ⟨21088888735179496277787121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28118518313572661703716161 21088888735179496277787121)
                  ·
                    refine ⟨15816666551384622208340341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21088888735179496277787121 15816666551384622208340341)
                    ·
                      refine ⟨1482812489192308332031907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15816666551384622208340341 1482812489192308332031907)
                      ·
                        rfl

theorem cell23_2887767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2887767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887767 prefixEnd_2887767 := by exact prefixLift 2887767
  have htrace : WordTrace (prefixWord ++ tailWord_2887767) baseStart_2887767 baseEnd_2887767 := by
    simpa [prefixWord, tailWord_2887767, baseEnd_2887767] using wordTrace_append hprefix tailTrace_2887767
  have hstable : (prefixWord ++ tailWord_2887767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887767).length < 2 ^ (prefixWord ++ tailWord_2887767).sum := by decide
  have hdescent : baseEnd_2887767 < baseStart_2887767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887772 : List Nat := [2, 2, 4, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_2887772 : Nat := 118140960795 + 2887772 * 2 ^ 59
def prefixEnd_2887772 : Nat := 4983230072969 + 3 ^ 40 * 2887772 * 2
def baseEnd_2887772 : Nat := 1482815056595580812469385

theorem tailTrace_2887772 : CollatzResearch.WordTrace tailWord_2887772 prefixEnd_2887772 1482815056595580812469385 := by
  unfold tailWord_2887772
  simp only [CollatzResearch.WordTrace]
  refine ⟨52662848847051355518836785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70217131796068474025115713 52662848847051355518836785)
  ·
    refine ⟨39497136635288516639127589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52662848847051355518836785 39497136635288516639127589)
    ·
      refine ⟨7405713119116596869836423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39497136635288516639127589 7405713119116596869836423)
      ·
        refine ⟨11108569678674895304754635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7405713119116596869836423 11108569678674895304754635)
        ·
          refine ⟨16662854518012342957131953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11108569678674895304754635 16662854518012342957131953)
          ·
            refine ⟨12497140888509257217848965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16662854518012342957131953 12497140888509257217848965)
            ·
              refine ⟨2343213916595485728346681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12497140888509257217848965 2343213916595485728346681)
              ·
                refine ⟨1757410437446614296260011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343213916595485728346681 1757410437446614296260011)
                ·
                  refine ⟨2636115656169921444390017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757410437446614296260011 2636115656169921444390017)
                  ·
                    refine ⟨1977086742127441083292513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2636115656169921444390017 1977086742127441083292513)
                    ·
                      refine ⟨1482815056595580812469385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977086742127441083292513 1482815056595580812469385)
                      ·
                        rfl

theorem cell23_2887772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_2887772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887772 prefixEnd_2887772 := by exact prefixLift 2887772
  have htrace : WordTrace (prefixWord ++ tailWord_2887772) baseStart_2887772 baseEnd_2887772 := by
    simpa [prefixWord, tailWord_2887772, baseEnd_2887772] using wordTrace_append hprefix tailTrace_2887772
  have hstable : (prefixWord ++ tailWord_2887772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887772).length < 2 ^ (prefixWord ++ tailWord_2887772).sum := by decide
  have hdescent : baseEnd_2887772 < baseStart_2887772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887778 : List Nat := [3, 3, 2, 2, 3, 1, 1, 8]
def baseStart_2887778 : Nat := 118140960795 + 2887778 * 2 ^ 59
def prefixEnd_2887778 : Nat := 4983230072969 + 3 ^ 40 * 2887778 * 2
def baseEnd_2887778 : Nat := 54919190277018806999791

theorem tailTrace_2887778 : CollatzResearch.WordTrace tailWord_2887778 prefixEnd_2887778 54919190277018806999791 := by
  unfold tailWord_2887778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26331479133020243515597997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70217277688053982708261325 26331479133020243515597997)
  ·
    refine ⟨9874304674882591318349249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26331479133020243515597997 9874304674882591318349249)
    ·
      refine ⟨7405728506161943488761937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9874304674882591318349249 7405728506161943488761937)
      ·
        refine ⟨5554296379621457616571453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7405728506161943488761937 5554296379621457616571453)
        ·
          refine ⟨2082861142358046606214295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5554296379621457616571453 2082861142358046606214295)
          ·
            refine ⟨3124291713537069909321443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082861142358046606214295 3124291713537069909321443)
            ·
              refine ⟨4686437570305604863982165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124291713537069909321443 4686437570305604863982165)
              ·
                refine ⟨54919190277018806999791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4686437570305604863982165 54919190277018806999791)
                ·
                  rfl

theorem cell23_2887778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_2887778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887778 prefixEnd_2887778 := by exact prefixLift 2887778
  have htrace : WordTrace (prefixWord ++ tailWord_2887778) baseStart_2887778 baseEnd_2887778 := by
    simpa [prefixWord, tailWord_2887778, baseEnd_2887778] using wordTrace_append hprefix tailTrace_2887778
  have hstable : (prefixWord ++ tailWord_2887778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887778).length < 2 ^ (prefixWord ++ tailWord_2887778).sum := by decide
  have hdescent : baseEnd_2887778 < baseStart_2887778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887781 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 3, 3, 2]
def baseStart_2887781 : Nat := 118140960795 + 2887781 * 2 ^ 59
def prefixEnd_2887781 : Nat := 4983230072969 + 3 ^ 40 * 2887781 * 2
def baseEnd_2887781 : Nat := 1482819677921471277256843

theorem tailTrace_2887781 : CollatzResearch.WordTrace tailWord_2887781 prefixEnd_2887781 1482819677921471277256843 := by
  unfold tailWord_2887781
  simp only [CollatzResearch.WordTrace]
  refine ⟨105326025951070105574751197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70217350634046737049834131 105326025951070105574751197)
  ·
    refine ⟨39497259731651289590531699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105326025951070105574751197 39497259731651289590531699)
    ·
      refine ⟨59245889597476934385797549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39497259731651289590531699 59245889597476934385797549)
      ·
        refine ⟨22217208599053850394674081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59245889597476934385797549 22217208599053850394674081)
        ·
          refine ⟨16662906449290387796005561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22217208599053850394674081 16662906449290387796005561)
          ·
            refine ⟨12497179836967790847004171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16662906449290387796005561 12497179836967790847004171)
            ·
              refine ⟨18745769755451686270506257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12497179836967790847004171 18745769755451686270506257)
              ·
                refine ⟨14059327316588764702879693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18745769755451686270506257 14059327316588764702879693)
                ·
                  refine ⟨5272247743720786763579885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14059327316588764702879693 5272247743720786763579885)
                  ·
                    refine ⟨1977092903895295036342457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5272247743720786763579885 1977092903895295036342457)
                    ·
                      refine ⟨1482819677921471277256843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977092903895295036342457 1482819677921471277256843)
                      ·
                        rfl

theorem cell23_2887781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_2887781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887781 prefixEnd_2887781 := by exact prefixLift 2887781
  have htrace : WordTrace (prefixWord ++ tailWord_2887781) baseStart_2887781 baseEnd_2887781 := by
    simpa [prefixWord, tailWord_2887781, baseEnd_2887781] using wordTrace_append hprefix tailTrace_2887781
  have hstable : (prefixWord ++ tailWord_2887781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887781).length < 2 ^ (prefixWord ++ tailWord_2887781).sum := by decide
  have hdescent : baseEnd_2887781 < baseStart_2887781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887798 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2887798 : Nat := 118140960795 + 2887798 * 2 ^ 59
def prefixEnd_2887798 : Nat := 4983230072969 + 3 ^ 40 * 2887798 * 2
def baseEnd_2887798 : Nat := 1482828407092597710744265

theorem tailTrace_2887798 : CollatzResearch.WordTrace tailWord_2887798 prefixEnd_2887798 1482828407092597710744265 := by
  unfold tailWord_2887798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582915374500532342382503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70217763994672344985413365 6582915374500532342382503)
  ·
    refine ⟨9874373061750798513573755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582915374500532342382503 9874373061750798513573755)
    ·
      refine ⟨14811559592626197770360633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874373061750798513573755 14811559592626197770360633)
      ·
        refine ⟨11108669694469648327770475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14811559592626197770360633 11108669694469648327770475)
        ·
          refine ⟨16663004541704472491655713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11108669694469648327770475 16663004541704472491655713)
          ·
            refine ⟨12497253406278354368741785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16663004541704472491655713 12497253406278354368741785)
            ·
              refine ⟨9372940054708765776556339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12497253406278354368741785 9372940054708765776556339)
              ·
                refine ⟨14059410082063148664834509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9372940054708765776556339 14059410082063148664834509)
                ·
                  refine ⟨5272278780773680749312941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14059410082063148664834509 5272278780773680749312941)
                  ·
                    refine ⟨1977104542790130280992353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5272278780773680749312941 1977104542790130280992353)
                    ·
                      refine ⟨1482828407092597710744265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977104542790130280992353 1482828407092597710744265)
                      ·
                        rfl

theorem cell23_2887798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2887798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887798 prefixEnd_2887798 := by exact prefixLift 2887798
  have htrace : WordTrace (prefixWord ++ tailWord_2887798) baseStart_2887798 baseEnd_2887798 := by
    simpa [prefixWord, tailWord_2887798, baseEnd_2887798] using wordTrace_append hprefix tailTrace_2887798
  have hstable : (prefixWord ++ tailWord_2887798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887798).length < 2 ^ (prefixWord ++ tailWord_2887798).sum := by decide
  have hdescent : baseEnd_2887798 < baseStart_2887798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887811 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 1, 4, 2]
def baseStart_2887811 : Nat := 118140960795 + 2887811 * 2 ^ 59
def prefixEnd_2887811 : Nat := 4983230072969 + 3 ^ 40 * 2887811 * 2
def baseEnd_2887811 : Nat := 1482835082341106159881705

theorem tailTrace_2887811 : CollatzResearch.WordTrace tailWord_2887811 prefixEnd_2887811 1482835082341106159881705 := by
  unfold tailWord_2887811
  simp only [CollatzResearch.WordTrace]
  refine ⟨105327120140961420698343287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70218080093974280465562191 105327120140961420698343287)
  ·
    refine ⟨157990680211442131047514931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105327120140961420698343287 157990680211442131047514931)
    ·
      refine ⟨236986020317163196571272397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157990680211442131047514931 236986020317163196571272397)
      ·
        refine ⟨88869757618936198714227149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236986020317163196571272397 88869757618936198714227149)
        ·
          refine ⟨33326159107101074517835181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88869757618936198714227149 33326159107101074517835181)
          ·
            refine ⟨12497309665162902944188193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33326159107101074517835181 12497309665162902944188193)
            ·
              refine ⟨9372982248872177208141145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12497309665162902944188193 9372982248872177208141145)
              ·
                refine ⟨7029736686654132906105859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9372982248872177208141145 7029736686654132906105859)
                ·
                  refine ⟨10544605029981199359158789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029736686654132906105859 10544605029981199359158789)
                  ·
                    refine ⟨1977113443121474879842273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10544605029981199359158789 1977113443121474879842273)
                    ·
                      refine ⟨1482835082341106159881705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977113443121474879842273 1482835082341106159881705)
                      ·
                        rfl

theorem cell23_2887811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_2887811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887811 prefixEnd_2887811 := by exact prefixLift 2887811
  have htrace : WordTrace (prefixWord ++ tailWord_2887811) baseStart_2887811 baseEnd_2887811 := by
    simpa [prefixWord, tailWord_2887811, baseEnd_2887811] using wordTrace_append hprefix tailTrace_2887811
  have hstable : (prefixWord ++ tailWord_2887811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887811).length < 2 ^ (prefixWord ++ tailWord_2887811).sum := by decide
  have hdescent : baseEnd_2887811 < baseStart_2887811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887817 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 9]
def baseStart_2887817 : Nat := 118140960795 + 2887817 * 2 ^ 59
def prefixEnd_2887817 : Nat := 4983230072969 + 3 ^ 40 * 2887817 * 2
def baseEnd_2887817 : Nat := 164759795913892570711853

theorem tailTrace_2887817 : CollatzResearch.WordTrace tailWord_2887817 prefixEnd_2887817 164759795913892570711853 := by
  unfold tailWord_2887817
  simp only [CollatzResearch.WordTrace]
  refine ⟨105327338978939683723061705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70218225985959789148707803 105327338978939683723061705)
  ·
    refine ⟨78995504234204762792296279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105327338978939683723061705 78995504234204762792296279)
    ·
      refine ⟨118493256351307144188444419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78995504234204762792296279 118493256351307144188444419)
      ·
        refine ⟨177739884526960716282666629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118493256351307144188444419 177739884526960716282666629)
        ·
          refine ⟨33326228348805134302999993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177739884526960716282666629 33326228348805134302999993)
          ·
            refine ⟨24994671261603850727249995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33326228348805134302999993 24994671261603850727249995)
            ·
              refine ⟨37492006892405776090874993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24994671261603850727249995 37492006892405776090874993)
              ·
                refine ⟨28119005169304332068156245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37492006892405776090874993 28119005169304332068156245)
                ·
                  refine ⟨164759795913892570711853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28119005169304332068156245 164759795913892570711853)
                  ·
                    rfl

theorem cell23_2887817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_2887817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887817 prefixEnd_2887817 := by exact prefixLift 2887817
  have htrace : WordTrace (prefixWord ++ tailWord_2887817) baseStart_2887817 baseEnd_2887817 := by
    simpa [prefixWord, tailWord_2887817, baseEnd_2887817] using wordTrace_append hprefix tailTrace_2887817
  have hstable : (prefixWord ++ tailWord_2887817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887817).length < 2 ^ (prefixWord ++ tailWord_2887817).sum := by decide
  have hdescent : baseEnd_2887817 < baseStart_2887817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887822 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2887822 : Nat := 118140960795 + 2887822 * 2 ^ 59
def prefixEnd_2887822 : Nat := 4983230072969 + 3 ^ 40 * 2887822 * 2
def baseEnd_2887822 : Nat := 1482840730628305616844155

theorem tailTrace_2887822 : CollatzResearch.WordTrace tailWord_2887822 prefixEnd_2887822 1482840730628305616844155 := by
  unfold tailWord_2887822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13165940167990196197124215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70218347562614379717995813 13165940167990196197124215)
  ·
    refine ⟨19748910251985294295686323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13165940167990196197124215 19748910251985294295686323)
    ·
      refine ⟨29623365377977941443529485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19748910251985294295686323 29623365377977941443529485)
      ·
        refine ⟨11108762016741728041323557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29623365377977941443529485 11108762016741728041323557)
        ·
          refine ⟨2082892878139074007748167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11108762016741728041323557 2082892878139074007748167)
          ·
            refine ⟨3124339317208611011622251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082892878139074007748167 3124339317208611011622251)
            ·
              refine ⟨4686508975812916517433377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124339317208611011622251 4686508975812916517433377)
              ·
                refine ⟨3514881731859687388075033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686508975812916517433377 3514881731859687388075033)
                ·
                  refine ⟨2636161298894765541056275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514881731859687388075033 2636161298894765541056275)
                  ·
                    refine ⟨3954241948342148311584413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636161298894765541056275 3954241948342148311584413)
                    ·
                      refine ⟨1482840730628305616844155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954241948342148311584413 1482840730628305616844155)
                      ·
                        rfl

theorem cell23_2887822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2887822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887822 prefixEnd_2887822 := by exact prefixLift 2887822
  have htrace : WordTrace (prefixWord ++ tailWord_2887822) baseStart_2887822 baseEnd_2887822 := by
    simpa [prefixWord, tailWord_2887822, baseEnd_2887822] using wordTrace_append hprefix tailTrace_2887822
  have hstable : (prefixWord ++ tailWord_2887822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887822).length < 2 ^ (prefixWord ++ tailWord_2887822).sum := by decide
  have hdescent : baseEnd_2887822 < baseStart_2887822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887845 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 2, 2, 2]
def baseStart_2887845 : Nat := 118140960795 + 2887845 * 2 ^ 59
def prefixEnd_2887845 : Nat := 4983230072969 + 3 ^ 40 * 2887845 * 2
def baseEnd_2887845 : Nat := 1482852540683359026856549

theorem tailTrace_2887845 : CollatzResearch.WordTrace tailWord_2887845 prefixEnd_2887845 1482852540683359026856549 := by
  unfold tailWord_2887845
  simp only [CollatzResearch.WordTrace]
  refine ⟨105328360222838244505080989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70218906815225496336720659 105328360222838244505080989)
  ·
    refine ⟨39498135083564341689405371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105328360222838244505080989 39498135083564341689405371)
    ·
      refine ⟨59247202625346512534108057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39498135083564341689405371 59247202625346512534108057)
      ·
        refine ⟨44435401969009884400581043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59247202625346512534108057 44435401969009884400581043)
        ·
          refine ⟨66653102953514826600871565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44435401969009884400581043 66653102953514826600871565)
          ·
            refine ⟨24994913607568059975326837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66653102953514826600871565 24994913607568059975326837)
            ·
              refine ⟨2343273150709505622686891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24994913607568059975326837 2343273150709505622686891)
              ·
                refine ⟨3514909726064258434030337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343273150709505622686891 3514909726064258434030337)
                ·
                  refine ⟨2636182294548193825522753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3514909726064258434030337 2636182294548193825522753)
                  ·
                    refine ⟨1977136720911145369142065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2636182294548193825522753 1977136720911145369142065)
                    ·
                      refine ⟨1482852540683359026856549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977136720911145369142065 1482852540683359026856549)
                      ·
                        rfl

theorem cell23_2887845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_2887845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887845 prefixEnd_2887845 := by exact prefixLift 2887845
  have htrace : WordTrace (prefixWord ++ tailWord_2887845) baseStart_2887845 baseEnd_2887845 := by
    simpa [prefixWord, tailWord_2887845, baseEnd_2887845] using wordTrace_append hprefix tailTrace_2887845
  have hstable : (prefixWord ++ tailWord_2887845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887845).length < 2 ^ (prefixWord ++ tailWord_2887845).sum := by decide
  have hdescent : baseEnd_2887845 < baseStart_2887845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887864 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 2, 5]
def baseStart_2887864 : Nat := 118140960795 + 2887864 * 2 ^ 59
def prefixEnd_2887864 : Nat := 4983230072969 + 3 ^ 40 * 2887864 * 2
def baseEnd_2887864 : Nat := 494287432271931484172987

theorem tailTrace_2887864 : CollatzResearch.WordTrace tailWord_2887864 prefixEnd_2887864 494287432271931484172987 := by
  unfold tailWord_2887864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52664526604884705375011323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70219368806512940500015097 52664526604884705375011323)
  ·
    refine ⟨78996789907327058062516985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52664526604884705375011323 78996789907327058062516985)
    ·
      refine ⟨59247592430495293546887739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78996789907327058062516985 59247592430495293546887739)
      ·
        refine ⟨88871388645742940320331609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59247592430495293546887739 88871388645742940320331609)
        ·
          refine ⟨66653541484307205240248707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88871388645742940320331609 66653541484307205240248707)
          ·
            refine ⟨99980312226460807860373061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66653541484307205240248707 99980312226460807860373061)
            ·
              refine ⟨18746308542461401473819949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99980312226460807860373061 18746308542461401473819949)
              ·
                refine ⟨7029865703423025552682481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18746308542461401473819949 7029865703423025552682481)
                ·
                  refine ⟨5272399277567269164511861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7029865703423025552682481 5272399277567269164511861)
                  ·
                    refine ⟨494287432271931484172987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5272399277567269164511861 494287432271931484172987)
                    ·
                      rfl

theorem cell23_2887864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_2887864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887864 prefixEnd_2887864 := by exact prefixLift 2887864
  have htrace : WordTrace (prefixWord ++ tailWord_2887864) baseStart_2887864 baseEnd_2887864 := by
    simpa [prefixWord, tailWord_2887864, baseEnd_2887864] using wordTrace_append hprefix tailTrace_2887864
  have hstable : (prefixWord ++ tailWord_2887864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887864).length < 2 ^ (prefixWord ++ tailWord_2887864).sum := by decide
  have hdescent : baseEnd_2887864 < baseStart_2887864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887921 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_2887921 : Nat := 118140960795 + 2887921 * 2 ^ 59
def prefixEnd_2887921 : Nat := 4983230072969 + 3 ^ 40 * 2887921 * 2
def baseEnd_2887921 : Nat := 1482891565213100729506199

theorem tailTrace_2887921 : CollatzResearch.WordTrace tailWord_2887921 prefixEnd_2887921 1482891565213100729506199 := by
  unfold tailWord_2887921
  simp only [CollatzResearch.WordTrace]
  refine ⟨105331132170562909484847617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70220754780375272989898411 105331132170562909484847617)
  ·
    refine ⟨78998349127922182113635713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105331132170562909484847617 78998349127922182113635713)
    ·
      refine ⟨59248761845941636585226785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78998349127922182113635713 59248761845941636585226785)
      ·
        refine ⟨44436571384456227438920089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59248761845941636585226785 44436571384456227438920089)
        ·
          refine ⟨33327428538342170579190067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44436571384456227438920089 33327428538342170579190067)
          ·
            refine ⟨49991142807513255868785101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33327428538342170579190067 49991142807513255868785101)
            ·
              refine ⟨18746678552817470950794413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49991142807513255868785101 18746678552817470950794413)
              ·
                refine ⟨7030004457306551606547905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18746678552817470950794413 7030004457306551606547905)
                ·
                  refine ⟨5272503342979913704910929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7030004457306551606547905 5272503342979913704910929)
                  ·
                    refine ⟨3954377507234935278683197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272503342979913704910929 3954377507234935278683197)
                    ·
                      refine ⟨1482891565213100729506199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954377507234935278683197 1482891565213100729506199)
                      ·
                        rfl

theorem cell23_2887921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_2887921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887921 prefixEnd_2887921 := by exact prefixLift 2887921
  have htrace : WordTrace (prefixWord ++ tailWord_2887921) baseStart_2887921 baseEnd_2887921 := by
    simpa [prefixWord, tailWord_2887921, baseEnd_2887921] using wordTrace_append hprefix tailTrace_2887921
  have hstable : (prefixWord ++ tailWord_2887921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887921).length < 2 ^ (prefixWord ++ tailWord_2887921).sum := by decide
  have hdescent : baseEnd_2887921 < baseStart_2887921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887945 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 1, 4]
def baseStart_2887945 : Nat := 118140960795 + 2887945 * 2 ^ 59
def prefixEnd_2887945 : Nat := 4983230072969 + 3 ^ 40 * 2887945 * 2
def baseEnd_2887945 : Nat := 494301296249602878535363

theorem tailTrace_2887945 : CollatzResearch.WordTrace tailWord_2887945 prefixEnd_2887945 494301296249602878535363 := by
  unfold tailWord_2887945
  simp only [CollatzResearch.WordTrace]
  refine ⟨105332007522475961583721289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70221338348317307722480859 105332007522475961583721289)
  ·
    refine ⟨78999005641856971187790967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105332007522475961583721289 78999005641856971187790967)
    ·
      refine ⟨118498508462785456781686451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78999005641856971187790967 118498508462785456781686451)
      ·
        refine ⟨177747762694178185172529677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118498508462785456781686451 177747762694178185172529677)
        ·
          refine ⟨66655411010316819439698629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177747762694178185172529677 66655411010316819439698629)
          ·
            refine ⟨12497889564434403644943493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66655411010316819439698629 12497889564434403644943493)
            ·
              refine ⟨2343354293331450683426905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12497889564434403644943493 2343354293331450683426905)
              ·
                refine ⟨1757515719998588012570179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343354293331450683426905 1757515719998588012570179)
                ·
                  refine ⟨2636273579997882018855269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757515719998588012570179 2636273579997882018855269)
                  ·
                    refine ⟨494301296249602878535363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636273579997882018855269 494301296249602878535363)
                    ·
                      rfl

theorem cell23_2887945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 4].length) (baseStart_2887945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887945 prefixEnd_2887945 := by exact prefixLift 2887945
  have htrace : WordTrace (prefixWord ++ tailWord_2887945) baseStart_2887945 baseEnd_2887945 := by
    simpa [prefixWord, tailWord_2887945, baseEnd_2887945] using wordTrace_append hprefix tailTrace_2887945
  have hstable : (prefixWord ++ tailWord_2887945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887945).length < 2 ^ (prefixWord ++ tailWord_2887945).sum := by decide
  have hdescent : baseEnd_2887945 < baseStart_2887945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887951 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 3]
def baseStart_2887951 : Nat := 118140960795 + 2887951 * 2 ^ 59
def prefixEnd_2887951 : Nat := 4983230072969 + 3 ^ 40 * 2887951 * 2
def baseEnd_2887951 : Nat := 1482906969632735612131061

theorem tailTrace_2887951 : CollatzResearch.WordTrace tailWord_2887951 prefixEnd_2887951 1482906969632735612131061 := by
  unfold tailWord_2887951
  simp only [CollatzResearch.WordTrace]
  refine ⟨105332226360454224608439707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70221484240302816405626471 105332226360454224608439707)
  ·
    refine ⟨157998339540681336912659561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105332226360454224608439707 157998339540681336912659561)
    ·
      refine ⟨118498754655511002684494671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157998339540681336912659561 118498754655511002684494671)
      ·
        refine ⟨177748131983266504026742007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118498754655511002684494671 177748131983266504026742007)
        ·
          refine ⟨266622197974899756040113011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177748131983266504026742007 266622197974899756040113011)
          ·
            refine ⟨399933296962349634060169517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266622197974899756040113011 399933296962349634060169517)
            ·
              refine ⟨149974986360881112772563569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399933296962349634060169517 149974986360881112772563569)
              ·
                refine ⟨112481239770660834579422677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149974986360881112772563569 112481239770660834579422677)
                ·
                  refine ⟨2636279057124863310455219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112481239770660834579422677 2636279057124863310455219)
                  ·
                    refine ⟨3954418585687294965682829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636279057124863310455219 3954418585687294965682829)
                    ·
                      refine ⟨1482906969632735612131061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954418585687294965682829 1482906969632735612131061)
                      ·
                        rfl

theorem cell23_2887951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 1, 3].length) (baseStart_2887951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887951 prefixEnd_2887951 := by exact prefixLift 2887951
  have htrace : WordTrace (prefixWord ++ tailWord_2887951) baseStart_2887951 baseEnd_2887951 := by
    simpa [prefixWord, tailWord_2887951, baseEnd_2887951] using wordTrace_append hprefix tailTrace_2887951
  have hstable : (prefixWord ++ tailWord_2887951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887951).length < 2 ^ (prefixWord ++ tailWord_2887951).sum := by decide
  have hdescent : baseEnd_2887951 < baseStart_2887951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887964 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2887964 : Nat := 118140960795 + 2887964 * 2 ^ 59
def prefixEnd_2887964 : Nat := 4983230072969 + 3 ^ 40 * 2887964 * 2
def baseEnd_2887964 : Nat := 1482913644881244061268501

theorem tailTrace_2887964 : CollatzResearch.WordTrace tailWord_2887964 prefixEnd_2887964 1482913644881244061268501 := by
  unfold tailWord_2887964
  simp only [CollatzResearch.WordTrace]
  refine ⟨52666350254703563914331473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70221800339604751885775297 52666350254703563914331473)
  ·
    refine ⟨39499762691027672935748605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52666350254703563914331473 39499762691027672935748605)
    ·
      refine ⟨14812411009135377350905727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39499762691027672935748605 14812411009135377350905727)
      ·
        refine ⟨22218616513703066026358591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812411009135377350905727 22218616513703066026358591)
        ·
          refine ⟨33327924770554599039537887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22218616513703066026358591 33327924770554599039537887)
          ·
            refine ⟨49991887155831898559306831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33327924770554599039537887 49991887155831898559306831)
            ·
              refine ⟨74987830733747847838960247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49991887155831898559306831 74987830733747847838960247)
              ·
                refine ⟨112481746100621771758440371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74987830733747847838960247 112481746100621771758440371)
                ·
                  refine ⟨168722619150932657637660557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112481746100621771758440371 168722619150932657637660557)
                  ·
                    refine ⟨63270982181599746614122709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168722619150932657637660557 63270982181599746614122709)
                    ·
                      refine ⟨1482913644881244061268501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63270982181599746614122709 1482913644881244061268501)
                      ·
                        rfl

theorem cell23_2887964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2887964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887964 prefixEnd_2887964 := by exact prefixLift 2887964
  have htrace : WordTrace (prefixWord ++ tailWord_2887964) baseStart_2887964 baseEnd_2887964 := by
    simpa [prefixWord, tailWord_2887964, baseEnd_2887964] using wordTrace_append hprefix tailTrace_2887964
  have hstable : (prefixWord ++ tailWord_2887964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887964).length < 2 ^ (prefixWord ++ tailWord_2887964).sum := by decide
  have hdescent : baseEnd_2887964 < baseStart_2887964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887968 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 5, 1, 3]
def baseStart_2887968 : Nat := 118140960795 + 2887968 * 2 ^ 59
def prefixEnd_2887968 : Nat := 4983230072969 + 3 ^ 40 * 2887968 * 2
def baseEnd_2887968 : Nat := 1482915698803862045618483

theorem tailTrace_2887968 : CollatzResearch.WordTrace tailWord_2887968 prefixEnd_2887968 1482915698803862045618483 := by
  unfold tailWord_2887968
  simp only [CollatzResearch.WordTrace]
  refine ⟨52666423200696318255904279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70221897600928424341205705 52666423200696318255904279)
  ·
    refine ⟨78999634801044477383856419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52666423200696318255904279 78999634801044477383856419)
    ·
      refine ⟨118499452201566716075784629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78999634801044477383856419 118499452201566716075784629)
      ·
        refine ⟨11109323643896879632104809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118499452201566716075784629 11109323643896879632104809)
        ·
          refine ⟨8331992732922659724078607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11109323643896879632104809 8331992732922659724078607)
          ·
            refine ⟨12497989099383989586117911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331992732922659724078607 12497989099383989586117911)
            ·
              refine ⟨18746983649075984379176867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12497989099383989586117911 18746983649075984379176867)
              ·
                refine ⟨28120475473613976568765301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18746983649075984379176867 28120475473613976568765301)
                ·
                  refine ⟨2636294575651310303321747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28120475473613976568765301 2636294575651310303321747)
                  ·
                    refine ⟨3954441863476965454982621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636294575651310303321747 3954441863476965454982621)
                    ·
                      refine ⟨1482915698803862045618483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954441863476965454982621 1482915698803862045618483)
                      ·
                        rfl

theorem cell23_2887968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_2887968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887968 prefixEnd_2887968 := by exact prefixLift 2887968
  have htrace : WordTrace (prefixWord ++ tailWord_2887968) baseStart_2887968 baseEnd_2887968 := by
    simpa [prefixWord, tailWord_2887968, baseEnd_2887968] using wordTrace_append hprefix tailTrace_2887968
  have hstable : (prefixWord ++ tailWord_2887968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887968).length < 2 ^ (prefixWord ++ tailWord_2887968).sum := by decide
  have hdescent : baseEnd_2887968 < baseStart_2887968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887971 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 1, 5]
def baseStart_2887971 : Nat := 118140960795 + 2887971 * 2 ^ 59
def prefixEnd_2887971 : Nat := 4983230072969 + 3 ^ 40 * 2887971 * 2
def baseEnd_2887971 : Nat := 494305746415275177960323

theorem tailTrace_2887971 : CollatzResearch.WordTrace tailWord_2887971 prefixEnd_2887971 494305746415275177960323 := by
  unfold tailWord_2887971
  simp only [CollatzResearch.WordTrace]
  refine ⟨105332955820381768024167767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70221970546921178682778511 105332955820381768024167767)
  ·
    refine ⟨157999433730572652036251651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105332955820381768024167767 157999433730572652036251651)
    ·
      refine ⟨236999150595858978054377477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157999433730572652036251651 236999150595858978054377477)
      ·
        refine ⟨44437340736723558385195777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236999150595858978054377477 44437340736723558385195777)
        ·
          refine ⟨33328005552542668788896833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44437340736723558385195777 33328005552542668788896833)
          ·
            refine ⟨24996004164407001591672625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33328005552542668788896833 24996004164407001591672625)
            ·
              refine ⟨18747003123305251193754469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24996004164407001591672625 18747003123305251193754469)
              ·
                refine ⟨3515063085619734598828963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18747003123305251193754469 3515063085619734598828963)
                ·
                  refine ⟨5272594628429601898243445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515063085619734598828963 5272594628429601898243445)
                  ·
                    refine ⟨494305746415275177960323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5272594628429601898243445 494305746415275177960323)
                    ·
                      rfl

theorem cell23_2887971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 5].length) (baseStart_2887971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887971 prefixEnd_2887971 := by exact prefixLift 2887971
  have htrace : WordTrace (prefixWord ++ tailWord_2887971) baseStart_2887971 baseEnd_2887971 := by
    simpa [prefixWord, tailWord_2887971, baseEnd_2887971] using wordTrace_append hprefix tailTrace_2887971
  have hstable : (prefixWord ++ tailWord_2887971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887971).length < 2 ^ (prefixWord ++ tailWord_2887971).sum := by decide
  have hdescent : baseEnd_2887971 < baseStart_2887971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887984 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 3, 6]
def baseStart_2887984 : Nat := 118140960795 + 2887984 * 2 ^ 59
def prefixEnd_2887984 : Nat := 4983230072969 + 3 ^ 40 * 2887984 * 2
def baseEnd_2887984 : Nat := 494307971498111327672803

theorem tailTrace_2887984 : CollatzResearch.WordTrace tailWord_2887984 prefixEnd_2887984 494307971498111327672803 := by
  unfold tailWord_2887984
  simp only [CollatzResearch.WordTrace]
  refine ⟨52666714984667335622195503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70222286646223114162927337 52666714984667335622195503)
  ·
    refine ⟨79000072477001003433293255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52666714984667335622195503 79000072477001003433293255)
    ·
      refine ⟨118500108715501505149939883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79000072477001003433293255 118500108715501505149939883)
      ·
        refine ⟨177750163073252257724909825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118500108715501505149939883 177750163073252257724909825)
        ·
          refine ⟨133312622304939193293682369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177750163073252257724909825 133312622304939193293682369)
          ·
            refine ⟨99984466728704394970261777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133312622304939193293682369 99984466728704394970261777)
            ·
              refine ⟨74988350046528296227696333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99984466728704394970261777 74988350046528296227696333)
              ·
                refine ⟨28120631267448111085386125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74988350046528296227696333 28120631267448111085386125)
                ·
                  refine ⟨10545236725293041657019797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28120631267448111085386125 10545236725293041657019797)
                  ·
                    refine ⟨494307971498111327672803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10545236725293041657019797 494307971498111327672803)
                    ·
                      rfl

theorem cell23_2887984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_2887984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887984 prefixEnd_2887984 := by exact prefixLift 2887984
  have htrace : WordTrace (prefixWord ++ tailWord_2887984) baseStart_2887984 baseEnd_2887984 := by
    simpa [prefixWord, tailWord_2887984, baseEnd_2887984] using wordTrace_append hprefix tailTrace_2887984
  have hstable : (prefixWord ++ tailWord_2887984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887984).length < 2 ^ (prefixWord ++ tailWord_2887984).sum := by decide
  have hdescent : baseEnd_2887984 < baseStart_2887984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887991 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 8, 2]
def baseStart_2887991 : Nat := 118140960795 + 2887991 * 2 ^ 59
def prefixEnd_2887991 : Nat := 4983230072969 + 3 ^ 40 * 2887991 * 2
def baseEnd_2887991 : Nat := 1482927508858915455630877

theorem tailTrace_2887991 : CollatzResearch.WordTrace tailWord_2887991 prefixEnd_2887991 1482927508858915455630877 := by
  unfold tailWord_2887991
  simp only [CollatzResearch.WordTrace]
  refine ⟨105333685280309311439895827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70222456853539540959930551 105333685280309311439895827)
  ·
    refine ⟨158000527920463967159843741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105333685280309311439895827 158000527920463967159843741)
    ·
      refine ⟨59250197970173987684941403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158000527920463967159843741 59250197970173987684941403)
      ·
        refine ⟨88875296955260981527412105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59250197970173987684941403 88875296955260981527412105)
        ·
          refine ⟨66656472716445736145559079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88875296955260981527412105 66656472716445736145559079)
          ·
            refine ⟨99984709074668604218338619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66656472716445736145559079 99984709074668604218338619)
            ·
              refine ⟨149977063612002906327507929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99984709074668604218338619 149977063612002906327507929)
              ·
                refine ⟨112482797709002179745630947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149977063612002906327507929 112482797709002179745630947)
                ·
                  refine ⟨168724196563503269618446421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112482797709002179745630947 168724196563503269618446421)
                  ·
                    refine ⟨1977236678478553940841169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 168724196563503269618446421 1977236678478553940841169)
                    ·
                      refine ⟨1482927508858915455630877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977236678478553940841169 1482927508858915455630877)
                      ·
                        rfl

theorem cell23_2887991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_2887991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2887991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2887991 prefixEnd_2887991 := by exact prefixLift 2887991
  have htrace : WordTrace (prefixWord ++ tailWord_2887991) baseStart_2887991 baseEnd_2887991 := by
    simpa [prefixWord, tailWord_2887991, baseEnd_2887991] using wordTrace_append hprefix tailTrace_2887991
  have hstable : (prefixWord ++ tailWord_2887991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887991).length < 2 ^ (prefixWord ++ tailWord_2887991).sum := by decide
  have hdescent : baseEnd_2887991 < baseStart_2887991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888011 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 3]
def baseStart_2888011 : Nat := 118140960795 + 2888011 * 2 ^ 59
def prefixEnd_2888011 : Nat := 4983230072969 + 3 ^ 40 * 2888011 * 2
def baseEnd_2888011 : Nat := 1482937778472005377380785

theorem tailTrace_2888011 : CollatzResearch.WordTrace tailWord_2888011 prefixEnd_2888011 1482937778472005377380785 := by
  unfold tailWord_2888011
  simp only [CollatzResearch.WordTrace]
  refine ⟨105334414740236854855623887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70222943160157903237082591 105334414740236854855623887)
  ·
    refine ⟨158001622110355282283435831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105334414740236854855623887 158001622110355282283435831)
    ·
      refine ⟨237002433165532923425153747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158001622110355282283435831 237002433165532923425153747)
      ·
        refine ⟨355503649748299385137730621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237002433165532923425153747 355503649748299385137730621)
        ·
          refine ⟨133313868655612269426648983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355503649748299385137730621 133313868655612269426648983)
          ·
            refine ⟨199970802983418404139973475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133313868655612269426648983 199970802983418404139973475)
            ·
              refine ⟨299956204475127606209960213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199970802983418404139973475 299956204475127606209960213)
              ·
                refine ⟨14060447084771606541091885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 299956204475127606209960213 14060447084771606541091885)
                ·
                  refine ⟨5272667656789352452909457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14060447084771606541091885 5272667656789352452909457)
                  ·
                    refine ⟨3954500742592014339682093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272667656789352452909457 3954500742592014339682093)
                    ·
                      refine ⟨1482937778472005377380785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954500742592014339682093 1482937778472005377380785)
                      ·
                        rfl

theorem cell23_2888011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 3].length) (baseStart_2888011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888011 prefixEnd_2888011 := by exact prefixLift 2888011
  have htrace : WordTrace (prefixWord ++ tailWord_2888011) baseStart_2888011 baseEnd_2888011 := by
    simpa [prefixWord, tailWord_2888011, baseEnd_2888011] using wordTrace_append hprefix tailTrace_2888011
  have hstable : (prefixWord ++ tailWord_2888011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888011).length < 2 ^ (prefixWord ++ tailWord_2888011).sum := by decide
  have hdescent : baseEnd_2888011 < baseStart_2888011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888018 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_2888018 : Nat := 118140960795 + 2888018 * 2 ^ 59
def prefixEnd_2888018 : Nat := 4983230072969 + 3 ^ 40 * 2888018 * 2
def baseEnd_2888018 : Nat := 494313790945528949997751

theorem tailTrace_2888018 : CollatzResearch.WordTrace tailWord_2888018 prefixEnd_2888018 494313790945528949997751 := by
  unfold tailWord_2888018
  simp only [CollatzResearch.WordTrace]
  refine ⟨26333667512802873762782177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70223113367474330034085805 26333667512802873762782177)
  ·
    refine ⟨19750250634602155322086633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26333667512802873762782177 19750250634602155322086633)
    ·
      refine ⟨14812687975951616491564975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19750250634602155322086633 14812687975951616491564975)
      ·
        refine ⟨22219031963927424737347463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812687975951616491564975 22219031963927424737347463)
        ·
          refine ⟨33328547945891137106021195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22219031963927424737347463 33328547945891137106021195)
          ·
            refine ⟨49992821918836705659031793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33328547945891137106021195 49992821918836705659031793)
            ·
              refine ⟨37494616439127529244273845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49992821918836705659031793 37494616439127529244273845)
              ·
                refine ⟨3515120291168205866650673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37494616439127529244273845 3515120291168205866650673)
                ·
                  refine ⟨2636340218376154399988005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515120291168205866650673 2636340218376154399988005)
                  ·
                    refine ⟨494313790945528949997751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636340218376154399988005 494313790945528949997751)
                    ·
                      rfl

theorem cell23_2888018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_2888018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888018 prefixEnd_2888018 := by exact prefixLift 2888018
  have htrace : WordTrace (prefixWord ++ tailWord_2888018) baseStart_2888018 baseEnd_2888018 := by
    simpa [prefixWord, tailWord_2888018, baseEnd_2888018] using wordTrace_append hprefix tailTrace_2888018
  have hstable : (prefixWord ++ tailWord_2888018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888018).length < 2 ^ (prefixWord ++ tailWord_2888018).sum := by decide
  have hdescent : baseEnd_2888018 < baseStart_2888018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888030 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2888030 : Nat := 118140960795 + 2888030 * 2 ^ 59
def prefixEnd_2888030 : Nat := 4983230072969 + 3 ^ 40 * 2888030 * 2
def baseEnd_2888030 : Nat := 494315844868146934347733

theorem tailTrace_2888030 : CollatzResearch.WordTrace tailWord_2888030 prefixEnd_2888030 494315844868146934347733 := by
  unfold tailWord_2888030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166888465896002637570693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70223405151445347400377029 13166888465896002637570693)
  ·
    refine ⟨2468791587355500494544505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13166888465896002637570693 2468791587355500494544505)
    ·
      refine ⟨1851593690516625370908379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2468791587355500494544505 1851593690516625370908379)
      ·
        refine ⟨2777390535774938056362569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851593690516625370908379 2777390535774938056362569)
        ·
          refine ⟨2083042901831203542271927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2777390535774938056362569 2083042901831203542271927)
          ·
            refine ⟨3124564352746805313407891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083042901831203542271927 3124564352746805313407891)
            ·
              refine ⟨4686846529120207970111837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124564352746805313407891 4686846529120207970111837)
              ·
                refine ⟨1757567448420077988791939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4686846529120207970111837 1757567448420077988791939)
                ·
                  refine ⟨2636351172630116983187909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757567448420077988791939 2636351172630116983187909)
                  ·
                    refine ⟨494315844868146934347733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636351172630116983187909 494315844868146934347733)
                    ·
                      rfl

theorem cell23_2888030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2888030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888030 prefixEnd_2888030 := by exact prefixLift 2888030
  have htrace : WordTrace (prefixWord ++ tailWord_2888030) baseStart_2888030 baseEnd_2888030 := by
    simpa [prefixWord, tailWord_2888030, baseEnd_2888030] using wordTrace_append hprefix tailTrace_2888030
  have hstable : (prefixWord ++ tailWord_2888030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888030).length < 2 ^ (prefixWord ++ tailWord_2888030).sum := by decide
  have hdescent : baseEnd_2888030 < baseStart_2888030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888031 : List Nat := [1, 1, 2, 3, 1, 2, 6, 7]
def baseStart_2888031 : Nat := 118140960795 + 2888031 * 2 ^ 59
def prefixEnd_2888031 : Nat := 4983230072969 + 3 ^ 40 * 2888031 * 2
def baseEnd_2888031 : Nat := 54924001780929455523359

theorem tailTrace_2888031 : CollatzResearch.WordTrace tailWord_2888031 prefixEnd_2888031 54924001780929455523359 := by
  unfold tailWord_2888031
  simp only [CollatzResearch.WordTrace]
  refine ⟨105335144200164398271351947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70223429466776265514234631 105335144200164398271351947)
  ·
    refine ⟨158002716300246597407027921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105335144200164398271351947 158002716300246597407027921)
    ·
      refine ⟨118502037225184948055270941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158002716300246597407027921 118502037225184948055270941)
      ·
        refine ⟨44438263959444355520726603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118502037225184948055270941 44438263959444355520726603)
        ·
          refine ⟨66657395939166533281089905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44438263959444355520726603 66657395939166533281089905)
          ·
            refine ⟨49993046954374899960817429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66657395939166533281089905 49993046954374899960817429)
            ·
              refine ⟨2343424075986323435663317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49993046954374899960817429 2343424075986323435663317)
              ·
                refine ⟨54924001780929455523359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2343424075986323435663317 54924001780929455523359)
                ·
                  rfl

theorem cell23_2888031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 7].length) (baseStart_2888031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888031 prefixEnd_2888031 := by exact prefixLift 2888031
  have htrace : WordTrace (prefixWord ++ tailWord_2888031) baseStart_2888031 baseEnd_2888031 := by
    simpa [prefixWord, tailWord_2888031, baseEnd_2888031] using wordTrace_append hprefix tailTrace_2888031
  have hstable : (prefixWord ++ tailWord_2888031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888031).length < 2 ^ (prefixWord ++ tailWord_2888031).sum := by decide
  have hdescent : baseEnd_2888031 < baseStart_2888031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888041 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_2888041 : Nat := 118140960795 + 2888041 * 2 ^ 59
def prefixEnd_2888041 : Nat := 4983230072969 + 3 ^ 40 * 2888041 * 2
def baseEnd_2888041 : Nat := 1482953182891640260005647

theorem tailTrace_2888041 : CollatzResearch.WordTrace tailWord_2888041 prefixEnd_2888041 1482953182891640260005647 := by
  unfold tailWord_2888041
  simp only [CollatzResearch.WordTrace]
  refine ⟨105335508930128169979215977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70223672620085446652810651 105335508930128169979215977)
  ·
    refine ⟨79001631697596127484411983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105335508930128169979215977 79001631697596127484411983)
    ·
      refine ⟨118502447546394191226617975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79001631697596127484411983 118502447546394191226617975)
      ·
        refine ⟨177753671319591286839926963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118502447546394191226617975 177753671319591286839926963)
        ·
          refine ⟨266630506979386930259890445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177753671319591286839926963 266630506979386930259890445)
          ·
            refine ⟨99986440117270098847458917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266630506979386930259890445 99986440117270098847458917)
            ·
              refine ⟨18747457521988143533898547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99986440117270098847458917 18747457521988143533898547)
              ·
                refine ⟨28121186282982215300847821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18747457521988143533898547 28121186282982215300847821)
                ·
                  refine ⟨10545444856118330737817933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28121186282982215300847821 10545444856118330737817933)
                  ·
                    refine ⟨3954541821044374026681725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10545444856118330737817933 3954541821044374026681725)
                    ·
                      refine ⟨1482953182891640260005647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954541821044374026681725 1482953182891640260005647)
                      ·
                        rfl

theorem cell23_2888041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_2888041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888041 prefixEnd_2888041 := by exact prefixLift 2888041
  have htrace : WordTrace (prefixWord ++ tailWord_2888041) baseStart_2888041 baseEnd_2888041 := by
    simpa [prefixWord, tailWord_2888041, baseEnd_2888041] using wordTrace_append hprefix tailTrace_2888041
  have hstable : (prefixWord ++ tailWord_2888041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888041).length < 2 ^ (prefixWord ++ tailWord_2888041).sum := by decide
  have hdescent : baseEnd_2888041 < baseStart_2888041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888059 : List Nat := [1, 1, 1, 1, 1, 8, 3, 2, 1, 2, 2]
def baseStart_2888059 : Nat := 118140960795 + 2888059 * 2 ^ 59
def prefixEnd_2888059 : Nat := 4983230072969 + 3 ^ 40 * 2888059 * 2
def baseEnd_2888059 : Nat := 1482962425543421189580565

theorem tailTrace_2888059 : CollatzResearch.WordTrace tailWord_2888059 prefixEnd_2888059 1482962425543421189580565 := by
  unfold tailWord_2888059
  simp only [CollatzResearch.WordTrace]
  refine ⟨105336165444062959053371231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70224110296041972702247487 105336165444062959053371231)
  ·
    refine ⟨158004248166094438580056847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105336165444062959053371231 158004248166094438580056847)
    ·
      refine ⟨237006372249141657870085271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158004248166094438580056847 237006372249141657870085271)
      ·
        refine ⟨355509558373712486805127907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237006372249141657870085271 355509558373712486805127907)
        ·
          refine ⟨533264337560568730207691861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355509558373712486805127907 533264337560568730207691861)
          ·
            refine ⟨6249191455787914807121389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 533264337560568730207691861 6249191455787914807121389)
            ·
              refine ⟨2343446795920468052670521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6249191455787914807121389 2343446795920468052670521)
              ·
                refine ⟨1757585096940351039502891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343446795920468052670521 1757585096940351039502891)
                ·
                  refine ⟨2636377645410526559254337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757585096940351039502891 2636377645410526559254337)
                  ·
                    refine ⟨1977283234057894919440753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2636377645410526559254337 1977283234057894919440753)
                    ·
                      refine ⟨1482962425543421189580565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977283234057894919440753 1482962425543421189580565)
                      ·
                        rfl

theorem cell23_2888059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 2, 2].length) (baseStart_2888059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888059 prefixEnd_2888059 := by exact prefixLift 2888059
  have htrace : WordTrace (prefixWord ++ tailWord_2888059) baseStart_2888059 baseEnd_2888059 := by
    simpa [prefixWord, tailWord_2888059, baseEnd_2888059] using wordTrace_append hprefix tailTrace_2888059
  have hstable : (prefixWord ++ tailWord_2888059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888059).length < 2 ^ (prefixWord ++ tailWord_2888059).sum := by decide
  have hdescent : baseEnd_2888059 < baseStart_2888059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888075 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 3]
def baseStart_2888075 : Nat := 118140960795 + 2888075 * 2 ^ 59
def prefixEnd_2888075 : Nat := 4983230072969 + 3 ^ 40 * 2888075 * 2
def baseEnd_2888075 : Nat := 1482970641233893126980491

theorem tailTrace_2888075 : CollatzResearch.WordTrace tailWord_2888075 prefixEnd_2888075 1482970641233893126980491 := by
  unfold tailWord_2888075
  simp only [CollatzResearch.WordTrace]
  refine ⟨105336749012004993785953679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70224499341336662523969119 105336749012004993785953679)
  ·
    refine ⟨158005123518007490678930519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105336749012004993785953679 158005123518007490678930519)
    ·
      refine ⟨237007685277011236018395779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158005123518007490678930519 237007685277011236018395779)
      ·
        refine ⟨355511527915516854027593669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237007685277011236018395779 355511527915516854027593669)
        ·
          refine ⟨66658411484159410130173813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355511527915516854027593669 66658411484159410130173813)
          ·
            refine ⟨6249226076639944699703795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66658411484159410130173813 6249226076639944699703795)
            ·
              refine ⟨9373839114959917049555693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6249226076639944699703795 9373839114959917049555693)
              ·
                refine ⟨3515189668109968893583385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9373839114959917049555693 3515189668109968893583385)
                ·
                  refine ⟨2636392251082476670187539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515189668109968893583385 2636392251082476670187539)
                  ·
                    refine ⟨3954588376623715005281309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636392251082476670187539 3954588376623715005281309)
                    ·
                      refine ⟨1482970641233893126980491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954588376623715005281309 1482970641233893126980491)
                      ·
                        rfl

theorem cell23_2888075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 1, 3].length) (baseStart_2888075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888075 prefixEnd_2888075 := by exact prefixLift 2888075
  have htrace : WordTrace (prefixWord ++ tailWord_2888075) baseStart_2888075 baseEnd_2888075 := by
    simpa [prefixWord, tailWord_2888075, baseEnd_2888075] using wordTrace_append hprefix tailTrace_2888075
  have hstable : (prefixWord ++ tailWord_2888075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888075).length < 2 ^ (prefixWord ++ tailWord_2888075).sum := by decide
  have hdescent : baseEnd_2888075 < baseStart_2888075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888101 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2888101 : Nat := 118140960795 + 2888101 * 2 ^ 59
def prefixEnd_2888101 : Nat := 4983230072969 + 3 ^ 40 * 2888101 * 2
def baseEnd_2888101 : Nat := 1482983991730910025255371

theorem tailTrace_2888101 : CollatzResearch.WordTrace tailWord_2888101 prefixEnd_2888101 1482983991730910025255371 := by
  unfold tailWord_2888101
  simp only [CollatzResearch.WordTrace]
  refine ⟨105337697309910800226400157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70225131539940533484266771 105337697309910800226400157)
  ·
    refine ⟨39501636491216550084900059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105337697309910800226400157 39501636491216550084900059)
    ·
      refine ⟨59252454736824825127350089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39501636491216550084900059 59252454736824825127350089)
      ·
        refine ⟨44439341052618618845512567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59252454736824825127350089 44439341052618618845512567)
        ·
          refine ⟨66659011578927928268268851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44439341052618618845512567 66659011578927928268268851)
          ·
            refine ⟨99988517368391892402403277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66659011578927928268268851 99988517368391892402403277)
            ·
              refine ⟨37495694013146959650901229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99988517368391892402403277 37495694013146959650901229)
              ·
                refine ⟨14060885254930109869087961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37495694013146959650901229 14060885254930109869087961)
                ·
                  refine ⟨10545663941197582401815971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14060885254930109869087961 10545663941197582401815971)
                  ·
                    refine ⟨15818495911796373602723957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10545663941197582401815971 15818495911796373602723957)
                    ·
                      refine ⟨1482983991730910025255371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15818495911796373602723957 1482983991730910025255371)
                      ·
                        rfl

theorem cell23_2888101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2888101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888101 prefixEnd_2888101 := by exact prefixLift 2888101
  have htrace : WordTrace (prefixWord ++ tailWord_2888101) baseStart_2888101 baseEnd_2888101 := by
    simpa [prefixWord, tailWord_2888101, baseEnd_2888101] using wordTrace_append hprefix tailTrace_2888101
  have hstable : (prefixWord ++ tailWord_2888101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888101).length < 2 ^ (prefixWord ++ tailWord_2888101).sum := by decide
  have hdescent : baseEnd_2888101 < baseStart_2888101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888109 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2888109 : Nat := 118140960795 + 2888109 * 2 ^ 59
def prefixEnd_2888109 : Nat := 4983230072969 + 3 ^ 40 * 2888109 * 2
def baseEnd_2888109 : Nat := 1482988099576145993955335

theorem tailTrace_2888109 : CollatzResearch.WordTrace tailWord_2888109 prefixEnd_2888109 1482988099576145993955335 := by
  unfold tailWord_2888109
  simp only [CollatzResearch.WordTrace]
  refine ⟨105337989093881817592691381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70225326062587878395127587 105337989093881817592691381)
  ·
    refine ⟨9875436477551420399314817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105337989093881817592691381 9875436477551420399314817)
    ·
      refine ⟨7406577358163565299486113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9875436477551420399314817 7406577358163565299486113)
      ·
        refine ⟨5554933018622673974614585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7406577358163565299486113 5554933018622673974614585)
        ·
          refine ⟨4166199763967005480960939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5554933018622673974614585 4166199763967005480960939)
          ·
            refine ⟨6249299645950508221441409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166199763967005480960939 6249299645950508221441409)
            ·
              refine ⟨4686974734462881166081057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6249299645950508221441409 4686974734462881166081057)
              ·
                refine ⟨3515231050847160874560793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686974734462881166081057 3515231050847160874560793)
                ·
                  refine ⟨2636423288135370655920595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515231050847160874560793 2636423288135370655920595)
                  ·
                    refine ⟨3954634932203055983880893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636423288135370655920595 3954634932203055983880893)
                    ·
                      refine ⟨1482988099576145993955335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954634932203055983880893 1482988099576145993955335)
                      ·
                        rfl

theorem cell23_2888109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2888109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888109 prefixEnd_2888109 := by exact prefixLift 2888109
  have htrace : WordTrace (prefixWord ++ tailWord_2888109) baseStart_2888109 baseEnd_2888109 := by
    simpa [prefixWord, tailWord_2888109, baseEnd_2888109] using wordTrace_append hprefix tailTrace_2888109
  have hstable : (prefixWord ++ tailWord_2888109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888109).length < 2 ^ (prefixWord ++ tailWord_2888109).sum := by decide
  have hdescent : baseEnd_2888109 < baseStart_2888109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888201 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_2888201 : Nat := 118140960795 + 2888201 * 2 ^ 59
def prefixEnd_2888201 : Nat := 4983230072969 + 3 ^ 40 * 2888201 * 2
def baseEnd_2888201 : Nat := 1483035339796359634004911

theorem tailTrace_2888201 : CollatzResearch.WordTrace tailWord_2888201 prefixEnd_2888201 1483035339796359634004911 := by
  unfold tailWord_2888201
  simp only [CollatzResearch.WordTrace]
  refine ⟨105341344609548517305040457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70227563073032344870026971 105341344609548517305040457)
  ·
    refine ⟨79006008457161387978780343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105341344609548517305040457 79006008457161387978780343)
    ·
      refine ⟨118509012685742081968170515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79006008457161387978780343 118509012685742081968170515)
      ·
        refine ⟨177763519028613122952255773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118509012685742081968170515 177763519028613122952255773)
        ·
          refine ⟨66661319635729921107095915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177763519028613122952255773 66661319635729921107095915)
          ·
            refine ⟨99991979453594881660643873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66661319635729921107095915 99991979453594881660643873)
            ·
              refine ⟨74993984590196161245482905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99991979453594881660643873 74993984590196161245482905)
              ·
                refine ⟨56245488442647120934112179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74993984590196161245482905 56245488442647120934112179)
                ·
                  refine ⟨84368232663970681401168269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56245488442647120934112179 84368232663970681401168269)
                  ·
                    refine ⟨31638087248989005525438101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84368232663970681401168269 31638087248989005525438101)
                    ·
                      refine ⟨1483035339796359634004911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31638087248989005525438101 1483035339796359634004911)
                      ·
                        rfl

theorem cell23_2888201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_2888201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888201 prefixEnd_2888201 := by exact prefixLift 2888201
  have htrace : WordTrace (prefixWord ++ tailWord_2888201) baseStart_2888201 baseEnd_2888201 := by
    simpa [prefixWord, tailWord_2888201, baseEnd_2888201] using wordTrace_append hprefix tailTrace_2888201
  have hstable : (prefixWord ++ tailWord_2888201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888201).length < 2 ^ (prefixWord ++ tailWord_2888201).sum := by decide
  have hdescent : baseEnd_2888201 < baseStart_2888201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888211 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 10]
def baseStart_2888211 : Nat := 118140960795 + 2888211 * 2 ^ 59
def prefixEnd_2888211 : Nat := 4983230072969 + 3 ^ 40 * 2888211 * 2
def baseEnd_2888211 : Nat := 164782274955878288319985

theorem tailTrace_2888211 : CollatzResearch.WordTrace tailWord_2888211 prefixEnd_2888211 164782274955878288319985 := by
  unfold tailWord_2888211
  simp only [CollatzResearch.WordTrace]
  refine ⟨105341709339512289012904487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70227806226341526008602991 105341709339512289012904487)
  ·
    refine ⟨158012564009268433519356731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105341709339512289012904487 158012564009268433519356731)
    ·
      refine ⟨237018846013902650279035097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158012564009268433519356731 237018846013902650279035097)
      ·
        refine ⟨177764134510426987709276323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237018846013902650279035097 177764134510426987709276323)
        ·
          refine ⟨266646201765640481563914485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177764134510426987709276323 266646201765640481563914485)
          ·
            refine ⟨24998081415528795146616983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 266646201765640481563914485 24998081415528795146616983)
            ·
              refine ⟨37497122123293192719925475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24998081415528795146616983 37497122123293192719925475)
              ·
                refine ⟨56245683184939789079888213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37497122123293192719925475 56245683184939789079888213)
                ·
                  refine ⟨164782274955878288319985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56245683184939789079888213 164782274955878288319985)
                  ·
                    rfl

theorem cell23_2888211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 10].length) (baseStart_2888211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888211 prefixEnd_2888211 := by exact prefixLift 2888211
  have htrace : WordTrace (prefixWord ++ tailWord_2888211) baseStart_2888211 baseEnd_2888211 := by
    simpa [prefixWord, tailWord_2888211, baseEnd_2888211] using wordTrace_append hprefix tailTrace_2888211
  have hstable : (prefixWord ++ tailWord_2888211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888211).length < 2 ^ (prefixWord ++ tailWord_2888211).sum := by decide
  have hdescent : baseEnd_2888211 < baseStart_2888211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888225 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2888225 : Nat := 118140960795 + 2888225 * 2 ^ 59
def prefixEnd_2888225 : Nat := 4983230072969 + 3 ^ 40 * 2888225 * 2
def baseEnd_2888225 : Nat := 1483047663332067540104801

theorem tailTrace_2888225 : CollatzResearch.WordTrace tailWord_2888225 prefixEnd_2888225 1483047663332067540104801 := by
  unfold tailWord_2888225
  simp only [CollatzResearch.WordTrace]
  refine ⟨105342219961461569403914129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70228146640974379602609419 105342219961461569403914129)
  ·
    refine ⟨79006664971096177052935597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105342219961461569403914129 79006664971096177052935597)
    ·
      refine ⟨29627499364161066394850849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79006664971096177052935597 29627499364161066394850849)
      ·
        refine ⟨22220624523120799796138137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29627499364161066394850849 22220624523120799796138137)
        ·
          refine ⟨16665468392340599847103603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22220624523120799796138137 16665468392340599847103603)
          ·
            refine ⟨24998202588510899770655405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16665468392340599847103603 24998202588510899770655405)
            ·
              refine ⟨9374325970691587413995777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24998202588510899770655405 9374325970691587413995777)
              ·
                refine ⟨7030744478018690560496833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9374325970691587413995777 7030744478018690560496833)
                ·
                  refine ⟨5273058358514017920372625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7030744478018690560496833 5273058358514017920372625)
                  ·
                    refine ⟨3954793768885513440279469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273058358514017920372625 3954793768885513440279469)
                    ·
                      refine ⟨1483047663332067540104801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954793768885513440279469 1483047663332067540104801)
                      ·
                        rfl

theorem cell23_2888225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2888225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888225 prefixEnd_2888225 := by exact prefixLift 2888225
  have htrace : WordTrace (prefixWord ++ tailWord_2888225) baseStart_2888225 baseEnd_2888225 := by
    simpa [prefixWord, tailWord_2888225, baseEnd_2888225] using wordTrace_append hprefix tailTrace_2888225
  have hstable : (prefixWord ++ tailWord_2888225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888225).length < 2 ^ (prefixWord ++ tailWord_2888225).sum := by decide
  have hdescent : baseEnd_2888225 < baseStart_2888225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888232 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2888232 : Nat := 118140960795 + 2888232 * 2 ^ 59
def prefixEnd_2888232 : Nat := 4983230072969 + 3 ^ 40 * 2888232 * 2
def baseEnd_2888232 : Nat := 494350419232216337572423

theorem tailTrace_2888232 : CollatzResearch.WordTrace tailWord_2888232 prefixEnd_2888232 494350419232216337572423 := by
  unfold tailWord_2888232
  simp only [CollatzResearch.WordTrace]
  refine ⟨52671237636218104799709475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70228316848290806399612633 52671237636218104799709475)
  ·
    refine ⟨79006856454327157199564213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52671237636218104799709475 79006856454327157199564213)
    ·
      refine ⟨7406892792593170987459145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79006856454327157199564213 7406892792593170987459145)
      ·
        refine ⟨5555169594444878240594359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7406892792593170987459145 5555169594444878240594359)
        ·
          refine ⟨8332754391667317360891539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555169594444878240594359 8332754391667317360891539)
          ·
            refine ⟨12499131587500976041337309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8332754391667317360891539 12499131587500976041337309)
            ·
              refine ⟨4687174345312866015501491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12499131587500976041337309 4687174345312866015501491)
              ·
                refine ⟨7030761517969299023252237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687174345312866015501491 7030761517969299023252237)
                ·
                  refine ⟨2636535569238487133719589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7030761517969299023252237 2636535569238487133719589)
                  ·
                    refine ⟨494350419232216337572423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2636535569238487133719589 494350419232216337572423)
                    ·
                      rfl

theorem cell23_2888232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2888232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888232 prefixEnd_2888232 := by exact prefixLift 2888232
  have htrace : WordTrace (prefixWord ++ tailWord_2888232) baseStart_2888232 baseEnd_2888232 := by
    simpa [prefixWord, tailWord_2888232, baseEnd_2888232] using wordTrace_append hprefix tailTrace_2888232
  have hstable : (prefixWord ++ tailWord_2888232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888232).length < 2 ^ (prefixWord ++ tailWord_2888232).sum := by decide
  have hdescent : baseEnd_2888232 < baseStart_2888232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888255 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 3]
def baseStart_2888255 : Nat := 118140960795 + 2888255 * 2 ^ 59
def prefixEnd_2888255 : Nat := 4983230072969 + 3 ^ 40 * 2888255 * 2
def baseEnd_2888255 : Nat := 1483063067751702422729663

theorem tailTrace_2888255 : CollatzResearch.WordTrace tailWord_2888255 prefixEnd_2888255 1483063067751702422729663 := by
  unfold tailWord_2888255
  simp only [CollatzResearch.WordTrace]
  refine ⟨105343314151352884527506219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70228876100901923018337479 105343314151352884527506219)
  ·
    refine ⟨158014971227029326791259329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105343314151352884527506219 158014971227029326791259329)
    ·
      refine ⟨118511228420271995093444497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158014971227029326791259329 118511228420271995093444497)
      ·
        refine ⟨88883421315203996320083373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118511228420271995093444497 88883421315203996320083373)
        ·
          refine ⟨33331282993201498620031265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88883421315203996320083373 33331282993201498620031265)
          ·
            refine ⟨24998462244901123965023449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33331282993201498620031265 24998462244901123965023449)
            ·
              refine ⟨18748846683675842973767587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24998462244901123965023449 18748846683675842973767587)
              ·
                refine ⟨28123270025513764460651381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18748846683675842973767587 28123270025513764460651381)
                ·
                  refine ⟨2636556564891915418186067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28123270025513764460651381 2636556564891915418186067)
                  ·
                    refine ⟨3954834847337873127279101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636556564891915418186067 3954834847337873127279101)
                    ·
                      refine ⟨1483063067751702422729663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954834847337873127279101 1483063067751702422729663)
                      ·
                        rfl

theorem cell23_2888255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 1, 3].length) (baseStart_2888255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888255 prefixEnd_2888255 := by exact prefixLift 2888255
  have htrace : WordTrace (prefixWord ++ tailWord_2888255) baseStart_2888255 baseEnd_2888255 := by
    simpa [prefixWord, tailWord_2888255, baseEnd_2888255] using wordTrace_append hprefix tailTrace_2888255
  have hstable : (prefixWord ++ tailWord_2888255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888255).length < 2 ^ (prefixWord ++ tailWord_2888255).sum := by decide
  have hdescent : baseEnd_2888255 < baseStart_2888255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888289 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_2888289 : Nat := 118140960795 + 2888289 * 2 ^ 59
def prefixEnd_2888289 : Nat := 4983230072969 + 3 ^ 40 * 2888289 * 2
def baseEnd_2888289 : Nat := 1483080526093955289704507

theorem tailTrace_2888289 : CollatzResearch.WordTrace tailWord_2888289 prefixEnd_2888289 1483080526093955289704507 := by
  unfold tailWord_2888289
  simp only [CollatzResearch.WordTrace]
  refine ⟨105344554233229708334243921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70229702822153138889495947 105344554233229708334243921)
  ·
    refine ⟨79008415674922281250682941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105344554233229708334243921 79008415674922281250682941)
    ·
      refine ⟨29628155878095855469006103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79008415674922281250682941 29628155878095855469006103)
      ·
        refine ⟨44442233817143783203509155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29628155878095855469006103 44442233817143783203509155)
        ·
          refine ⟨66663350725715674805263733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44442233817143783203509155 66663350725715674805263733)
          ·
            refine ⟨6249689130535844512993475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66663350725715674805263733 6249689130535844512993475)
            ·
              refine ⟨9374533695803766769490213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6249689130535844512993475 9374533695803766769490213)
              ·
                refine ⟨1757725067963206269279415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9374533695803766769490213 1757725067963206269279415)
                ·
                  refine ⟨2636587601944809403919123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757725067963206269279415 2636587601944809403919123)
                  ·
                    refine ⟨3954881402917214105878685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2636587601944809403919123 3954881402917214105878685)
                    ·
                      refine ⟨1483080526093955289704507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954881402917214105878685 1483080526093955289704507)
                      ·
                        rfl

theorem cell23_2888289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_2888289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888289 prefixEnd_2888289 := by exact prefixLift 2888289
  have htrace : WordTrace (prefixWord ++ tailWord_2888289) baseStart_2888289 baseEnd_2888289 := by
    simpa [prefixWord, tailWord_2888289, baseEnd_2888289] using wordTrace_append hprefix tailTrace_2888289
  have hstable : (prefixWord ++ tailWord_2888289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888289).length < 2 ^ (prefixWord ++ tailWord_2888289).sum := by decide
  have hdescent : baseEnd_2888289 < baseStart_2888289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888295 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_2888295 : Nat := 118140960795 + 2888295 * 2 ^ 59
def prefixEnd_2888295 : Nat := 4983230072969 + 3 ^ 40 * 2888295 * 2
def baseEnd_2888295 : Nat := 1483083606977882266229479

theorem tailTrace_2888295 : CollatzResearch.WordTrace tailWord_2888295 prefixEnd_2888295 1483083606977882266229479 := by
  unfold tailWord_2888295
  simp only [CollatzResearch.WordTrace]
  refine ⟨105344773071207971358962339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70229848714138647572641559 105344773071207971358962339)
  ·
    refine ⟨158017159606811957038443509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105344773071207971358962339 158017159606811957038443509)
    ·
      refine ⟨14814108713138620972354079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158017159606811957038443509 14814108713138620972354079)
      ·
        refine ⟨22221163069707931458531119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814108713138620972354079 22221163069707931458531119)
        ·
          refine ⟨33331744604561897187796679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22221163069707931458531119 33331744604561897187796679)
          ·
            refine ⟨49997616906842845781695019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33331744604561897187796679 49997616906842845781695019)
            ·
              refine ⟨74996425360264268672542529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49997616906842845781695019 74996425360264268672542529)
              ·
                refine ⟨56247319020198201504406897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74996425360264268672542529 56247319020198201504406897)
                ·
                  refine ⟨42185489265148651128305173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56247319020198201504406897 42185489265148651128305173)
                  ·
                    refine ⟨1977444809303843021639305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42185489265148651128305173 1977444809303843021639305)
                    ·
                      refine ⟨1483083606977882266229479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977444809303843021639305 1483083606977882266229479)
                      ·
                        rfl

theorem cell23_2888295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_2888295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888295 prefixEnd_2888295 := by exact prefixLift 2888295
  have htrace : WordTrace (prefixWord ++ tailWord_2888295) baseStart_2888295 baseEnd_2888295 := by
    simpa [prefixWord, tailWord_2888295, baseEnd_2888295] using wordTrace_append hprefix tailTrace_2888295
  have hstable : (prefixWord ++ tailWord_2888295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888295).length < 2 ^ (prefixWord ++ tailWord_2888295).sum := by decide
  have hdescent : baseEnd_2888295 < baseStart_2888295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888312 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 3, 2, 2]
def baseStart_2888312 : Nat := 118140960795 + 2888312 * 2 ^ 59
def prefixEnd_2888312 : Nat := 4983230072969 + 3 ^ 40 * 2888312 * 2
def baseEnd_2888312 : Nat := 1483092336149008699716901

theorem tailTrace_2888312 : CollatzResearch.WordTrace tailWord_2888312 prefixEnd_2888312 1483092336149008699716901 := by
  unfold tailWord_2888312
  simp only [CollatzResearch.WordTrace]
  refine ⟨52672696556073191631165595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70230262074764255508220793 52672696556073191631165595)
  ·
    refine ⟨79009044834109787446748393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52672696556073191631165595 79009044834109787446748393)
    ·
      refine ⟨59256783625582340585061295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79009044834109787446748393 59256783625582340585061295)
      ·
        refine ⟨88885175438373510877591943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59256783625582340585061295 88885175438373510877591943)
        ·
          refine ⟨133327763157560266316387915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88885175438373510877591943 133327763157560266316387915)
          ·
            refine ⟨199991644736340399474581873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133327763157560266316387915 199991644736340399474581873)
            ·
              refine ⟨149993733552255299605936405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199991644736340399474581873 149993733552255299605936405)
              ·
                refine ⟨7030956260261967169028269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149993733552255299605936405 7030956260261967169028269)
                ·
                  refine ⟨2636608597598237688385601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7030956260261967169028269 2636608597598237688385601)
                  ·
                    refine ⟨1977456448198678266289201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2636608597598237688385601 1977456448198678266289201)
                    ·
                      refine ⟨1483092336149008699716901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977456448198678266289201 1483092336149008699716901)
                      ·
                        rfl

theorem cell23_2888312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_2888312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888312 prefixEnd_2888312 := by exact prefixLift 2888312
  have htrace : WordTrace (prefixWord ++ tailWord_2888312) baseStart_2888312 baseEnd_2888312 := by
    simpa [prefixWord, tailWord_2888312, baseEnd_2888312] using wordTrace_append hprefix tailTrace_2888312
  have hstable : (prefixWord ++ tailWord_2888312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888312).length < 2 ^ (prefixWord ++ tailWord_2888312).sum := by decide
  have hdescent : baseEnd_2888312 < baseStart_2888312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888325 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_2888325 : Nat := 118140960795 + 2888325 * 2 ^ 59
def prefixEnd_2888325 : Nat := 4983230072969 + 3 ^ 40 * 2888325 * 2
def baseEnd_2888325 : Nat := 1483099011397517148854341

theorem tailTrace_2888325 : CollatzResearch.WordTrace tailWord_2888325 prefixEnd_2888325 1483099011397517148854341 := by
  unfold tailWord_2888325
  simp only [CollatzResearch.WordTrace]
  refine ⟨105345867261099286482554429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70230578174066190988369619 105345867261099286482554429)
  ·
    refine ⟨39504700222912232430957911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105345867261099286482554429 39504700222912232430957911)
    ·
      refine ⟨59257050334368348646436867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39504700222912232430957911 59257050334368348646436867)
      ·
        refine ⟨88885575501552522969655301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59257050334368348646436867 88885575501552522969655301)
        ·
          refine ⟨16666045406541098056810369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88885575501552522969655301 16666045406541098056810369)
          ·
            refine ⟨12499534054905823542607777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16666045406541098056810369 12499534054905823542607777)
            ·
              refine ⟨9374650541179367656955833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12499534054905823542607777 9374650541179367656955833)
              ·
                refine ⟨7030987905884525742716875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9374650541179367656955833 7030987905884525742716875)
                ·
                  refine ⟨10546481858826788614075313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7030987905884525742716875 10546481858826788614075313)
                  ·
                    refine ⟨7909861394120091460556485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10546481858826788614075313 7909861394120091460556485)
                    ·
                      refine ⟨1483099011397517148854341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7909861394120091460556485 1483099011397517148854341)
                      ·
                        rfl

theorem cell23_2888325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_2888325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888325 prefixEnd_2888325 := by exact prefixLift 2888325
  have htrace : WordTrace (prefixWord ++ tailWord_2888325) baseStart_2888325 baseEnd_2888325 := by
    simpa [prefixWord, tailWord_2888325, baseEnd_2888325] using wordTrace_append hprefix tailTrace_2888325
  have hstable : (prefixWord ++ tailWord_2888325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888325).length < 2 ^ (prefixWord ++ tailWord_2888325).sum := by decide
  have hdescent : baseEnd_2888325 < baseStart_2888325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888355 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 7, 2]
def baseStart_2888355 : Nat := 118140960795 + 2888355 * 2 ^ 59
def prefixEnd_2888355 : Nat := 4983230072969 + 3 ^ 40 * 2888355 * 2
def baseEnd_2888355 : Nat := 1483114415817152031479203

theorem tailTrace_2888355 : CollatzResearch.WordTrace tailWord_2888355 prefixEnd_2888355 1483114415817152031479203 := by
  unfold tailWord_2888355
  simp only [CollatzResearch.WordTrace]
  refine ⟨105346961450990601606146519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70231307633993734404097679 105346961450990601606146519)
  ·
    refine ⟨158020442176485902409219779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105346961450990601606146519 158020442176485902409219779)
    ·
      refine ⟨237030663264728853613829669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158020442176485902409219779 237030663264728853613829669)
      ·
        refine ⟨44443249362136660052593063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237030663264728853613829669 44443249362136660052593063)
        ·
          refine ⟨66664874043204990078889595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44443249362136660052593063 66664874043204990078889595)
          ·
            refine ⟨99997311064807485118334393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66664874043204990078889595 99997311064807485118334393)
            ·
              refine ⟨74997983298605613838750795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99997311064807485118334393 74997983298605613838750795)
              ·
                refine ⟨112496974947908420758126193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74997983298605613838750795 112496974947908420758126193)
                ·
                  refine ⟨84372731210931315568594645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112496974947908420758126193 84372731210931315568594645)
                  ·
                    refine ⟨1977485887756202708638937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84372731210931315568594645 1977485887756202708638937)
                    ·
                      refine ⟨1483114415817152031479203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977485887756202708638937 1483114415817152031479203)
                      ·
                        rfl

theorem cell23_2888355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_2888355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888355 prefixEnd_2888355 := by exact prefixLift 2888355
  have htrace : WordTrace (prefixWord ++ tailWord_2888355) baseStart_2888355 baseEnd_2888355 := by
    simpa [prefixWord, tailWord_2888355, baseEnd_2888355] using wordTrace_append hprefix tailTrace_2888355
  have hstable : (prefixWord ++ tailWord_2888355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888355).length < 2 ^ (prefixWord ++ tailWord_2888355).sum := by decide
  have hdescent : baseEnd_2888355 < baseStart_2888355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888366 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_2888366 : Nat := 118140960795 + 2888366 * 2 ^ 59
def prefixEnd_2888366 : Nat := 4983230072969 + 3 ^ 40 * 2888366 * 2
def baseEnd_2888366 : Nat := 1483120064104351488441653

theorem tailTrace_2888366 : CollatzResearch.WordTrace tailWord_2888366 prefixEnd_2888366 1483120064104351488441653 := by
  unfold tailWord_2888366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13168420331743843810599619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70231575102633833656531301 13168420331743843810599619)
  ·
    refine ⟨19752630497615765715899429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13168420331743843810599619 19752630497615765715899429)
    ·
      refine ⟨3703618218302956071731143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19752630497615765715899429 3703618218302956071731143)
      ·
        refine ⟨5555427327454434107596715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703618218302956071731143 5555427327454434107596715)
        ·
          refine ⟨8333140991181651161395073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555427327454434107596715 8333140991181651161395073)
          ·
            refine ⟨6249855743386238371046305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8333140991181651161395073 6249855743386238371046305)
            ·
              refine ⟨4687391807539678778284729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6249855743386238371046305 4687391807539678778284729)
              ·
                refine ⟨3515543855654759083713547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687391807539678778284729 3515543855654759083713547)
                ·
                  refine ⟨5273315783482138625570321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515543855654759083713547 5273315783482138625570321)
                  ·
                    refine ⟨3954986837611603969177741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273315783482138625570321 3954986837611603969177741)
                    ·
                      refine ⟨1483120064104351488441653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3954986837611603969177741 1483120064104351488441653)
                      ·
                        rfl

theorem cell23_2888366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_2888366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888366 prefixEnd_2888366 := by exact prefixLift 2888366
  have htrace : WordTrace (prefixWord ++ tailWord_2888366) baseStart_2888366 baseEnd_2888366 := by
    simpa [prefixWord, tailWord_2888366, baseEnd_2888366] using wordTrace_append hprefix tailTrace_2888366
  have hstable : (prefixWord ++ tailWord_2888366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888366).length < 2 ^ (prefixWord ++ tailWord_2888366).sum := by decide
  have hdescent : baseEnd_2888366 < baseStart_2888366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888369 : List Nat := [1, 2, 2, 6, 1, 2, 2, 7]
def baseStart_2888369 : Nat := 118140960795 + 2888369 * 2 ^ 59
def prefixEnd_2888369 : Nat := 4983230072969 + 3 ^ 40 * 2888369 * 2
def baseEnd_2888369 : Nat := 54930429798011665803857

theorem tailTrace_2888369 : CollatzResearch.WordTrace tailWord_2888369 prefixEnd_2888369 54930429798011665803857 := by
  unfold tailWord_2888369
  simp only [CollatzResearch.WordTrace]
  refine ⟨105347472072939881997156161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70231648048626587998104107 105347472072939881997156161)
  ·
    refine ⟨79010604054704911497867121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105347472072939881997156161 79010604054704911497867121)
    ·
      refine ⟨59257953041028683623400341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79010604054704911497867121 59257953041028683623400341)
      ·
        refine ⟨2777716548798219544846891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59257953041028683623400341 2777716548798219544846891)
        ·
          refine ⟨4166574823197329317270337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2777716548798219544846891 4166574823197329317270337)
          ·
            refine ⟨3124931117397996987952753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4166574823197329317270337 3124931117397996987952753)
            ·
              refine ⟨2343698338048497740964565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124931117397996987952753 2343698338048497740964565)
              ·
                refine ⟨54930429798011665803857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2343698338048497740964565 54930429798011665803857)
                ·
                  rfl

theorem cell23_2888369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 7].length) (baseStart_2888369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888369 prefixEnd_2888369 := by exact prefixLift 2888369
  have htrace : WordTrace (prefixWord ++ tailWord_2888369) baseStart_2888369 baseEnd_2888369 := by
    simpa [prefixWord, tailWord_2888369, baseEnd_2888369] using wordTrace_append hprefix tailTrace_2888369
  have hstable : (prefixWord ++ tailWord_2888369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888369).length < 2 ^ (prefixWord ++ tailWord_2888369).sum := by decide
  have hdescent : baseEnd_2888369 < baseStart_2888369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888397 : List Nat := [1, 6, 2, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2888397 : Nat := 118140960795 + 2888397 * 2 ^ 59
def prefixEnd_2888397 : Nat := 4983230072969 + 3 ^ 40 * 2888397 * 2
def baseEnd_2888397 : Nat := 1483135982004640867154011

theorem tailTrace_2888397 : CollatzResearch.WordTrace tailWord_2888397 prefixEnd_2888397 1483135982004640867154011 := by
  unfold tailWord_2888397
  simp only [CollatzResearch.WordTrace]
  refine ⟨105348493316838442779175445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70232328877892295186116963 105348493316838442779175445)
  ·
    refine ⟨4938210624226802005273849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105348493316838442779175445 4938210624226802005273849)
    ·
      refine ⟨3703657968170101503955387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4938210624226802005273849 3703657968170101503955387)
      ·
        refine ⟨5555486952255152255933081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703657968170101503955387 5555486952255152255933081)
        ·
          refine ⟨4166615214191364191949811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5555486952255152255933081 4166615214191364191949811)
          ·
            refine ⟨6249922821287046287924717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166615214191364191949811 6249922821287046287924717)
            ·
              refine ⟨2343721057982642357971769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6249922821287046287924717 2343721057982642357971769)
              ·
                refine ⟨1757790793486981768478827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343721057982642357971769 1757790793486981768478827)
                ·
                  refine ⟨2636686190230472652718241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757790793486981768478827 2636686190230472652718241)
                  ·
                    refine ⟨1977514642672854489538681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2636686190230472652718241 1977514642672854489538681)
                    ·
                      refine ⟨1483135982004640867154011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977514642672854489538681 1483135982004640867154011)
                      ·
                        rfl

theorem cell23_2888397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2888397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888397 prefixEnd_2888397 := by exact prefixLift 2888397
  have htrace : WordTrace (prefixWord ++ tailWord_2888397) baseStart_2888397 baseEnd_2888397 := by
    simpa [prefixWord, tailWord_2888397, baseEnd_2888397] using wordTrace_append hprefix tailTrace_2888397
  have hstable : (prefixWord ++ tailWord_2888397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888397).length < 2 ^ (prefixWord ++ tailWord_2888397).sum := by decide
  have hdescent : baseEnd_2888397 < baseStart_2888397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888435 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 3]
def baseStart_2888435 : Nat := 118140960795 + 2888435 * 2 ^ 59
def prefixEnd_2888435 : Nat := 4983230072969 + 3 ^ 40 * 2888435 * 2
def baseEnd_2888435 : Nat := 1483155494269511718478835

theorem tailTrace_2888435 : CollatzResearch.WordTrace tailWord_2888435 prefixEnd_2888435 1483155494269511718478835 := by
  unfold tailWord_2888435
  simp only [CollatzResearch.WordTrace]
  refine ⟨105349879290700775269058759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70233252860467183512705839 105349879290700775269058759)
  ·
    refine ⟨158024818936051162903588139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105349879290700775269058759 158024818936051162903588139)
    ·
      refine ⟨237037228404076744355382209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158024818936051162903588139 237037228404076744355382209)
      ·
        refine ⟨177777921303057558266536657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237037228404076744355382209 177777921303057558266536657)
        ·
          refine ⟨133333440977293168699902493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177777921303057558266536657 133333440977293168699902493)
          ·
            refine ⟨50000040366484938262463435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133333440977293168699902493 50000040366484938262463435)
            ·
              refine ⟨75000060549727407393695153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50000040366484938262463435 75000060549727407393695153)
              ·
                refine ⟨56250045412295555545271365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75000060549727407393695153 56250045412295555545271365)
                ·
                  refine ⟨10546883514805416664738381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56250045412295555545271365 10546883514805416664738381)
                  ·
                    refine ⟨3955081318052031249276893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10546883514805416664738381 3955081318052031249276893)
                    ·
                      refine ⟨1483155494269511718478835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3955081318052031249276893 1483155494269511718478835)
                      ·
                        rfl

theorem cell23_2888435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_2888435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888435 prefixEnd_2888435 := by exact prefixLift 2888435
  have htrace : WordTrace (prefixWord ++ tailWord_2888435) baseStart_2888435 baseEnd_2888435 := by
    simpa [prefixWord, tailWord_2888435, baseEnd_2888435] using wordTrace_append hprefix tailTrace_2888435
  have hstable : (prefixWord ++ tailWord_2888435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888435).length < 2 ^ (prefixWord ++ tailWord_2888435).sum := by decide
  have hdescent : baseEnd_2888435 < baseStart_2888435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888452 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2888452 : Nat := 118140960795 + 2888452 * 2 ^ 59
def prefixEnd_2888452 : Nat := 4983230072969 + 3 ^ 40 * 2888452 * 2
def baseEnd_2888452 : Nat := 1483164223440638151966257

theorem tailTrace_2888452 : CollatzResearch.WordTrace tailWord_2888452 prefixEnd_2888452 1483164223440638151966257 := by
  unfold tailWord_2888452
  simp only [CollatzResearch.WordTrace]
  refine ⟨52675249665819593586213805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70233666221092791448285073 52675249665819593586213805)
  ·
    refine ⟨19753218624682347594830177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52675249665819593586213805 19753218624682347594830177)
    ·
      refine ⟨14814913968511760696122633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19753218624682347594830177 14814913968511760696122633)
      ·
        refine ⟨11111185476383820522091975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14814913968511760696122633 11111185476383820522091975)
        ·
          refine ⟨16666778214575730783137963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11111185476383820522091975 16666778214575730783137963)
          ·
            refine ⟨25000167321863596174706945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16666778214575730783137963 25000167321863596174706945)
            ·
              refine ⟨18750125491397697131030209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25000167321863596174706945 18750125491397697131030209)
              ·
                refine ⟨14062594118548272848272657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18750125491397697131030209 14062594118548272848272657)
                ·
                  refine ⟨10546945588911204636204493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14062594118548272848272657 10546945588911204636204493)
                  ·
                    refine ⟨3955104595841701738576685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10546945588911204636204493 3955104595841701738576685)
                    ·
                      refine ⟨1483164223440638151966257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3955104595841701738576685 1483164223440638151966257)
                      ·
                        rfl

theorem cell23_2888452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2888452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888452 prefixEnd_2888452 := by exact prefixLift 2888452
  have htrace : WordTrace (prefixWord ++ tailWord_2888452) baseStart_2888452 baseEnd_2888452 := by
    simpa [prefixWord, tailWord_2888452, baseEnd_2888452] using wordTrace_append hprefix tailTrace_2888452
  have hstable : (prefixWord ++ tailWord_2888452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888452).length < 2 ^ (prefixWord ++ tailWord_2888452).sum := by decide
  have hdescent : baseEnd_2888452 < baseStart_2888452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888465 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2888465 : Nat := 118140960795 + 2888465 * 2 ^ 59
def prefixEnd_2888465 : Nat := 4983230072969 + 3 ^ 40 * 2888465 * 2
def baseEnd_2888465 : Nat := 1483170898689146601103697

theorem tailTrace_2888465 : CollatzResearch.WordTrace tailWord_2888465 prefixEnd_2888465 1483170898689146601103697 := by
  unfold tailWord_2888465
  simp only [CollatzResearch.WordTrace]
  refine ⟨105350973480592090392650849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70233982320394726928433899 105350973480592090392650849)
  ·
    refine ⟨79013230110444067794488137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105350973480592090392650849 79013230110444067794488137)
    ·
      refine ⟨59259922582833050845866103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79013230110444067794488137 59259922582833050845866103)
      ·
        refine ⟨88889883874249576268799155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59259922582833050845866103 88889883874249576268799155)
        ·
          refine ⟨133334825811374364403198733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88889883874249576268799155 133334825811374364403198733)
          ·
            refine ⟨50000559679265386651199525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133334825811374364403198733 50000559679265386651199525)
            ·
              refine ⟨9375104939862259997099911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50000559679265386651199525 9375104939862259997099911)
              ·
                refine ⟨14062657409793389995649867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9375104939862259997099911 14062657409793389995649867)
                ·
                  refine ⟨21093986114690084993474801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14062657409793389995649867 21093986114690084993474801)
                  ·
                    refine ⟨15820489586017563745106101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21093986114690084993474801 15820489586017563745106101)
                    ·
                      refine ⟨1483170898689146601103697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15820489586017563745106101 1483170898689146601103697)
                      ·
                        rfl

theorem cell23_2888465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2888465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888465 prefixEnd_2888465 := by exact prefixLift 2888465
  have htrace : WordTrace (prefixWord ++ tailWord_2888465) baseStart_2888465 baseEnd_2888465 := by
    simpa [prefixWord, tailWord_2888465, baseEnd_2888465] using wordTrace_append hprefix tailTrace_2888465
  have hstable : (prefixWord ++ tailWord_2888465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888465).length < 2 ^ (prefixWord ++ tailWord_2888465).sum := by decide
  have hdescent : baseEnd_2888465 < baseStart_2888465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888492 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 6, 2]
def baseStart_2888492 : Nat := 118140960795 + 2888492 * 2 ^ 59
def prefixEnd_2888492 : Nat := 4983230072969 + 3 ^ 40 * 2888492 * 2
def baseEnd_2888492 : Nat := 1483184762666817995466073

theorem tailTrace_2888492 : CollatzResearch.WordTrace tailWord_2888492 prefixEnd_2888492 1483184762666817995466073 := by
  unfold tailWord_2888492
  simp only [CollatzResearch.WordTrace]
  refine ⟨52675979125747137001941865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70234638834329516002589153 52675979125747137001941865)
  ·
    refine ⟨39506984344310352751456399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52675979125747137001941865 39506984344310352751456399)
    ·
      refine ⟨59260476516465529127184599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39506984344310352751456399 59260476516465529127184599)
      ·
        refine ⟨88890714774698293690776899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59260476516465529127184599 88890714774698293690776899)
        ·
          refine ⟨133336072162047440536165349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88890714774698293690776899 133336072162047440536165349)
          ·
            refine ⟨25000513530383895100531003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133336072162047440536165349 25000513530383895100531003)
            ·
              refine ⟨37500770295575842650796505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25000513530383895100531003 37500770295575842650796505)
              ·
                refine ⟨28125577721681881988097379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37500770295575842650796505 28125577721681881988097379)
                ·
                  refine ⟨42188366582522822982146069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28125577721681881988097379 42188366582522822982146069)
                  ·
                    refine ⟨1977579683555757327288097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42188366582522822982146069 1977579683555757327288097)
                    ·
                      refine ⟨1483184762666817995466073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977579683555757327288097 1483184762666817995466073)
                      ·
                        rfl

theorem cell23_2888492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 6, 2].length) (baseStart_2888492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888492 prefixEnd_2888492 := by exact prefixLift 2888492
  have htrace : WordTrace (prefixWord ++ tailWord_2888492) baseStart_2888492 baseEnd_2888492 := by
    simpa [prefixWord, tailWord_2888492, baseEnd_2888492] using wordTrace_append hprefix tailTrace_2888492
  have hstable : (prefixWord ++ tailWord_2888492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888492).length < 2 ^ (prefixWord ++ tailWord_2888492).sum := by decide
  have hdescent : baseEnd_2888492 < baseStart_2888492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888493 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2888493 : Nat := 118140960795 + 2888493 * 2 ^ 59
def prefixEnd_2888493 : Nat := 4983230072969 + 3 ^ 40 * 2888493 * 2
def baseEnd_2888493 : Nat := 164798364016385832394841

theorem tailTrace_2888493 : CollatzResearch.WordTrace tailWord_2888493 prefixEnd_2888493 164798364016385832394841 := by
  unfold tailWord_2888493
  simp only [CollatzResearch.WordTrace]
  refine ⟨105351994724490651174670133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70234663149660434116446755 105351994724490651174670133)
  ·
    refine ⟨9876749505420998547625325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105351994724490651174670133 9876749505420998547625325)
    ·
      refine ⟨3703781064532874455359497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9876749505420998547625325 3703781064532874455359497)
      ·
        refine ⟨2777835798399655841519623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3703781064532874455359497 2777835798399655841519623)
        ·
          refine ⟨4166753697599483762279435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2777835798399655841519623 4166753697599483762279435)
          ·
            refine ⟨6250130546399225643419153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166753697599483762279435 6250130546399225643419153)
            ·
              refine ⟨4687597909799419232564365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250130546399225643419153 4687597909799419232564365)
              ·
                refine ⟨1757849216174782212211637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4687597909799419232564365 1757849216174782212211637)
                ·
                  refine ⟨164798364016385832394841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1757849216174782212211637 164798364016385832394841)
                  ·
                    rfl

theorem cell23_2888493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2888493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888493 prefixEnd_2888493 := by exact prefixLift 2888493
  have htrace : WordTrace (prefixWord ++ tailWord_2888493) baseStart_2888493 baseEnd_2888493 := by
    simpa [prefixWord, tailWord_2888493, baseEnd_2888493] using wordTrace_append hprefix tailTrace_2888493
  have hstable : (prefixWord ++ tailWord_2888493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888493).length < 2 ^ (prefixWord ++ tailWord_2888493).sum := by decide
  have hdescent : baseEnd_2888493 < baseStart_2888493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888512 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_2888512 : Nat := 118140960795 + 2888512 * 2 ^ 59
def prefixEnd_2888512 : Nat := 4983230072969 + 3 ^ 40 * 2888512 * 2
def baseEnd_2888512 : Nat := 1483195032279907917215981

theorem tailTrace_2888512 : CollatzResearch.WordTrace tailWord_2888512 prefixEnd_2888512 1483195032279907917215981 := by
  unfold tailWord_2888512
  simp only [CollatzResearch.WordTrace]
  refine ⟨52676343855710908709805895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70235125140947878279741193 52676343855710908709805895)
  ·
    refine ⟨79014515783566363064708843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52676343855710908709805895 79014515783566363064708843)
    ·
      refine ⟨118521773675349544597063265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79014515783566363064708843 118521773675349544597063265)
      ·
        refine ⟨88891330256512158447797449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118521773675349544597063265 88891330256512158447797449)
        ·
          refine ⟨66668497692384118835848087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88891330256512158447797449 66668497692384118835848087)
          ·
            refine ⟨100002746538576178253772131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66668497692384118835848087 100002746538576178253772131)
            ·
              refine ⟨150004119807864267380658197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100002746538576178253772131 150004119807864267380658197)
              ·
                refine ⟨7031443115993637533468353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150004119807864267380658197 7031443115993637533468353)
                ·
                  refine ⟨5273582336995228150101265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7031443115993637533468353 5273582336995228150101265)
                  ·
                    refine ⟨3955186752746421112575949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273582336995228150101265 3955186752746421112575949)
                    ·
                      refine ⟨1483195032279907917215981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3955186752746421112575949 1483195032279907917215981)
                      ·
                        rfl

theorem cell23_2888512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_2888512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888512 prefixEnd_2888512 := by exact prefixLift 2888512
  have htrace : WordTrace (prefixWord ++ tailWord_2888512) baseStart_2888512 baseEnd_2888512 := by
    simpa [prefixWord, tailWord_2888512, baseEnd_2888512] using wordTrace_append hprefix tailTrace_2888512
  have hstable : (prefixWord ++ tailWord_2888512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888512).length < 2 ^ (prefixWord ++ tailWord_2888512).sum := by decide
  have hdescent : baseEnd_2888512 < baseStart_2888512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888515 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 8]
def baseStart_2888515 : Nat := 118140960795 + 2888515 * 2 ^ 59
def prefixEnd_2888515 : Nat := 4983230072969 + 3 ^ 40 * 2888515 * 2
def baseEnd_2888515 : Nat := 164799619191319045053163

theorem tailTrace_2888515 : CollatzResearch.WordTrace tailWord_2888515 prefixEnd_2888515 164799619191319045053163 := by
  unfold tailWord_2888515
  simp only [CollatzResearch.WordTrace]
  refine ⟨105352797130410948931970999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70235198086940632621313999 105352797130410948931970999)
  ·
    refine ⟨158029195695616423397956499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105352797130410948931970999 158029195695616423397956499)
    ·
      refine ⟨237043793543424635096934749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158029195695616423397956499 237043793543424635096934749)
      ·
        refine ⟨88891422578784238161350531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237043793543424635096934749 88891422578784238161350531)
        ·
          refine ⟨133337133868176357242025797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88891422578784238161350531 133337133868176357242025797)
          ·
            refine ⟨25000712600283066982879837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133337133868176357242025797 25000712600283066982879837)
            ·
              refine ⟨9375267225106150118579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25000712600283066982879837 9375267225106150118579939)
              ·
                refine ⟨14062900837659225177869909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9375267225106150118579939 14062900837659225177869909)
                ·
                  refine ⟨164799619191319045053163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14062900837659225177869909 164799619191319045053163)
                  ·
                    rfl

theorem cell23_2888515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 8].length) (baseStart_2888515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888515 prefixEnd_2888515 := by exact prefixLift 2888515
  have htrace : WordTrace (prefixWord ++ tailWord_2888515) baseStart_2888515 baseEnd_2888515 := by
    simpa [prefixWord, tailWord_2888515, baseEnd_2888515] using wordTrace_append hprefix tailTrace_2888515
  have hstable : (prefixWord ++ tailWord_2888515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888515).length < 2 ^ (prefixWord ++ tailWord_2888515).sum := by decide
  have hdescent : baseEnd_2888515 < baseStart_2888515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888569 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 4, 3, 2]
def baseStart_2888569 : Nat := 118140960795 + 2888569 * 2 ^ 59
def prefixEnd_2888569 : Nat := 4983230072969 + 3 ^ 40 * 2888569 * 2
def baseEnd_2888569 : Nat := 1483224300677214194203219

theorem tailTrace_2888569 : CollatzResearch.WordTrace tailWord_2888569 prefixEnd_2888569 1483224300677214194203219 := by
  unfold tailWord_2888569
  simp only [CollatzResearch.WordTrace]
  refine ⟨105354766672215316154436761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70236511114810210769624507 105354766672215316154436761)
  ·
    refine ⟨79016075004161487115827571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105354766672215316154436761 79016075004161487115827571)
    ·
      refine ⟨118524112506242230673741357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79016075004161487115827571 118524112506242230673741357)
      ·
        refine ⟨44446542189840836502653009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118524112506242230673741357 44446542189840836502653009)
        ·
          refine ⟨33334906642380627376989757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44446542189840836502653009 33334906642380627376989757)
          ·
            refine ⟨12500589990892735266371159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33334906642380627376989757 12500589990892735266371159)
            ·
              refine ⟨18750884986339102899556739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12500589990892735266371159 18750884986339102899556739)
              ·
                refine ⟨28126327479508654349335109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18750884986339102899556739 28126327479508654349335109)
                ·
                  refine ⟨5273686402407872690500333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28126327479508654349335109 5273686402407872690500333)
                  ·
                    refine ⟨1977632400902952258937625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5273686402407872690500333 1977632400902952258937625)
                    ·
                      refine ⟨1483224300677214194203219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977632400902952258937625 1483224300677214194203219)
                      ·
                        rfl

theorem cell23_2888569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_2888569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888569 prefixEnd_2888569 := by exact prefixLift 2888569
  have htrace : WordTrace (prefixWord ++ tailWord_2888569) baseStart_2888569 baseEnd_2888569 := by
    simpa [prefixWord, tailWord_2888569, baseEnd_2888569] using wordTrace_append hprefix tailTrace_2888569
  have hstable : (prefixWord ++ tailWord_2888569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888569).length < 2 ^ (prefixWord ++ tailWord_2888569).sum := by decide
  have hdescent : baseEnd_2888569 < baseStart_2888569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888609 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_2888609 : Nat := 118140960795 + 2888609 * 2 ^ 59
def prefixEnd_2888609 : Nat := 4983230072969 + 3 ^ 40 * 2888609 * 2
def baseEnd_2888609 : Nat := 494414946634464679234345

theorem tailTrace_2888609 : CollatzResearch.WordTrace tailWord_2888609 prefixEnd_2888609 494414946634464679234345 := by
  unfold tailWord_2888609
  simp only [CollatzResearch.WordTrace]
  refine ⟨105356225592070402985892881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70237483728046935323928587 105356225592070402985892881)
  ·
    refine ⟨79017169194052802239419661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105356225592070402985892881 79017169194052802239419661)
    ·
      refine ⟨29631438447769800839782373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79017169194052802239419661 29631438447769800839782373)
      ·
        refine ⟨5555894708956837657459195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29631438447769800839782373 5555894708956837657459195)
        ·
          refine ⟨8333842063435256486188793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555894708956837657459195 8333842063435256486188793)
          ·
            refine ⟨6250381547576442364641595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8333842063435256486188793 6250381547576442364641595)
            ·
              refine ⟨9375572321364663546962393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250381547576442364641595 9375572321364663546962393)
              ·
                refine ⟨7031679241023497660221795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9375572321364663546962393 7031679241023497660221795)
                ·
                  refine ⟨10547518861535246490332693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7031679241023497660221795 10547518861535246490332693)
                  ·
                    refine ⟨494414946634464679234345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10547518861535246490332693 494414946634464679234345)
                    ·
                      rfl

theorem cell23_2888609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_2888609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888609 prefixEnd_2888609 := by exact prefixLift 2888609
  have htrace : WordTrace (prefixWord ++ tailWord_2888609) baseStart_2888609 baseEnd_2888609 := by
    simpa [prefixWord, tailWord_2888609, baseEnd_2888609] using wordTrace_append hprefix tailTrace_2888609
  have hstable : (prefixWord ++ tailWord_2888609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888609).length < 2 ^ (prefixWord ++ tailWord_2888609).sum := by decide
  have hdescent : baseEnd_2888609 < baseStart_2888609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888652 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_2888652 : Nat := 118140960795 + 2888652 * 2 ^ 59
def prefixEnd_2888652 : Nat := 4983230072969 + 3 ^ 40 * 2888652 * 2
def baseEnd_2888652 : Nat := 494422306523845789821779

theorem tailTrace_2888652 : CollatzResearch.WordTrace tailWord_2888652 prefixEnd_2888652 494422306523845789821779 := by
  unfold tailWord_2888652
  simp only [CollatzResearch.WordTrace]
  refine ⟨52678896965457310664854105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70238529287276414219805473 52678896965457310664854105)
  ·
    refine ⟨39509172724092982998640579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52678896965457310664854105 39509172724092982998640579)
    ·
      refine ⟨59263759086139474497960869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39509172724092982998640579 59263759086139474497960869)
      ·
        refine ⟨11111954828651151468367663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59263759086139474497960869 11111954828651151468367663)
        ·
          refine ⟨16667932242976727202551495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11111954828651151468367663 16667932242976727202551495)
          ·
            refine ⟨25001898364465090803827243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16667932242976727202551495 25001898364465090803827243)
            ·
              refine ⟨37502847546697636205740865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25001898364465090803827243 37502847546697636205740865)
              ·
                refine ⟨28127135660023227154305649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37502847546697636205740865 28127135660023227154305649)
                ·
                  refine ⟨21095351745017420365729237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28127135660023227154305649 21095351745017420365729237)
                  ·
                    refine ⟨494422306523845789821779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21095351745017420365729237 494422306523845789821779)
                    ·
                      rfl

theorem cell23_2888652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_2888652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888652 prefixEnd_2888652 := by exact prefixLift 2888652
  have htrace : WordTrace (prefixWord ++ tailWord_2888652) baseStart_2888652 baseEnd_2888652 := by
    simpa [prefixWord, tailWord_2888652, baseEnd_2888652] using wordTrace_append hprefix tailTrace_2888652
  have hstable : (prefixWord ++ tailWord_2888652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888652).length < 2 ^ (prefixWord ++ tailWord_2888652).sum := by decide
  have hdescent : baseEnd_2888652 < baseStart_2888652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888796 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2888796 : Nat := 118140960795 + 2888796 * 2 ^ 59
def prefixEnd_2888796 : Nat := 4983230072969 + 3 ^ 40 * 2888796 * 2
def baseEnd_2888796 : Nat := 1483340860785784806064675

theorem tailTrace_2888796 : CollatzResearch.WordTrace tailWord_2888796 prefixEnd_2888796 1483340860785784806064675 := by
  unfold tailWord_2888796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52681523021196466961475121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70242030694928622615300161 52681523021196466961475121)
  ·
    refine ⟨39511142265897350221106341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52681523021196466961475121 39511142265897350221106341)
    ·
      refine ⟨7408339174855753166457439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39511142265897350221106341 7408339174855753166457439)
      ·
        refine ⟨11112508762283629749686159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408339174855753166457439 11112508762283629749686159)
        ·
          refine ⟨16668763143425444624529239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11112508762283629749686159 16668763143425444624529239)
          ·
            refine ⟨25003144715138166936793859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16668763143425444624529239 25003144715138166936793859)
            ·
              refine ⟨37504717072707250405190789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25003144715138166936793859 37504717072707250405190789)
              ·
                refine ⟨7032134451132609450973273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37504717072707250405190789 7032134451132609450973273)
                ·
                  refine ⟨5274100838349457088229955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7032134451132609450973273 5274100838349457088229955)
                  ·
                    refine ⟨7911151257524185632344933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274100838349457088229955 7911151257524185632344933)
                    ·
                      refine ⟨1483340860785784806064675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7911151257524185632344933 1483340860785784806064675)
                      ·
                        rfl

theorem cell23_2888796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2888796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888796 prefixEnd_2888796 := by exact prefixLift 2888796
  have htrace : WordTrace (prefixWord ++ tailWord_2888796) baseStart_2888796 baseEnd_2888796 := by
    simpa [prefixWord, tailWord_2888796, baseEnd_2888796] using wordTrace_append hprefix tailTrace_2888796
  have hstable : (prefixWord ++ tailWord_2888796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888796).length < 2 ^ (prefixWord ++ tailWord_2888796).sum := by decide
  have hdescent : baseEnd_2888796 < baseStart_2888796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888797 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 5]
def baseStart_2888797 : Nat := 118140960795 + 2888797 * 2 ^ 59
def prefixEnd_2888797 : Nat := 4983230072969 + 3 ^ 40 * 2888797 * 2
def baseEnd_2888797 : Nat := 164815708251826589128019

theorem tailTrace_2888797 : CollatzResearch.WordTrace tailWord_2888797 prefixEnd_2888797 164815708251826589128019 := by
  unfold tailWord_2888797
  simp only [CollatzResearch.WordTrace]
  refine ⟨105363082515389311093736645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70242055010259540729157763 105363082515389311093736645)
  ·
    refine ⟨19755577971635495830075621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105363082515389311093736645 19755577971635495830075621)
    ·
      refine ⟨3704170869681655468139179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19755577971635495830075621 3704170869681655468139179)
      ·
        refine ⟨5556256304522483202208769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704170869681655468139179 5556256304522483202208769)
        ·
          refine ⟨4167192228391862401656577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5556256304522483202208769 4167192228391862401656577)
          ·
            refine ⟨3125394171293896801242433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4167192228391862401656577 3125394171293896801242433)
            ·
              refine ⟨2344045628470422600931825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125394171293896801242433 2344045628470422600931825)
              ·
                refine ⟨1758034221352816950698869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344045628470422600931825 1758034221352816950698869)
                ·
                  refine ⟨164815708251826589128019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758034221352816950698869 164815708251826589128019)
                  ·
                    rfl

theorem cell23_2888797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_2888797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888797 prefixEnd_2888797 := by exact prefixLift 2888797
  have htrace : WordTrace (prefixWord ++ tailWord_2888797) baseStart_2888797 baseEnd_2888797 := by
    simpa [prefixWord, tailWord_2888797, baseEnd_2888797] using wordTrace_append hprefix tailTrace_2888797
  have hstable : (prefixWord ++ tailWord_2888797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888797).length < 2 ^ (prefixWord ++ tailWord_2888797).sum := by decide
  have hdescent : baseEnd_2888797 < baseStart_2888797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888813 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_2888813 : Nat := 118140960795 + 2888813 * 2 ^ 59
def prefixEnd_2888813 : Nat := 4983230072969 + 3 ^ 40 * 2888813 * 2
def baseEnd_2888813 : Nat := 1483349589956911239552097

theorem tailTrace_2888813 : CollatzResearch.WordTrace tailWord_2888813 prefixEnd_2888813 1483349589956911239552097 := by
  unfold tailWord_2888813
  simp only [CollatzResearch.WordTrace]
  refine ⟨105363666083331345826319093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70242444055554230550879395 105363666083331345826319093)
  ·
    refine ⟨9877843695312313671217415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105363666083331345826319093 9877843695312313671217415)
    ·
      refine ⟨14816765542968470506826123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9877843695312313671217415 14816765542968470506826123)
      ·
        refine ⟨22225148314452705760239185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14816765542968470506826123 22225148314452705760239185)
        ·
          refine ⟨16668861235839529320179389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22225148314452705760239185 16668861235839529320179389)
          ·
            refine ⟨6250822963439823495067271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16668861235839529320179389 6250822963439823495067271)
            ·
              refine ⟨9376234445159735242600907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250822963439823495067271 9376234445159735242600907)
              ·
                refine ⟨14064351667739602863901361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9376234445159735242600907 14064351667739602863901361)
                ·
                  refine ⟨10548263750804702147926021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14064351667739602863901361 10548263750804702147926021)
                  ·
                    refine ⟨1977799453275881652736129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10548263750804702147926021 1977799453275881652736129)
                    ·
                      refine ⟨1483349589956911239552097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977799453275881652736129 1483349589956911239552097)
                      ·
                        rfl

theorem cell23_2888813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_2888813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888813 prefixEnd_2888813 := by exact prefixLift 2888813
  have htrace : WordTrace (prefixWord ++ tailWord_2888813) baseStart_2888813 baseEnd_2888813 := by
    simpa [prefixWord, tailWord_2888813, baseEnd_2888813] using wordTrace_append hprefix tailTrace_2888813
  have hstable : (prefixWord ++ tailWord_2888813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888813).length < 2 ^ (prefixWord ++ tailWord_2888813).sum := by decide
  have hdescent : baseEnd_2888813 < baseStart_2888813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888833 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2888833 : Nat := 118140960795 + 2888833 * 2 ^ 59
def prefixEnd_2888833 : Nat := 4983230072969 + 3 ^ 40 * 2888833 * 2
def baseEnd_2888833 : Nat := 1483359859570001161302005

theorem tailTrace_2888833 : CollatzResearch.WordTrace tailWord_2888833 prefixEnd_2888833 1483359859570001161302005 := by
  unfold tailWord_2888833
  simp only [CollatzResearch.WordTrace]
  refine ⟨105364395543258889242047153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70242930362172592828031435 105364395543258889242047153)
  ·
    refine ⟨79023296657444166931535365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105364395543258889242047153 79023296657444166931535365)
    ·
      refine ⟨14816868123270781299662881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79023296657444166931535365 14816868123270781299662881)
      ·
        refine ⟨11112651092453085974747161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14816868123270781299662881 11112651092453085974747161)
        ·
          refine ⟨8334488319339814481060371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11112651092453085974747161 8334488319339814481060371)
          ·
            refine ⟨12501732479009721721590557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334488319339814481060371 12501732479009721721590557)
            ·
              refine ⟨4688149679628645645596459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12501732479009721721590557 4688149679628645645596459)
              ·
                refine ⟨7032224519442968468394689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688149679628645645596459 7032224519442968468394689)
                ·
                  refine ⟨5274168389582226351296017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7032224519442968468394689 5274168389582226351296017)
                  ·
                    refine ⟨3955626292186669763472013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5274168389582226351296017 3955626292186669763472013)
                    ·
                      refine ⟨1483359859570001161302005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3955626292186669763472013 1483359859570001161302005)
                      ·
                        rfl

theorem cell23_2888833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2888833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888833 prefixEnd_2888833 := by exact prefixLift 2888833
  have htrace : WordTrace (prefixWord ++ tailWord_2888833) baseStart_2888833 baseEnd_2888833 := by
    simpa [prefixWord, tailWord_2888833, baseEnd_2888833] using wordTrace_append hprefix tailTrace_2888833
  have hstable : (prefixWord ++ tailWord_2888833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888833).length < 2 ^ (prefixWord ++ tailWord_2888833).sum := by decide
  have hdescent : baseEnd_2888833 < baseStart_2888833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888903 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_2888903 : Nat := 118140960795 + 2888903 * 2 ^ 59
def prefixEnd_2888903 : Nat := 4983230072969 + 3 ^ 40 * 2888903 * 2
def baseEnd_2888903 : Nat := 1483395803215815887426683

theorem tailTrace_2888903 : CollatzResearch.WordTrace tailWord_2888903 prefixEnd_2888903 1483395803215815887426683 := by
  unfold tailWord_2888903
  simp only [CollatzResearch.WordTrace]
  refine ⟨105366948653005291197095363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70244632435336860798063575 105366948653005291197095363)
  ·
    refine ⟨158050422979507936795643045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105366948653005291197095363 158050422979507936795643045)
    ·
      refine ⟨29634454308657738149183071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158050422979507936795643045 29634454308657738149183071)
      ·
        refine ⟨44451681462986607223774607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29634454308657738149183071 44451681462986607223774607)
        ·
          refine ⟨66677522194479910835661911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44451681462986607223774607 66677522194479910835661911)
          ·
            refine ⟨100016283291719866253492867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66677522194479910835661911 100016283291719866253492867)
            ·
              refine ⟨150024424937579799380239301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100016283291719866253492867 150024424937579799380239301)
              ·
                refine ⟨28129579675796212383794869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150024424937579799380239301 28129579675796212383794869)
                ·
                  refine ⟨2637148094605894910980769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28129579675796212383794869 2637148094605894910980769)
                  ·
                    refine ⟨1977861070954421183235577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637148094605894910980769 1977861070954421183235577)
                    ·
                      refine ⟨1483395803215815887426683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977861070954421183235577 1483395803215815887426683)
                      ·
                        rfl

theorem cell23_2888903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_2888903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888903 prefixEnd_2888903 := by exact prefixLift 2888903
  have htrace : WordTrace (prefixWord ++ tailWord_2888903) baseStart_2888903 baseEnd_2888903 := by
    simpa [prefixWord, tailWord_2888903, baseEnd_2888903] using wordTrace_append hprefix tailTrace_2888903
  have hstable : (prefixWord ++ tailWord_2888903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888903).length < 2 ^ (prefixWord ++ tailWord_2888903).sum := by decide
  have hdescent : baseEnd_2888903 < baseStart_2888903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888906 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_2888906 : Nat := 118140960795 + 2888906 * 2 ^ 59
def prefixEnd_2888906 : Nat := 4983230072969 + 3 ^ 40 * 2888906 * 2
def baseEnd_2888906 : Nat := 1483397343657779375689169

theorem tailTrace_2888906 : CollatzResearch.WordTrace tailWord_2888906 prefixEnd_2888906 1483397343657779375689169 := by
  unfold tailWord_2888906
  simp only [CollatzResearch.WordTrace]
  refine ⟨26341764517998605677363643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70244705381329615139636381 26341764517998605677363643)
  ·
    refine ⟨39512646776997908516045465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26341764517998605677363643 39512646776997908516045465)
    ·
      refine ⟨29634485082748431387034099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39512646776997908516045465 29634485082748431387034099)
      ·
        refine ⟨44451727624122647080551149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29634485082748431387034099 44451727624122647080551149)
        ·
          refine ⟨16669397859045992655206681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44451727624122647080551149 16669397859045992655206681)
          ·
            refine ⟨12502048394284494491405011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16669397859045992655206681 12502048394284494491405011)
            ·
              refine ⟨18753072591426741737107517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12502048394284494491405011 18753072591426741737107517)
              ·
                refine ⟨7032402221785028151415319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18753072591426741737107517 7032402221785028151415319)
                ·
                  refine ⟨10548603332677542227122979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032402221785028151415319 10548603332677542227122979)
                  ·
                    refine ⟨15822904999016313340684469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10548603332677542227122979 15822904999016313340684469)
                    ·
                      refine ⟨1483397343657779375689169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15822904999016313340684469 1483397343657779375689169)
                      ·
                        rfl

theorem cell23_2888906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_2888906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888906 prefixEnd_2888906 := by exact prefixLift 2888906
  have htrace : WordTrace (prefixWord ++ tailWord_2888906) baseStart_2888906 baseEnd_2888906 := by
    simpa [prefixWord, tailWord_2888906, baseEnd_2888906] using wordTrace_append hprefix tailTrace_2888906
  have hstable : (prefixWord ++ tailWord_2888906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888906).length < 2 ^ (prefixWord ++ tailWord_2888906).sum := by decide
  have hdescent : baseEnd_2888906 < baseStart_2888906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888940 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_2888940 : Nat := 118140960795 + 2888940 * 2 ^ 59
def prefixEnd_2888940 : Nat := 4983230072969 + 3 ^ 40 * 2888940 * 2
def baseEnd_2888940 : Nat := 1483414802000032242664013

theorem tailTrace_2888940 : CollatzResearch.WordTrace tailWord_2888940 prefixEnd_2888940 1483414802000032242664013 := by
  unfold tailWord_2888940
  simp only [CollatzResearch.WordTrace]
  refine ⟨52684149076935623258096137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70245532102580831010794849 52684149076935623258096137)
  ·
    refine ⟨39513111807701717443572103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52684149076935623258096137 39513111807701717443572103)
    ·
      refine ⟨59269667711552576165358155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39513111807701717443572103 59269667711552576165358155)
      ·
        refine ⟨88904501567328864248037233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59269667711552576165358155 88904501567328864248037233)
        ·
          refine ⟨66678376175496648186027925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88904501567328864248037233 66678376175496648186027925)
          ·
            refine ⟨3125548883226405383720059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66678376175496648186027925 3125548883226405383720059)
            ·
              refine ⟨4688323324839608075580089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125548883226405383720059 4688323324839608075580089)
              ·
                refine ⟨3516242493629706056685067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688323324839608075580089 3516242493629706056685067)
                ·
                  refine ⟨5274363740444559085027601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516242493629706056685067 5274363740444559085027601)
                  ·
                    refine ⟨3955772805333419313770701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5274363740444559085027601 3955772805333419313770701)
                    ·
                      refine ⟨1483414802000032242664013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3955772805333419313770701 1483414802000032242664013)
                      ·
                        rfl

theorem cell23_2888940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_2888940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888940 prefixEnd_2888940 := by exact prefixLift 2888940
  have htrace : WordTrace (prefixWord ++ tailWord_2888940) baseStart_2888940 baseEnd_2888940 := by
    simpa [prefixWord, tailWord_2888940, baseEnd_2888940] using wordTrace_append hprefix tailTrace_2888940
  have hstable : (prefixWord ++ tailWord_2888940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888940).length < 2 ^ (prefixWord ++ tailWord_2888940).sum := by decide
  have hdescent : baseEnd_2888940 < baseStart_2888940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888986 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_2888986 : Nat := 118140960795 + 2888986 * 2 ^ 59
def prefixEnd_2888986 : Nat := 4983230072969 + 3 ^ 40 * 2888986 * 2
def baseEnd_2888986 : Nat := 494479474036713020896267

theorem tailTrace_2888986 : CollatzResearch.WordTrace tailWord_2888986 prefixEnd_2888986 494479474036713020896267 := by
  unfold tailWord_2888986
  simp only [CollatzResearch.WordTrace]
  refine ⟨26342493977926149093091703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70246650607803064248244541 26342493977926149093091703)
  ·
    refine ⟨39513740966889223639637555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26342493977926149093091703 39513740966889223639637555)
    ·
      refine ⟨59270611450333835459456333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39513740966889223639637555 59270611450333835459456333)
      ·
        refine ⟨22226479293875188297296125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59270611450333835459456333 22226479293875188297296125)
        ·
          refine ⟨8334929735203195611486047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22226479293875188297296125 8334929735203195611486047)
          ·
            refine ⟨12502394602804793417229071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334929735203195611486047 12502394602804793417229071)
            ·
              refine ⟨18753591904207190125843607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12502394602804793417229071 18753591904207190125843607)
              ·
                refine ⟨28130387856310785188765411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18753591904207190125843607 28130387856310785188765411)
                ·
                  refine ⟨42195581784466177783148117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28130387856310785188765411 42195581784466177783148117)
                  ·
                    refine ⟨494479474036713020896267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42195581784466177783148117 494479474036713020896267)
                    ·
                      rfl

theorem cell23_2888986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_2888986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2888986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2888986 prefixEnd_2888986 := by exact prefixLift 2888986
  have htrace : WordTrace (prefixWord ++ tailWord_2888986) baseStart_2888986 baseEnd_2888986 := by
    simpa [prefixWord, tailWord_2888986, baseEnd_2888986] using wordTrace_append hprefix tailTrace_2888986
  have hstable : (prefixWord ++ tailWord_2888986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888986).length < 2 ^ (prefixWord ++ tailWord_2888986).sum := by decide
  have hdescent : baseEnd_2888986 < baseStart_2888986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889010 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_2889010 : Nat := 118140960795 + 2889010 * 2 ^ 59
def prefixEnd_2889010 : Nat := 4983230072969 + 3 ^ 40 * 2889010 * 2
def baseEnd_2889010 : Nat := 1483450745645846968788691

theorem tailTrace_2889010 : CollatzResearch.WordTrace tailWord_2889010 prefixEnd_2889010 1483450745645846968788691 := by
  unfold tailWord_2889010
  simp only [CollatzResearch.WordTrace]
  refine ⟨26342712815904412117810121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70247234175745098980826989 26342712815904412117810121)
  ·
    refine ⟨19757034611928309088357591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26342712815904412117810121 19757034611928309088357591)
    ·
      refine ⟨29635551917892463632536387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19757034611928309088357591 29635551917892463632536387)
      ·
        refine ⟨44453327876838695448804581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29635551917892463632536387 44453327876838695448804581)
        ·
          refine ⟨8334998976907255396650859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44453327876838695448804581 8334998976907255396650859)
          ·
            refine ⟨12502498465360883094976289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334998976907255396650859 12502498465360883094976289)
            ·
              refine ⟨9376873849020662321232217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12502498465360883094976289 9376873849020662321232217)
              ·
                refine ⟨7032655386765496740924163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9376873849020662321232217 7032655386765496740924163)
                ·
                  refine ⟨10548983080148245111386245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032655386765496740924163 10548983080148245111386245)
                  ·
                    refine ⟨1977934327527795958384921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10548983080148245111386245 1977934327527795958384921)
                    ·
                      refine ⟨1483450745645846968788691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977934327527795958384921 1483450745645846968788691)
                      ·
                        rfl

theorem cell23_2889010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_2889010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889010 prefixEnd_2889010 := by exact prefixLift 2889010
  have htrace : WordTrace (prefixWord ++ tailWord_2889010) baseStart_2889010 baseEnd_2889010 := by
    simpa [prefixWord, tailWord_2889010, baseEnd_2889010] using wordTrace_append hprefix tailTrace_2889010
  have hstable : (prefixWord ++ tailWord_2889010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889010).length < 2 ^ (prefixWord ++ tailWord_2889010).sum := by decide
  have hdescent : baseEnd_2889010 < baseStart_2889010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889021 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2889021 : Nat := 118140960795 + 2889021 * 2 ^ 59
def prefixEnd_2889021 : Nat := 4983230072969 + 3 ^ 40 * 2889021 * 2
def baseEnd_2889021 : Nat := 1483456393933046425751141

theorem tailTrace_2889021 : CollatzResearch.WordTrace tailWord_2889021 prefixEnd_2889021 1483456393933046425751141 := by
  unfold tailWord_2889021
  simp only [CollatzResearch.WordTrace]
  refine ⟨105371252466577797349890917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70247501644385198233260611 105371252466577797349890917)
  ·
    refine ⟨19757109837483337003104547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105371252466577797349890917 19757109837483337003104547)
    ·
      refine ⟨29635664756225005504656821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19757109837483337003104547 29635664756225005504656821)
      ·
        refine ⟨2778343570896094266061577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29635664756225005504656821 2778343570896094266061577)
        ·
          refine ⟨2083757678172070699546183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778343570896094266061577 2083757678172070699546183)
          ·
            refine ⟨3125636517258106049319275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083757678172070699546183 3125636517258106049319275)
            ·
              refine ⟨4688454775887159073978913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125636517258106049319275 4688454775887159073978913)
              ·
                refine ⟨3516341081915369305484185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688454775887159073978913 3516341081915369305484185)
                ·
                  refine ⟨2637255811436526979113139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516341081915369305484185 2637255811436526979113139)
                  ·
                    refine ⟨3955883717154790468669709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2637255811436526979113139 3955883717154790468669709)
                    ·
                      refine ⟨1483456393933046425751141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3955883717154790468669709 1483456393933046425751141)
                      ·
                        rfl

theorem cell23_2889021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2889021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889021 prefixEnd_2889021 := by exact prefixLift 2889021
  have htrace : WordTrace (prefixWord ++ tailWord_2889021) baseStart_2889021 baseEnd_2889021 := by
    simpa [prefixWord, tailWord_2889021, baseEnd_2889021] using wordTrace_append hprefix tailTrace_2889021
  have hstable : (prefixWord ++ tailWord_2889021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889021).length < 2 ^ (prefixWord ++ tailWord_2889021).sum := by decide
  have hdescent : baseEnd_2889021 < baseStart_2889021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889033 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 5]
def baseStart_2889033 : Nat := 118140960795 + 2889033 * 2 ^ 59
def prefixEnd_2889033 : Nat := 4983230072969 + 3 ^ 40 * 2889033 * 2
def baseEnd_2889033 : Nat := 164829172855655597644565

theorem tailTrace_2889033 : CollatzResearch.WordTrace tailWord_2889033 prefixEnd_2889033 164829172855655597644565 := by
  unfold tailWord_2889033
  simp only [CollatzResearch.WordTrace]
  refine ⟨105371690142534323399327753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70247793428356215599551835 105371690142534323399327753)
  ·
    refine ⟨79028767606900742549495815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105371690142534323399327753 79028767606900742549495815)
    ·
      refine ⟨118543151410351113824243723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79028767606900742549495815 118543151410351113824243723)
      ·
        refine ⟨177814727115526670736365585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118543151410351113824243723 177814727115526670736365585)
        ·
          refine ⟨133361045336645003052274189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177814727115526670736365585 133361045336645003052274189)
          ·
            refine ⟨50010392001241876144602821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133361045336645003052274189 50010392001241876144602821)
            ·
              refine ⟨9376948500232851777113029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50010392001241876144602821 9376948500232851777113029)
              ·
                refine ⟨1758177843793659708208693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9376948500232851777113029 1758177843793659708208693)
                ·
                  refine ⟨164829172855655597644565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758177843793659708208693 164829172855655597644565)
                  ·
                    rfl

theorem cell23_2889033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 5].length) (baseStart_2889033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889033 prefixEnd_2889033 := by exact prefixLift 2889033
  have htrace : WordTrace (prefixWord ++ tailWord_2889033) baseStart_2889033 baseEnd_2889033 := by
    simpa [prefixWord, tailWord_2889033, baseEnd_2889033] using wordTrace_append hprefix tailTrace_2889033
  have hstable : (prefixWord ++ tailWord_2889033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889033).length < 2 ^ (prefixWord ++ tailWord_2889033).sum := by decide
  have hdescent : baseEnd_2889033 < baseStart_2889033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889044 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_2889044 : Nat := 118140960795 + 2889044 * 2 ^ 59
def prefixEnd_2889044 : Nat := 4983230072969 + 3 ^ 40 * 2889044 * 2
def baseEnd_2889044 : Nat := 1483468203988099835763535

theorem tailTrace_2889044 : CollatzResearch.WordTrace tailWord_2889044 prefixEnd_2889044 1483468203988099835763535 := by
  unfold tailWord_2889044
  simp only [CollatzResearch.WordTrace]
  refine ⟨52686045672747236138989093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70248060896996314851985457 52686045672747236138989093)
  ·
    refine ⟨9878633563640106776060455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52686045672747236138989093 9878633563640106776060455)
    ·
      refine ⟨14817950345460160164090683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9878633563640106776060455 14817950345460160164090683)
      ·
        refine ⟨22226925518190240246136025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14817950345460160164090683 22226925518190240246136025)
        ·
          refine ⟨16670194138642680184602019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22226925518190240246136025 16670194138642680184602019)
          ·
            refine ⟨25005291207964020276903029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16670194138642680184602019 25005291207964020276903029)
            ·
              refine ⟨2344246050746626900959659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25005291207964020276903029 2344246050746626900959659)
              ·
                refine ⟨3516369076119940351439489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344246050746626900959659 3516369076119940351439489)
                ·
                  refine ⟨2637276807089955263579617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516369076119940351439489 2637276807089955263579617)
                  ·
                    refine ⟨1977957605317466447684713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637276807089955263579617 1977957605317466447684713)
                    ·
                      refine ⟨1483468203988099835763535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1977957605317466447684713 1483468203988099835763535)
                      ·
                        rfl

theorem cell23_2889044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_2889044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889044 prefixEnd_2889044 := by exact prefixLift 2889044
  have htrace : WordTrace (prefixWord ++ tailWord_2889044) baseStart_2889044 baseEnd_2889044 := by
    simpa [prefixWord, tailWord_2889044, baseEnd_2889044] using wordTrace_append hprefix tailTrace_2889044
  have hstable : (prefixWord ++ tailWord_2889044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889044).length < 2 ^ (prefixWord ++ tailWord_2889044).sum := by decide
  have hdescent : baseEnd_2889044 < baseStart_2889044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889083 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 4]
def baseStart_2889083 : Nat := 118140960795 + 2889083 * 2 ^ 59
def prefixEnd_2889083 : Nat := 4983230072969 + 3 ^ 40 * 2889083 * 2
def baseEnd_2889083 : Nat := 1483488229733625183175855

theorem tailTrace_2889083 : CollatzResearch.WordTrace tailWord_2889083 prefixEnd_2889083 1483488229733625183175855 := by
  unfold tailWord_2889083
  simp only [CollatzResearch.WordTrace]
  refine ⟨105373513792353181938647903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70249009194902121292431935 105373513792353181938647903)
  ·
    refine ⟨158060270688529772907971855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105373513792353181938647903 158060270688529772907971855)
    ·
      refine ⟨237090406032794659361957783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158060270688529772907971855 237090406032794659361957783)
      ·
        refine ⟨355635609049191989042936675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237090406032794659361957783 355635609049191989042936675)
        ·
          refine ⟨533453413573787983564405013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355635609049191989042936675 533453413573787983564405013)
          ·
            refine ⟨25005628761271311729581485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 533453413573787983564405013 25005628761271311729581485)
            ·
              refine ⟨9377110785476741898593057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25005628761271311729581485 9377110785476741898593057)
              ·
                refine ⟨7032833089107556423944793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9377110785476741898593057 7032833089107556423944793)
                ·
                  refine ⟨5274624816830667317958595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7032833089107556423944793 5274624816830667317958595)
                  ·
                    refine ⟨7911937225246000976937893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274624816830667317958595 7911937225246000976937893)
                    ·
                      refine ⟨1483488229733625183175855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7911937225246000976937893 1483488229733625183175855)
                      ·
                        rfl

theorem cell23_2889083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 4].length) (baseStart_2889083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889083 prefixEnd_2889083 := by exact prefixLift 2889083
  have htrace : WordTrace (prefixWord ++ tailWord_2889083) baseStart_2889083 baseEnd_2889083 := by
    simpa [prefixWord, tailWord_2889083, baseEnd_2889083] using wordTrace_append hprefix tailTrace_2889083
  have hstable : (prefixWord ++ tailWord_2889083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889083).length < 2 ^ (prefixWord ++ tailWord_2889083).sum := by decide
  have hdescent : baseEnd_2889083 < baseStart_2889083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889090 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2889090 : Nat := 118140960795 + 2889090 * 2 ^ 59
def prefixEnd_2889090 : Nat := 4983230072969 + 3 ^ 40 * 2889090 * 2
def baseEnd_2889090 : Nat := 1483491824098206655788323

theorem tailTrace_2889090 : CollatzResearch.WordTrace tailWord_2889090 prefixEnd_2889090 1483491824098206655788323 := by
  unfold tailWord_2889090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26343442275831955533538181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70249179402218548089435149 26343442275831955533538181)
  ·
    refine ⟨4939395426718491662538409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26343442275831955533538181 4939395426718491662538409)
    ·
      refine ⟨3704546570038868746903807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4939395426718491662538409 3704546570038868746903807)
      ·
        refine ⟨5556819855058303120355711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704546570038868746903807 5556819855058303120355711)
        ·
          refine ⟨8335229782587454680533567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556819855058303120355711 8335229782587454680533567)
          ·
            refine ⟨12502844673881182020800351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8335229782587454680533567 12502844673881182020800351)
            ·
              refine ⟨18754267010821773031200527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12502844673881182020800351 18754267010821773031200527)
              ·
                refine ⟨28131400516232659546800791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18754267010821773031200527 28131400516232659546800791)
                ·
                  refine ⟨42197100774348989320201187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28131400516232659546800791 42197100774348989320201187)
                  ·
                    refine ⟨63295651161523483980301781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42197100774348989320201187 63295651161523483980301781)
                    ·
                      refine ⟨1483491824098206655788323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63295651161523483980301781 1483491824098206655788323)
                      ·
                        rfl

theorem cell23_2889090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2889090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889090 prefixEnd_2889090 := by exact prefixLift 2889090
  have htrace : WordTrace (prefixWord ++ tailWord_2889090) baseStart_2889090 baseEnd_2889090 := by
    simpa [prefixWord, tailWord_2889090, baseEnd_2889090] using wordTrace_append hprefix tailTrace_2889090
  have hstable : (prefixWord ++ tailWord_2889090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889090).length < 2 ^ (prefixWord ++ tailWord_2889090).sum := by decide
  have hdescent : baseEnd_2889090 < baseStart_2889090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889120 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_2889120 : Nat := 118140960795 + 2889120 * 2 ^ 59
def prefixEnd_2889120 : Nat := 4983230072969 + 3 ^ 40 * 2889120 * 2
def baseEnd_2889120 : Nat := 1483507228517841538413185

theorem tailTrace_2889120 : CollatzResearch.WordTrace tailWord_2889120 prefixEnd_2889120 1483507228517841538413185 := by
  unfold tailWord_2889120
  simp only [CollatzResearch.WordTrace]
  refine ⟨52687431646609568628872407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70249908862146091505163209 52687431646609568628872407)
  ·
    refine ⟨79031147469914352943308611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52687431646609568628872407 79031147469914352943308611)
    ·
      refine ⟨118546721204871529414962917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79031147469914352943308611 118546721204871529414962917)
      ·
        refine ⟨22227510225913411765305547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118546721204871529414962917 22227510225913411765305547)
        ·
          refine ⟨33341265338870117647958321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22227510225913411765305547 33341265338870117647958321)
          ·
            refine ⟨25005949004152588235968741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33341265338870117647958321 25005949004152588235968741)
            ·
              refine ⟨4688615438278610294244139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25005949004152588235968741 4688615438278610294244139)
              ·
                refine ⟨7032923157417915441366209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688615438278610294244139 7032923157417915441366209)
                ·
                  refine ⟨5274692368063436581024657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7032923157417915441366209 5274692368063436581024657)
                  ·
                    refine ⟨3956019276047577435768493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5274692368063436581024657 3956019276047577435768493)
                    ·
                      refine ⟨1483507228517841538413185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956019276047577435768493 1483507228517841538413185)
                      ·
                        rfl

theorem cell23_2889120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_2889120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889120 prefixEnd_2889120 := by exact prefixLift 2889120
  have htrace : WordTrace (prefixWord ++ tailWord_2889120) baseStart_2889120 baseEnd_2889120 := by
    simpa [prefixWord, tailWord_2889120, baseEnd_2889120] using wordTrace_append hprefix tailTrace_2889120
  have hstable : (prefixWord ++ tailWord_2889120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889120).length < 2 ^ (prefixWord ++ tailWord_2889120).sum := by decide
  have hdescent : baseEnd_2889120 < baseStart_2889120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889127 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2889127 : Nat := 118140960795 + 2889127 * 2 ^ 59
def prefixEnd_2889127 : Nat := 4983230072969 + 3 ^ 40 * 2889127 * 2
def baseEnd_2889127 : Nat := 494503607627474337008551

theorem tailTrace_2889127 : CollatzResearch.WordTrace tailWord_2889127 prefixEnd_2889127 494503607627474337008551 := by
  unfold tailWord_2889127
  simp only [CollatzResearch.WordTrace]
  refine ⟨105375118604193777453249635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70250079069462518302166423 105375118604193777453249635)
  ·
    refine ⟨158062677906290666179874453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105375118604193777453249635 158062677906290666179874453)
    ·
      refine ⟨7409188026857374977181615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158062677906290666179874453 7409188026857374977181615)
      ·
        refine ⟨11113782040286062465772423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409188026857374977181615 11113782040286062465772423)
        ·
          refine ⟨16670673060429093698658635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11113782040286062465772423 16670673060429093698658635)
          ·
            refine ⟨25006009590643640547987953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16670673060429093698658635 25006009590643640547987953)
            ·
              refine ⟨18754507192982730410990965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25006009590643640547987953 18754507192982730410990965)
              ·
                refine ⟨1758235049342130976030403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18754507192982730410990965 1758235049342130976030403)
                ·
                  refine ⟨2637352574013196464045605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758235049342130976030403 2637352574013196464045605)
                  ·
                    refine ⟨494503607627474337008551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637352574013196464045605 494503607627474337008551)
                    ·
                      rfl

theorem cell23_2889127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2889127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889127 prefixEnd_2889127 := by exact prefixLift 2889127
  have htrace : WordTrace (prefixWord ++ tailWord_2889127) baseStart_2889127 baseEnd_2889127 := by
    simpa [prefixWord, tailWord_2889127, baseEnd_2889127] using wordTrace_append hprefix tailTrace_2889127
  have hstable : (prefixWord ++ tailWord_2889127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889127).length < 2 ^ (prefixWord ++ tailWord_2889127).sum := by decide
  have hdescent : baseEnd_2889127 < baseStart_2889127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889160 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_2889160 : Nat := 118140960795 + 2889160 * 2 ^ 59
def prefixEnd_2889160 : Nat := 4983230072969 + 3 ^ 40 * 2889160 * 2
def baseEnd_2889160 : Nat := 1483527767744021381913001

theorem tailTrace_2889160 : CollatzResearch.WordTrace tailWord_2889160 prefixEnd_2889160 1483527767744021381913001 := by
  unfold tailWord_2889160
  simp only [CollatzResearch.WordTrace]
  refine ⟨52688161106537112044600467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70250881475382816059467289 52688161106537112044600467)
  ·
    refine ⟨79032241659805668066900701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52688161106537112044600467 79032241659805668066900701)
    ·
      refine ⟨29637090622427125525087763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79032241659805668066900701 29637090622427125525087763)
      ·
        refine ⟨44455635933640688287631645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29637090622427125525087763 44455635933640688287631645)
        ·
          refine ⟨16670863475115258107861867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44455635933640688287631645 16670863475115258107861867)
          ·
            refine ⟨25006295212672887161792801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16670863475115258107861867 25006295212672887161792801)
            ·
              refine ⟨18754721409504665371344601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25006295212672887161792801 18754721409504665371344601)
              ·
                refine ⟨14066041057128499028508451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18754721409504665371344601 14066041057128499028508451)
                ·
                  refine ⟨21099061585692748542762677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14066041057128499028508451 21099061585692748542762677)
                  ·
                    refine ⟨1978037023658695175884001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21099061585692748542762677 1978037023658695175884001)
                    ·
                      refine ⟨1483527767744021381913001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978037023658695175884001 1483527767744021381913001)
                      ·
                        rfl

theorem cell23_2889160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_2889160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889160 prefixEnd_2889160 := by exact prefixLift 2889160
  have htrace : WordTrace (prefixWord ++ tailWord_2889160) baseStart_2889160 baseEnd_2889160 := by
    simpa [prefixWord, tailWord_2889160, baseEnd_2889160] using wordTrace_append hprefix tailTrace_2889160
  have hstable : (prefixWord ++ tailWord_2889160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889160).length < 2 ^ (prefixWord ++ tailWord_2889160).sum := by decide
  have hdescent : baseEnd_2889160 < baseStart_2889160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889177 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 2, 3, 2]
def baseStart_2889177 : Nat := 118140960795 + 2889177 * 2 ^ 59
def prefixEnd_2889177 : Nat := 4983230072969 + 3 ^ 40 * 2889177 * 2
def baseEnd_2889177 : Nat := 1483536496915147815400423

theorem tailTrace_2889177 : CollatzResearch.WordTrace tailWord_2889177 prefixEnd_2889177 1483536496915147815400423 := by
  unfold tailWord_2889177
  simp only [CollatzResearch.WordTrace]
  refine ⟨105376942254012635992569785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70251294836008423995046523 105376942254012635992569785)
  ·
    refine ⟨79032706690509476994427339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105376942254012635992569785 79032706690509476994427339)
    ·
      refine ⟨118549060035764215491641009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79032706690509476994427339 118549060035764215491641009)
      ·
        refine ⟨88911795026823161618730757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118549060035764215491641009 88911795026823161618730757)
        ·
          refine ⟨16670961567529342803512017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88911795026823161618730757 16670961567529342803512017)
          ·
            refine ⟨12503221175647007102634013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16670961567529342803512017 12503221175647007102634013)
            ·
              refine ⟨4688707940867627663487755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12503221175647007102634013 4688707940867627663487755)
              ·
                refine ⟨7033061911301441495231633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688707940867627663487755 7033061911301441495231633)
                ·
                  refine ⟨5274796433476081121423725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7033061911301441495231633 5274796433476081121423725)
                  ·
                    refine ⟨1978048662553530420533897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5274796433476081121423725 1978048662553530420533897)
                    ·
                      refine ⟨1483536496915147815400423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978048662553530420533897 1483536496915147815400423)
                      ·
                        rfl

theorem cell23_2889177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_2889177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889177 prefixEnd_2889177 := by exact prefixLift 2889177
  have htrace : WordTrace (prefixWord ++ tailWord_2889177) baseStart_2889177 baseEnd_2889177 := by
    simpa [prefixWord, tailWord_2889177, baseEnd_2889177] using wordTrace_append hprefix tailTrace_2889177
  have hstable : (prefixWord ++ tailWord_2889177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889177).length < 2 ^ (prefixWord ++ tailWord_2889177).sum := by decide
  have hdescent : baseEnd_2889177 < baseStart_2889177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889183 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 1, 6]
def baseStart_2889183 : Nat := 118140960795 + 2889183 * 2 ^ 59
def prefixEnd_2889183 : Nat := 4983230072969 + 3 ^ 40 * 2889183 * 2
def baseEnd_2889183 : Nat := 494513192599691597308465

theorem tailTrace_2889183 : CollatzResearch.WordTrace tailWord_2889183 prefixEnd_2889183 494513192599691597308465 := by
  unfold tailWord_2889183
  simp only [CollatzResearch.WordTrace]
  refine ⟨105377161091990899017288203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70251440727993932678192135 105377161091990899017288203)
  ·
    refine ⟨158065741637986348525932305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105377161091990899017288203 158065741637986348525932305)
    ·
      refine ⟨118549306228489761394449229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158065741637986348525932305 118549306228489761394449229)
      ·
        refine ⟨44455989835683660522918461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118549306228489761394449229 44455989835683660522918461)
        ·
          refine ⟨16670996188381372696094423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44455989835683660522918461 16670996188381372696094423)
          ·
            refine ⟨25006494282572059044141635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16670996188381372696094423 25006494282572059044141635)
            ·
              refine ⟨37509741423858088566212453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25006494282572059044141635 37509741423858088566212453)
              ·
                refine ⟨7033076516973391606164835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37509741423858088566212453 7033076516973391606164835)
                ·
                  refine ⟨10549614775460087409247253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033076516973391606164835 10549614775460087409247253)
                  ·
                    refine ⟨494513192599691597308465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10549614775460087409247253 494513192599691597308465)
                    ·
                      rfl

theorem cell23_2889183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_2889183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889183 prefixEnd_2889183 := by exact prefixLift 2889183
  have htrace : WordTrace (prefixWord ++ tailWord_2889183) baseStart_2889183 baseEnd_2889183 := by
    simpa [prefixWord, tailWord_2889183, baseEnd_2889183] using wordTrace_append hprefix tailTrace_2889183
  have hstable : (prefixWord ++ tailWord_2889183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889183).length < 2 ^ (prefixWord ++ tailWord_2889183).sum := by decide
  have hdescent : baseEnd_2889183 < baseStart_2889183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889187 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 1, 5]
def baseStart_2889187 : Nat := 118140960795 + 2889187 * 2 ^ 59
def prefixEnd_2889187 : Nat := 4983230072969 + 3 ^ 40 * 2889187 * 2
def baseEnd_2889187 : Nat := 494513877240564258758459

theorem tailTrace_2889187 : CollatzResearch.WordTrace tailWord_2889187 prefixEnd_2889187 494513877240564258758459 := by
  unfold tailWord_2889187
  simp only [CollatzResearch.WordTrace]
  refine ⟨105377306983976407700433815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70251537989317605133622543 105377306983976407700433815)
  ·
    refine ⟨158065960475964611550650723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105377306983976407700433815 158065960475964611550650723)
    ·
      refine ⟨237098940713946917325976085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158065960475964611550650723 237098940713946917325976085)
      ·
        refine ⟨11114012845966261749655129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 237098940713946917325976085 11114012845966261749655129)
        ·
          refine ⟨8335509634474696312241347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11114012845966261749655129 8335509634474696312241347)
          ·
            refine ⟨12503264451712044468362021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8335509634474696312241347 12503264451712044468362021)
            ·
              refine ⟨2344362084696008337817879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12503264451712044468362021 2344362084696008337817879)
              ·
                refine ⟨3516543127044012506726819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344362084696008337817879 3516543127044012506726819)
                ·
                  refine ⟨5274814690566018760090229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516543127044012506726819 5274814690566018760090229)
                  ·
                    refine ⟨494513877240564258758459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5274814690566018760090229 494513877240564258758459)
                    ·
                      rfl

theorem cell23_2889187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 5].length) (baseStart_2889187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889187 prefixEnd_2889187 := by exact prefixLift 2889187
  have htrace : WordTrace (prefixWord ++ tailWord_2889187) baseStart_2889187 baseEnd_2889187 := by
    simpa [prefixWord, tailWord_2889187, baseEnd_2889187] using wordTrace_append hprefix tailTrace_2889187
  have hstable : (prefixWord ++ tailWord_2889187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889187).length < 2 ^ (prefixWord ++ tailWord_2889187).sum := by decide
  have hdescent : baseEnd_2889187 < baseStart_2889187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889200 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 4, 4]
def baseStart_2889200 : Nat := 118140960795 + 2889200 * 2 ^ 59
def prefixEnd_2889200 : Nat := 4983230072969 + 3 ^ 40 * 2889200 * 2
def baseEnd_2889200 : Nat := 494516102323400408470939

theorem tailTrace_2889200 : CollatzResearch.WordTrace tailWord_2889200 prefixEnd_2889200 494516102323400408470939 := by
  unfold tailWord_2889200
  simp only [CollatzResearch.WordTrace]
  refine ⟨52688890566464655460328527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70251854088619540613771369 52688890566464655460328527)
  ·
    refine ⟨79033335849696983190492791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52688890566464655460328527 79033335849696983190492791)
    ·
      refine ⟨118550003774545474785739187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79033335849696983190492791 118550003774545474785739187)
      ·
        refine ⟨177825005661818212178608781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118550003774545474785739187 177825005661818212178608781)
        ·
          refine ⟨66684377123181829566978293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177825005661818212178608781 66684377123181829566978293)
          ·
            refine ⟨6251660355298296521904215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66684377123181829566978293 6251660355298296521904215)
            ·
              refine ⟨9377490532947444782856323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251660355298296521904215 9377490532947444782856323)
              ·
                refine ⟨14066235799421167174284485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9377490532947444782856323 14066235799421167174284485)
                ·
                  refine ⟨2637419212391468845178341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14066235799421167174284485 2637419212391468845178341)
                  ·
                    refine ⟨494516102323400408470939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637419212391468845178341 494516102323400408470939)
                    ·
                      rfl

theorem cell23_2889200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_2889200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889200 prefixEnd_2889200 := by exact prefixLift 2889200
  have htrace : WordTrace (prefixWord ++ tailWord_2889200) baseStart_2889200 baseEnd_2889200 := by
    simpa [prefixWord, tailWord_2889200, baseEnd_2889200] using wordTrace_append hprefix tailTrace_2889200
  have hstable : (prefixWord ++ tailWord_2889200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889200).length < 2 ^ (prefixWord ++ tailWord_2889200).sum := by decide
  have hdescent : baseEnd_2889200 < baseStart_2889200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889217 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 1, 6]
def baseStart_2889217 : Nat := 118140960795 + 2889217 * 2 ^ 59
def prefixEnd_2889217 : Nat := 4983230072969 + 3 ^ 40 * 2889217 * 2
def baseEnd_2889217 : Nat := 494519012047109219633413

theorem tailTrace_2889217 : CollatzResearch.WordTrace tailWord_2889217 prefixEnd_2889217 494519012047109219633413 := by
  unfold tailWord_2889217
  simp only [CollatzResearch.WordTrace]
  refine ⟨105378401173867722824025905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70252267449245148549350603 105378401173867722824025905)
  ·
    refine ⟨79033800880400792118019429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105378401173867722824025905 79033800880400792118019429)
    ·
      refine ⟨14818837665075148522128643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79033800880400792118019429 14818837665075148522128643)
      ·
        refine ⟨22228256497612722783192965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14818837665075148522128643 22228256497612722783192965)
        ·
          refine ⟨4167798093302385521848681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22228256497612722783192965 4167798093302385521848681)
          ·
            refine ⟨3125848569976789141386511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4167798093302385521848681 3125848569976789141386511)
            ·
              refine ⟨4688772854965183712079767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125848569976789141386511 4688772854965183712079767)
              ·
                refine ⟨7033159282447775568119651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688772854965183712079767 7033159282447775568119651)
                ·
                  refine ⟨10549738923671663352179477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033159282447775568119651 10549738923671663352179477)
                  ·
                    refine ⟨494519012047109219633413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10549738923671663352179477 494519012047109219633413)
                    ·
                      rfl

theorem cell23_2889217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_2889217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889217 prefixEnd_2889217 := by exact prefixLift 2889217
  have htrace : WordTrace (prefixWord ++ tailWord_2889217) baseStart_2889217 baseEnd_2889217 := by
    simpa [prefixWord, tailWord_2889217, baseEnd_2889217] using wordTrace_append hprefix tailTrace_2889217
  have hstable : (prefixWord ++ tailWord_2889217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889217).length < 2 ^ (prefixWord ++ tailWord_2889217).sum := by decide
  have hdescent : baseEnd_2889217 < baseStart_2889217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889230 : List Nat := [4, 1, 1, 2, 4, 1, 1, 9]
def baseStart_2889230 : Nat := 118140960795 + 2889230 * 2 ^ 59
def prefixEnd_2889230 : Nat := 4983230072969 + 3 ^ 40 * 2889230 * 2
def baseEnd_2889230 : Nat := 54946804125549485482877

theorem tailTrace_2889230 : CollatzResearch.WordTrace tailWord_2889230 prefixEnd_2889230 54946804125549485482877 := by
  unfold tailWord_2889230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13172359415352578255531143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70252583548547084029499429 13172359415352578255531143)
  ·
    refine ⟨19758539123028867383296715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13172359415352578255531143 19758539123028867383296715)
    ·
      refine ⟨29637808684543301074945073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19758539123028867383296715 29637808684543301074945073)
      ·
        refine ⟨22228356513407475806208805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29637808684543301074945073 22228356513407475806208805)
        ·
          refine ⟨4167816846263901713664151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22228356513407475806208805 4167816846263901713664151)
          ·
            refine ⟨6251725269395852570496227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167816846263901713664151 6251725269395852570496227)
            ·
              refine ⟨9377587904093778855744341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251725269395852570496227 9377587904093778855744341)
              ·
                refine ⟨54946804125549485482877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9377587904093778855744341 54946804125549485482877)
                ·
                  rfl

theorem cell23_2889230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_2889230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889230 prefixEnd_2889230 := by exact prefixLift 2889230
  have htrace : WordTrace (prefixWord ++ tailWord_2889230) baseStart_2889230 baseEnd_2889230 := by
    simpa [prefixWord, tailWord_2889230, baseEnd_2889230] using wordTrace_append hprefix tailTrace_2889230
  have hstable : (prefixWord ++ tailWord_2889230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889230).length < 2 ^ (prefixWord ++ tailWord_2889230).sum := by decide
  have hdescent : baseEnd_2889230 < baseStart_2889230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889253 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2889253 : Nat := 118140960795 + 2889253 * 2 ^ 59
def prefixEnd_2889253 : Nat := 4983230072969 + 3 ^ 40 * 2889253 * 2
def baseEnd_2889253 : Nat := 1483575521444889518050073

theorem tailTrace_2889253 : CollatzResearch.WordTrace tailWord_2889253 prefixEnd_2889253 1483575521444889518050073 := by
  unfold tailWord_2889253
  simp only [CollatzResearch.WordTrace]
  refine ⟨105379714201737300972336413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70253142801158200648224275 105379714201737300972336413)
  ·
    refine ⟨39517392825651487864626155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105379714201737300972336413 39517392825651487864626155)
    ·
      refine ⟨59276089238477231796939233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39517392825651487864626155 59276089238477231796939233)
      ·
        refine ⟨44457066928857923847704425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59276089238477231796939233 44457066928857923847704425)
        ·
          refine ⟨33342800196643442885778319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44457066928857923847704425 33342800196643442885778319)
          ·
            refine ⟨50014200294965164328667479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33342800196643442885778319 50014200294965164328667479)
            ·
              refine ⟨75021300442447746493001219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50014200294965164328667479 75021300442447746493001219)
              ·
                refine ⟨112531950663671619739501829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75021300442447746493001219 112531950663671619739501829)
                ·
                  refine ⟨21099740749438428701156593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112531950663671619739501829 21099740749438428701156593)
                  ·
                    refine ⟨15824805562078821525867445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21099740749438428701156593 15824805562078821525867445)
                    ·
                      refine ⟨1483575521444889518050073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15824805562078821525867445 1483575521444889518050073)
                      ·
                        rfl

theorem cell23_2889253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2889253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889253 prefixEnd_2889253 := by exact prefixLift 2889253
  have htrace : WordTrace (prefixWord ++ tailWord_2889253) baseStart_2889253 baseEnd_2889253 := by
    simpa [prefixWord, tailWord_2889253, baseEnd_2889253] using wordTrace_append hprefix tailTrace_2889253
  have hstable : (prefixWord ++ tailWord_2889253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889253).length < 2 ^ (prefixWord ++ tailWord_2889253).sum := by decide
  have hdescent : baseEnd_2889253 < baseStart_2889253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889258 : List Nat := [3, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2889258 : Nat := 118140960795 + 2889258 * 2 ^ 59
def prefixEnd_2889258 : Nat := 4983230072969 + 3 ^ 40 * 2889258 * 2
def baseEnd_2889258 : Nat := 1483578088848161998487551

theorem tailTrace_2889258 : CollatzResearch.WordTrace tailWord_2889258 prefixEnd_2889258 1483578088848161998487551 := by
  unfold tailWord_2889258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26344974141679796706567107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70253264377812791217512285 26344974141679796706567107)
  ·
    refine ⟨39517461212519695059850661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26344974141679796706567107 39517461212519695059850661)
    ·
      refine ⟨7409523977347442823721999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39517461212519695059850661 7409523977347442823721999)
      ·
        refine ⟨11114285966021164235582999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409523977347442823721999 11114285966021164235582999)
        ·
          refine ⟨16671428949031746353374499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11114285966021164235582999 16671428949031746353374499)
          ·
            refine ⟨25007143423547619530061749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16671428949031746353374499 25007143423547619530061749)
            ·
              refine ⟨2344419695957589330943289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25007143423547619530061749 2344419695957589330943289)
              ·
                refine ⟨1758314771968191998207467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344419695957589330943289 1758314771968191998207467)
                ·
                  refine ⟨2637472157952287997311201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758314771968191998207467 2637472157952287997311201)
                  ·
                    refine ⟨1978104118464215997983401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637472157952287997311201 1978104118464215997983401)
                    ·
                      refine ⟨1483578088848161998487551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978104118464215997983401 1483578088848161998487551)
                      ·
                        rfl

theorem cell23_2889258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2889258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889258 prefixEnd_2889258 := by exact prefixLift 2889258
  have htrace : WordTrace (prefixWord ++ tailWord_2889258) baseStart_2889258 baseEnd_2889258 := by
    simpa [prefixWord, tailWord_2889258, baseEnd_2889258] using wordTrace_append hprefix tailTrace_2889258
  have hstable : (prefixWord ++ tailWord_2889258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889258).length < 2 ^ (prefixWord ++ tailWord_2889258).sum := by decide
  have hdescent : baseEnd_2889258 < baseStart_2889258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889297 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 1, 4, 2]
def baseStart_2889297 : Nat := 118140960795 + 2889297 * 2 ^ 59
def prefixEnd_2889297 : Nat := 4983230072969 + 3 ^ 40 * 2889297 * 2
def baseEnd_2889297 : Nat := 1483598114593687345899871

theorem tailTrace_2889297 : CollatzResearch.WordTrace tailWord_2889297 prefixEnd_2889297 1483598114593687345899871 := by
  unfold tailWord_2889297
  simp only [CollatzResearch.WordTrace]
  refine ⟨105381319013577896486938145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70254212675718597657958763 105381319013577896486938145)
  ·
    refine ⟨79035989260183422365203609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105381319013577896486938145 79035989260183422365203609)
    ·
      refine ⟨59276991945137566773902707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79035989260183422365203609 59276991945137566773902707)
      ·
        refine ⟨88915487917706350160854061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59276991945137566773902707 88915487917706350160854061)
        ·
          refine ⟨33343307969139881310320273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88915487917706350160854061 33343307969139881310320273)
          ·
            refine ⟨25007480976854910982740205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33343307969139881310320273 25007480976854910982740205)
            ·
              refine ⟨9377805366320591618527577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25007480976854910982740205 9377805366320591618527577)
              ·
                refine ⟨7033354024740443713895683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9377805366320591618527577 7033354024740443713895683)
                ·
                  refine ⟨10550031037110665570843525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033354024740443713895683 10550031037110665570843525)
                  ·
                    refine ⟨1978130819458249794533161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10550031037110665570843525 1978130819458249794533161)
                    ·
                      refine ⟨1483598114593687345899871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978130819458249794533161 1483598114593687345899871)
                      ·
                        rfl

theorem cell23_2889297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_2889297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889297 prefixEnd_2889297 := by exact prefixLift 2889297
  have htrace : WordTrace (prefixWord ++ tailWord_2889297) baseStart_2889297 baseEnd_2889297 := by
    simpa [prefixWord, tailWord_2889297, baseEnd_2889297] using wordTrace_append hprefix tailTrace_2889297
  have hstable : (prefixWord ++ tailWord_2889297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889297).length < 2 ^ (prefixWord ++ tailWord_2889297).sum := by decide
  have hdescent : baseEnd_2889297 < baseStart_2889297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889300 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2889300 : Nat := 118140960795 + 2889300 * 2 ^ 59
def prefixEnd_2889300 : Nat := 4983230072969 + 3 ^ 40 * 2889300 * 2
def baseEnd_2889300 : Nat := 1483599655035650834162357

theorem tailTrace_2889300 : CollatzResearch.WordTrace tailWord_2889300 prefixEnd_2889300 1483599655035650834162357 := by
  unfold tailWord_2889300
  simp only [CollatzResearch.WordTrace]
  refine ⟨52690714216283513999648677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70254285621711351999531569 52690714216283513999648677)
  ·
    refine ⟨9879508915553158874934127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52690714216283513999648677 9879508915553158874934127)
    ·
      refine ⟨14819263373329738312401191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9879508915553158874934127 14819263373329738312401191)
      ·
        refine ⟨22228895059994607468601787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14819263373329738312401191 22228895059994607468601787)
        ·
          refine ⟨33343342589991911202902681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22228895059994607468601787 33343342589991911202902681)
          ·
            refine ⟨25007506942493933402177011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33343342589991911202902681 25007506942493933402177011)
            ·
              refine ⟨37511260413740900103265517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25007506942493933402177011 37511260413740900103265517)
              ·
                refine ⟨14066722655152837538724569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37511260413740900103265517 14066722655152837538724569)
                ·
                  refine ⟨10550041991364628154043427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14066722655152837538724569 10550041991364628154043427)
                  ·
                    refine ⟨15825062987046942231065141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10550041991364628154043427 15825062987046942231065141)
                    ·
                      refine ⟨1483599655035650834162357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15825062987046942231065141 1483599655035650834162357)
                      ·
                        rfl

theorem cell23_2889300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2889300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889300 prefixEnd_2889300 := by exact prefixLift 2889300
  have htrace : WordTrace (prefixWord ++ tailWord_2889300) baseStart_2889300 baseEnd_2889300 := by
    simpa [prefixWord, tailWord_2889300, baseEnd_2889300] using wordTrace_append hprefix tailTrace_2889300
  have hstable : (prefixWord ++ tailWord_2889300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889300).length < 2 ^ (prefixWord ++ tailWord_2889300).sum := by decide
  have hdescent : baseEnd_2889300 < baseStart_2889300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889309 : List Nat := [1, 4, 4, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2889309 : Nat := 118140960795 + 2889309 * 2 ^ 59
def prefixEnd_2889309 : Nat := 4983230072969 + 3 ^ 40 * 2889309 * 2
def baseEnd_2889309 : Nat := 1483604276361541298949817

theorem tailTrace_2889309 : CollatzResearch.WordTrace tailWord_2889309 prefixEnd_2889309 1483604276361541298949817 := by
  unfold tailWord_2889309
  simp only [CollatzResearch.WordTrace]
  refine ⟨105381756689534422536374981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70254504459689615024249987 105381756689534422536374981)
  ·
    refine ⟨19759079379287704225570309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105381756689534422536374981 19759079379287704225570309)
    ·
      refine ⟨3704827383616444542294433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19759079379287704225570309 3704827383616444542294433)
      ·
        refine ⟨2778620537712333406720825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3704827383616444542294433 2778620537712333406720825)
        ·
          refine ⟨2083965403284250055040619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778620537712333406720825 2083965403284250055040619)
          ·
            refine ⟨3125948104926375082560929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083965403284250055040619 3125948104926375082560929)
            ·
              refine ⟨2344461078694781311920697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125948104926375082560929 2344461078694781311920697)
              ·
                refine ⟨1758345809021085983940523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344461078694781311920697 1758345809021085983940523)
                ·
                  refine ⟨2637518713531628975910785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758345809021085983940523 2637518713531628975910785)
                  ·
                    refine ⟨1978139035148721731933089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637518713531628975910785 1978139035148721731933089)
                    ·
                      refine ⟨1483604276361541298949817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978139035148721731933089 1483604276361541298949817)
                      ·
                        rfl

theorem cell23_2889309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2889309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889309 prefixEnd_2889309 := by exact prefixLift 2889309
  have htrace : WordTrace (prefixWord ++ tailWord_2889309) baseStart_2889309 baseEnd_2889309 := by
    simpa [prefixWord, tailWord_2889309, baseEnd_2889309] using wordTrace_append hprefix tailTrace_2889309
  have hstable : (prefixWord ++ tailWord_2889309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889309).length < 2 ^ (prefixWord ++ tailWord_2889309).sum := by decide
  have hdescent : baseEnd_2889309 < baseStart_2889309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889354 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_2889354 : Nat := 118140960795 + 2889354 * 2 ^ 59
def prefixEnd_2889354 : Nat := 4983230072969 + 3 ^ 40 * 2889354 * 2
def baseEnd_2889354 : Nat := 164847486998999291431901

theorem tailTrace_2889354 : CollatzResearch.WordTrace tailWord_2889354 prefixEnd_2889354 164847486998999291431901 := by
  unfold tailWord_2889354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26345849493592848805440779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70255598649580930147842077 26345849493592848805440779)
  ·
    refine ⟨39518774240389273208161169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26345849493592848805440779 39518774240389273208161169)
    ·
      refine ⟨29639080680291954906120877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39518774240389273208161169 29639080680291954906120877)
      ·
        refine ⟨11114655255109483089795329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29639080680291954906120877 11114655255109483089795329)
        ·
          refine ⟨8335991441332112317346497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11114655255109483089795329 8335991441332112317346497)
          ·
            refine ⟨6251993580999084238009873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8335991441332112317346497 6251993580999084238009873)
            ·
              refine ⟨4688995185749313178507405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6251993580999084238009873 4688995185749313178507405)
              ·
                refine ⟨1758373194655992441940277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4688995185749313178507405 1758373194655992441940277)
                ·
                  refine ⟨164847486998999291431901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758373194655992441940277 164847486998999291431901)
                  ·
                    rfl

theorem cell23_2889354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_2889354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889354 prefixEnd_2889354 := by exact prefixLift 2889354
  have htrace : WordTrace (prefixWord ++ tailWord_2889354) baseStart_2889354 baseEnd_2889354 := by
    simpa [prefixWord, tailWord_2889354, baseEnd_2889354] using wordTrace_append hprefix tailTrace_2889354
  have hstable : (prefixWord ++ tailWord_2889354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889354).length < 2 ^ (prefixWord ++ tailWord_2889354).sum := by decide
  have hdescent : baseEnd_2889354 < baseStart_2889354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889407 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_2889407 : Nat := 118140960795 + 2889407 * 2 ^ 59
def prefixEnd_2889407 : Nat := 4983230072969 + 3 ^ 40 * 2889407 * 2
def baseEnd_2889407 : Nat := 1483654597465681915524365

theorem tailTrace_2889407 : CollatzResearch.WordTrace tailWord_2889407 prefixEnd_2889407 1483654597465681915524365 := by
  unfold tailWord_2889407
  simp only [CollatzResearch.WordTrace]
  refine ⟨105385331043179385273442475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70256887362119590182294983 105385331043179385273442475)
  ·
    refine ⟨158077996564769077910163713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105385331043179385273442475 158077996564769077910163713)
    ·
      refine ⟨118558497423576808432622785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158077996564769077910163713 118558497423576808432622785)
      ·
        refine ⟨88918873067682606324467089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118558497423576808432622785 88918873067682606324467089)
        ·
          refine ⟨66689154800761954743350317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88918873067682606324467089 66689154800761954743350317)
          ·
            refine ⟨25008433050285733028756369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66689154800761954743350317 25008433050285733028756369)
            ·
              refine ⟨18756324787714299771567277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25008433050285733028756369 18756324787714299771567277)
              ·
                refine ⟨7033621795392862414337729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18756324787714299771567277 7033621795392862414337729)
                ·
                  refine ⟨5275216346544646810753297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7033621795392862414337729 5275216346544646810753297)
                  ·
                    refine ⟨3956412259908485108064973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275216346544646810753297 3956412259908485108064973)
                    ·
                      refine ⟨1483654597465681915524365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956412259908485108064973 1483654597465681915524365)
                      ·
                        rfl

theorem cell23_2889407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_2889407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889407 prefixEnd_2889407 := by exact prefixLift 2889407
  have htrace : WordTrace (prefixWord ++ tailWord_2889407) baseStart_2889407 baseEnd_2889407 := by
    simpa [prefixWord, tailWord_2889407, baseEnd_2889407] using wordTrace_append hprefix tailTrace_2889407
  have hstable : (prefixWord ++ tailWord_2889407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889407).length < 2 ^ (prefixWord ++ tailWord_2889407).sum := by decide
  have hdescent : baseEnd_2889407 < baseStart_2889407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889421 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2889421 : Nat := 118140960795 + 2889421 * 2 ^ 59
def prefixEnd_2889421 : Nat := 4983230072969 + 3 ^ 40 * 2889421 * 2
def baseEnd_2889421 : Nat := 1483661786194844860749301

theorem tailTrace_2889421 : CollatzResearch.WordTrace tailWord_2889421 prefixEnd_2889421 1483661786194844860749301 := by
  unfold tailWord_2889421
  simp only [CollatzResearch.WordTrace]
  refine ⟨105385841665128665664452117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70257227776752443776301411 105385841665128665664452117)
  ·
    refine ⟨4939961328052906203021193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105385841665128665664452117 4939961328052906203021193)
    ·
      refine ⟨3704970996039679652265895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4939961328052906203021193 3704970996039679652265895)
      ·
        refine ⟨5557456494059519478398843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704970996039679652265895 5557456494059519478398843)
        ·
          refine ⟨8336184741089279217598265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5557456494059519478398843 8336184741089279217598265)
          ·
            refine ⟨6252138555816959413198699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8336184741089279217598265 6252138555816959413198699)
            ·
              refine ⟨9378207833725439119798049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252138555816959413198699 9378207833725439119798049)
              ·
                refine ⟨7033655875294079339848537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9378207833725439119798049 7033655875294079339848537)
                ·
                  refine ⟨5275241906470559504886403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7033655875294079339848537 5275241906470559504886403)
                  ·
                    refine ⟨7912862859705839257329605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5275241906470559504886403 7912862859705839257329605)
                    ·
                      refine ⟨1483661786194844860749301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7912862859705839257329605 1483661786194844860749301)
                      ·
                        rfl

theorem cell23_2889421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2889421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889421 prefixEnd_2889421 := by exact prefixLift 2889421
  have htrace : WordTrace (prefixWord ++ tailWord_2889421) baseStart_2889421 baseEnd_2889421 := by
    simpa [prefixWord, tailWord_2889421, baseEnd_2889421] using wordTrace_append hprefix tailTrace_2889421
  have hstable : (prefixWord ++ tailWord_2889421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889421).length < 2 ^ (prefixWord ++ tailWord_2889421).sum := by decide
  have hdescent : baseEnd_2889421 < baseStart_2889421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889431 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 1, 4]
def baseStart_2889431 : Nat := 118140960795 + 2889431 * 2 ^ 59
def prefixEnd_2889431 : Nat := 4983230072969 + 3 ^ 40 * 2889431 * 2
def baseEnd_2889431 : Nat := 494555640333796607208085

theorem tailTrace_2889431 : CollatzResearch.WordTrace tailWord_2889431 prefixEnd_2889431 494555640333796607208085 := by
  unfold tailWord_2889431
  simp only [CollatzResearch.WordTrace]
  refine ⟨105386206395092437372316147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70257470930061624914877431 105386206395092437372316147)
  ·
    refine ⟨158079309592638656058474221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105386206395092437372316147 158079309592638656058474221)
    ·
      refine ⟨59279741097239496021927833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158079309592638656058474221 59279741097239496021927833)
      ·
        refine ⟨44459805822929622016445875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59279741097239496021927833 44459805822929622016445875)
        ·
          refine ⟨66689708734394433024668813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44459805822929622016445875 66689708734394433024668813)
          ·
            refine ⟨25008640775397912384250805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66689708734394433024668813 25008640775397912384250805)
            ·
              refine ⟨2344560072693554286023513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25008640775397912384250805 2344560072693554286023513)
              ·
                refine ⟨1758420054520165714517635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344560072693554286023513 1758420054520165714517635)
                ·
                  refine ⟨2637630081780248571776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758420054520165714517635 2637630081780248571776453)
                  ·
                    refine ⟨494555640333796607208085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637630081780248571776453 494555640333796607208085)
                    ·
                      rfl

theorem cell23_2889431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_2889431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889431 prefixEnd_2889431 := by exact prefixLift 2889431
  have htrace : WordTrace (prefixWord ++ tailWord_2889431) baseStart_2889431 baseEnd_2889431 := by
    simpa [prefixWord, tailWord_2889431, baseEnd_2889431] using wordTrace_append hprefix tailTrace_2889431
  have hstable : (prefixWord ++ tailWord_2889431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889431).length < 2 ^ (prefixWord ++ tailWord_2889431).sum := by decide
  have hdescent : baseEnd_2889431 < baseStart_2889431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889454 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_2889454 : Nat := 118140960795 + 2889454 * 2 ^ 59
def prefixEnd_2889454 : Nat := 4983230072969 + 3 ^ 40 * 2889454 * 2
def baseEnd_2889454 : Nat := 1483678731056443231636649

theorem tailTrace_2889454 : CollatzResearch.WordTrace tailWord_2889454 prefixEnd_2889454 1483678731056443231636649 := by
  unfold tailWord_2889454
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173380659251139037550427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70258030182672741533602277 13173380659251139037550427)
  ·
    refine ⟨19760070988876708556325641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13173380659251139037550427 19760070988876708556325641)
    ·
      refine ⟨14820053241657531417244231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19760070988876708556325641 14820053241657531417244231)
      ·
        refine ⟨22230079862486297125866347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14820053241657531417244231 22230079862486297125866347)
        ·
          refine ⟨33345119793729445688799521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22230079862486297125866347 33345119793729445688799521)
          ·
            refine ⟨25008839845297084266599641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33345119793729445688799521 25008839845297084266599641)
            ·
              refine ⟨18756629883972813199949731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25008839845297084266599641 18756629883972813199949731)
              ·
                refine ⟨28134944825959219799924597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18756629883972813199949731 28134944825959219799924597)
                ·
                  refine ⟨2637651077433676856242931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28134944825959219799924597 2637651077433676856242931)
                  ·
                    refine ⟨3956476616150515284364397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2637651077433676856242931 3956476616150515284364397)
                    ·
                      refine ⟨1483678731056443231636649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956476616150515284364397 1483678731056443231636649)
                      ·
                        rfl

theorem cell23_2889454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_2889454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889454 prefixEnd_2889454 := by exact prefixLift 2889454
  have htrace : WordTrace (prefixWord ++ tailWord_2889454) baseStart_2889454 baseEnd_2889454 := by
    simpa [prefixWord, tailWord_2889454, baseEnd_2889454] using wordTrace_append hprefix tailTrace_2889454
  have hstable : (prefixWord ++ tailWord_2889454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889454).length < 2 ^ (prefixWord ++ tailWord_2889454).sum := by decide
  have hdescent : baseEnd_2889454 < baseStart_2889454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889457 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_2889457 : Nat := 118140960795 + 2889457 * 2 ^ 59
def prefixEnd_2889457 : Nat := 4983230072969 + 3 ^ 40 * 2889457 * 2
def baseEnd_2889457 : Nat := 494560090499468906633045

theorem tailTrace_2889457 : CollatzResearch.WordTrace tailWord_2889457 prefixEnd_2889457 494560090499468906633045 := by
  unfold tailWord_2889457
  simp only [CollatzResearch.WordTrace]
  refine ⟨105387154692998243812762625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70258103128665495875175083 105387154692998243812762625)
  ·
    refine ⟨79040366019748682859571969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105387154692998243812762625 79040366019748682859571969)
    ·
      refine ⟨59280274514811512144678977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79040366019748682859571969 59280274514811512144678977)
      ·
        refine ⟨44460205886108634108509233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59280274514811512144678977 44460205886108634108509233)
        ·
          refine ⟨33345154414581475581381925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44460205886108634108509233 33345154414581475581381925)
          ·
            refine ⟨6252216452734026671509111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33345154414581475581381925 6252216452734026671509111)
            ·
              refine ⟨9378324679101040007263667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252216452734026671509111 9378324679101040007263667)
              ·
                refine ⟨14067487018651560010895501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9378324679101040007263667 14067487018651560010895501)
                ·
                  refine ⟨5275307631994335004085813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14067487018651560010895501 5275307631994335004085813)
                  ·
                    refine ⟨494560090499468906633045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5275307631994335004085813 494560090499468906633045)
                    ·
                      rfl

theorem cell23_2889457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_2889457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889457 prefixEnd_2889457 := by exact prefixLift 2889457
  have htrace : WordTrace (prefixWord ++ tailWord_2889457) baseStart_2889457 baseEnd_2889457 := by
    simpa [prefixWord, tailWord_2889457, baseEnd_2889457] using wordTrace_append hprefix tailTrace_2889457
  have hstable : (prefixWord ++ tailWord_2889457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889457).length < 2 ^ (prefixWord ++ tailWord_2889457).sum := by decide
  have hdescent : baseEnd_2889457 < baseStart_2889457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889504 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 2, 4]
def baseStart_2889504 : Nat := 118140960795 + 2889504 * 2 ^ 59
def prefixEnd_2889504 : Nat := 4983230072969 + 3 ^ 40 * 2889504 * 2
def baseEnd_2889504 : Nat := 494568135029722678670473

theorem tailTrace_2889504 : CollatzResearch.WordTrace tailWord_2889504 prefixEnd_2889504 494568135029722678670473 := by
  unfold tailWord_2889504
  simp only [CollatzResearch.WordTrace]
  refine ⟨52694434461913985419861783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70259245949218647226482377 52694434461913985419861783)
  ·
    refine ⟨79041651692870978129792675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52694434461913985419861783 79041651692870978129792675)
    ·
      refine ⟨118562477539306467194689013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79041651692870978129792675 118562477539306467194689013)
      ·
        refine ⟨11115232269309981299502095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118562477539306467194689013 11115232269309981299502095)
        ·
          refine ⟨16672848403964971949253143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11115232269309981299502095 16672848403964971949253143)
          ·
            refine ⟨25009272605947457923879715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16672848403964971949253143 25009272605947457923879715)
            ·
              refine ⟨37513908908921186885819573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25009272605947457923879715 37513908908921186885819573)
              ·
                refine ⟨3516928960211361270545585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37513908908921186885819573 3516928960211361270545585)
                ·
                  refine ⟨2637696720158520952909189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516928960211361270545585 2637696720158520952909189)
                  ·
                    refine ⟨494568135029722678670473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2637696720158520952909189 494568135029722678670473)
                    ·
                      rfl

theorem cell23_2889504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 4].length) (baseStart_2889504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889504 prefixEnd_2889504 := by exact prefixLift 2889504
  have htrace : WordTrace (prefixWord ++ tailWord_2889504) baseStart_2889504 baseEnd_2889504 := by
    simpa [prefixWord, tailWord_2889504, baseEnd_2889504] using wordTrace_append hprefix tailTrace_2889504
  have hstable : (prefixWord ++ tailWord_2889504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889504).length < 2 ^ (prefixWord ++ tailWord_2889504).sum := by decide
  have hdescent : baseEnd_2889504 < baseStart_2889504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889507 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4]
def baseStart_2889507 : Nat := 118140960795 + 2889507 * 2 ^ 59
def prefixEnd_2889507 : Nat := 4983230072969 + 3 ^ 40 * 2889507 * 2
def baseEnd_2889507 : Nat := 1483705945531131524273905

theorem tailTrace_2889507 : CollatzResearch.WordTrace tailWord_2889507 prefixEnd_2889507 1483705945531131524273905 := by
  unfold tailWord_2889507
  simp only [CollatzResearch.WordTrace]
  refine ⟨105388978342817102352082775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70259318895211401568055183 105388978342817102352082775)
  ·
    refine ⟨158083467514225653528124163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105388978342817102352082775 158083467514225653528124163)
    ·
      refine ⟨237125201271338480292186245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158083467514225653528124163 237125201271338480292186245)
      ·
        refine ⟨44460975238375965054784921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237125201271338480292186245 44460975238375965054784921)
        ·
          refine ⟨33345731428781973791088691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44460975238375965054784921 33345731428781973791088691)
          ·
            refine ⟨50018597143172960686633037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33345731428781973791088691 50018597143172960686633037)
            ·
              refine ⟨18756973928689860257487389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50018597143172960686633037 18756973928689860257487389)
              ·
                refine ⟨7033865223258697596557771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18756973928689860257487389 7033865223258697596557771)
                ·
                  refine ⟨10550797834888046394836657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033865223258697596557771 10550797834888046394836657)
                  ·
                    refine ⟨7913098376166034796127493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10550797834888046394836657 7913098376166034796127493)
                    ·
                      refine ⟨1483705945531131524273905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7913098376166034796127493 1483705945531131524273905)
                      ·
                        rfl

theorem cell23_2889507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_2889507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889507 prefixEnd_2889507 := by exact prefixLift 2889507
  have htrace : WordTrace (prefixWord ++ tailWord_2889507) baseStart_2889507 baseEnd_2889507 := by
    simpa [prefixWord, tailWord_2889507, baseEnd_2889507] using wordTrace_append hprefix tailTrace_2889507
  have hstable : (prefixWord ++ tailWord_2889507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889507).length < 2 ^ (prefixWord ++ tailWord_2889507).sum := by decide
  have hdescent : baseEnd_2889507 < baseStart_2889507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889527 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_2889527 : Nat := 118140960795 + 2889527 * 2 ^ 59
def prefixEnd_2889527 : Nat := 4983230072969 + 3 ^ 40 * 2889527 * 2
def baseEnd_2889527 : Nat := 1483716215144221446023813

theorem tailTrace_2889527 : CollatzResearch.WordTrace tailWord_2889527 prefixEnd_2889527 1483716215144221446023813 := by
  unfold tailWord_2889527
  simp only [CollatzResearch.WordTrace]
  refine ⟨105389707802744645767810835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70259805201829763845207223 105389707802744645767810835)
  ·
    refine ⟨158084561704116968651716253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105389707802744645767810835 158084561704116968651716253)
    ·
      refine ⟨59281710639043863244393595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158084561704116968651716253 59281710639043863244393595)
      ·
        refine ⟨88922565958565794866590393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59281710639043863244393595 88922565958565794866590393)
        ·
          refine ⟨66691924468924346149942795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88922565958565794866590393 66691924468924346149942795)
          ·
            refine ⟨100037886703386519224914193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66691924468924346149942795 100037886703386519224914193)
            ·
              refine ⟨75028415027539889418685645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100037886703386519224914193 75028415027539889418685645)
              ·
                refine ⟨28135655635327458532007117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75028415027539889418685645 28135655635327458532007117)
                ·
                  refine ⟨10550870863247796949502669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28135655635327458532007117 10550870863247796949502669)
                  ·
                    refine ⟨3956576573717923856063501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10550870863247796949502669 3956576573717923856063501)
                    ·
                      refine ⟨1483716215144221446023813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956576573717923856063501 1483716215144221446023813)
                      ·
                        rfl

theorem cell23_2889527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_2889527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889527 prefixEnd_2889527 := by exact prefixLift 2889527
  have htrace : WordTrace (prefixWord ++ tailWord_2889527) baseStart_2889527 baseEnd_2889527 := by
    simpa [prefixWord, tailWord_2889527, baseEnd_2889527] using wordTrace_append hprefix tailTrace_2889527
  have hstable : (prefixWord ++ tailWord_2889527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889527).length < 2 ^ (prefixWord ++ tailWord_2889527).sum := by decide
  have hdescent : baseEnd_2889527 < baseStart_2889527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889528 : List Nat := [2, 1, 2, 1, 3, 3, 1, 5, 1, 2, 2]
def baseStart_2889528 : Nat := 118140960795 + 2889528 * 2 ^ 59
def prefixEnd_2889528 : Nat := 4983230072969 + 3 ^ 40 * 2889528 * 2
def baseEnd_2889528 : Nat := 1483716728624875942111309

theorem tailTrace_2889528 : CollatzResearch.WordTrace tailWord_2889528 prefixEnd_2889528 1483716728624875942111309 := by
  unfold tailWord_2889528
  simp only [CollatzResearch.WordTrace]
  refine ⟨52694872137870511469298619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70259829517160681959064825 52694872137870511469298619)
  ·
    refine ⟨79042308206805767203947929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52694872137870511469298619 79042308206805767203947929)
    ·
      refine ⟨59281731155104325402960947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79042308206805767203947929 59281731155104325402960947)
      ·
        refine ⟨88922596732656488104441421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59281731155104325402960947 88922596732656488104441421)
        ·
          refine ⟨33345973774746183039165533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88922596732656488104441421 33345973774746183039165533)
          ·
            refine ⟨12504740165529818639687075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33345973774746183039165533 12504740165529818639687075)
            ·
              refine ⟨18757110248294727959530613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12504740165529818639687075 18757110248294727959530613)
              ·
                refine ⟨1758479085777630746205995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18757110248294727959530613 1758479085777630746205995)
                ·
                  refine ⟨2637718628666446119308993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758479085777630746205995 2637718628666446119308993)
                  ·
                    refine ⟨1978288971499834589481745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2637718628666446119308993 1978288971499834589481745)
                    ·
                      refine ⟨1483716728624875942111309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978288971499834589481745 1483716728624875942111309)
                      ·
                        rfl

theorem cell23_2889528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 1, 2, 2].length) (baseStart_2889528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889528 prefixEnd_2889528 := by exact prefixLift 2889528
  have htrace : WordTrace (prefixWord ++ tailWord_2889528) baseStart_2889528 baseEnd_2889528 := by
    simpa [prefixWord, tailWord_2889528, baseEnd_2889528] using wordTrace_append hprefix tailTrace_2889528
  have hstable : (prefixWord ++ tailWord_2889528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889528).length < 2 ^ (prefixWord ++ tailWord_2889528).sum := by decide
  have hdescent : baseEnd_2889528 < baseStart_2889528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889584 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 3, 4, 2]
def baseStart_2889584 : Nat := 118140960795 + 2889584 * 2 ^ 59
def prefixEnd_2889584 : Nat := 4983230072969 + 3 ^ 40 * 2889584 * 2
def baseEnd_2889584 : Nat := 1483745483541527723011051

theorem tailTrace_2889584 : CollatzResearch.WordTrace tailWord_2889584 prefixEnd_2889584 1483745483541527723011051 := by
  unfold tailWord_2889584
  simp only [CollatzResearch.WordTrace]
  refine ⟨52695893381769072251317903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70261191175692096335090537 52695893381769072251317903)
  ·
    refine ⟨79043840072653608376976855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52695893381769072251317903 79043840072653608376976855)
    ·
      refine ⟨118565760108980412565465283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79043840072653608376976855 118565760108980412565465283)
      ·
        refine ⟨177848640163470618848197925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118565760108980412565465283 177848640163470618848197925)
        ·
          refine ⟨33346620030650741034037111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177848640163470618848197925 33346620030650741034037111)
          ·
            refine ⟨50019930045976111551055667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33346620030650741034037111 50019930045976111551055667)
            ·
              refine ⟨75029895068964167326583501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50019930045976111551055667 75029895068964167326583501)
              ·
                refine ⟨28136210650861562747468813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75029895068964167326583501 28136210650861562747468813)
                ·
                  refine ⟨10551078994073086030300805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28136210650861562747468813 10551078994073086030300805)
                  ·
                    refine ⟨1978327311388703630681401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10551078994073086030300805 1978327311388703630681401)
                    ·
                      refine ⟨1483745483541527723011051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978327311388703630681401 1483745483541527723011051)
                      ·
                        rfl

theorem cell23_2889584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 3, 4, 2].length) (baseStart_2889584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889584 prefixEnd_2889584 := by exact prefixLift 2889584
  have htrace : WordTrace (prefixWord ++ tailWord_2889584) baseStart_2889584 baseEnd_2889584 := by
    simpa [prefixWord, tailWord_2889584, baseEnd_2889584] using wordTrace_append hprefix tailTrace_2889584
  have hstable : (prefixWord ++ tailWord_2889584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889584).length < 2 ^ (prefixWord ++ tailWord_2889584).sum := by decide
  have hdescent : baseEnd_2889584 < baseStart_2889584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889587 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 3]
def baseStart_2889587 : Nat := 118140960795 + 2889587 * 2 ^ 59
def prefixEnd_2889587 : Nat := 4983230072969 + 3 ^ 40 * 2889587 * 2
def baseEnd_2889587 : Nat := 1483747023983491211273537

theorem tailTrace_2889587 : CollatzResearch.WordTrace tailWord_2889587 prefixEnd_2889587 1483747023983491211273537 := by
  unfold tailWord_2889587
  simp only [CollatzResearch.WordTrace]
  refine ⟨105391896182527276014995015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70261264121684850676663343 105391896182527276014995015)
  ·
    refine ⟨158087844273790914022492523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105391896182527276014995015 158087844273790914022492523)
    ·
      refine ⟨237131766410686371033738785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158087844273790914022492523 237131766410686371033738785)
      ·
        refine ⟨177848824808014778275304089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237131766410686371033738785 177848824808014778275304089)
        ·
          refine ⟨133386618606011083706478067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177848824808014778275304089 133386618606011083706478067)
          ·
            refine ⟨200079927909016625559717101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133386618606011083706478067 200079927909016625559717101)
            ·
              refine ⟨75029972965881234584893913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200079927909016625559717101 75029972965881234584893913)
              ·
                refine ⟨56272479724410925938670435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75029972965881234584893913 56272479724410925938670435)
                ·
                  refine ⟨84408719586616388908005653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56272479724410925938670435 84408719586616388908005653)
                  ·
                    refine ⟨3956658730622643230062765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84408719586616388908005653 3956658730622643230062765)
                    ·
                      refine ⟨1483747023983491211273537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956658730622643230062765 1483747023983491211273537)
                      ·
                        rfl

theorem cell23_2889587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_2889587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889587 prefixEnd_2889587 := by exact prefixLift 2889587
  have htrace : WordTrace (prefixWord ++ tailWord_2889587) baseStart_2889587 baseEnd_2889587 := by
    simpa [prefixWord, tailWord_2889587, baseEnd_2889587] using wordTrace_append hprefix tailTrace_2889587
  have hstable : (prefixWord ++ tailWord_2889587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889587).length < 2 ^ (prefixWord ++ tailWord_2889587).sum := by decide
  have hdescent : baseEnd_2889587 < baseStart_2889587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889622 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2889622 : Nat := 118140960795 + 2889622 * 2 ^ 59
def prefixEnd_2889622 : Nat := 4983230072969 + 3 ^ 40 * 2889622 * 2
def baseEnd_2889622 : Nat := 1483764995806398574335877

theorem tailTrace_2889622 : CollatzResearch.WordTrace tailWord_2889622 prefixEnd_2889622 1483764995806398574335877 := by
  unfold tailWord_2889622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587073296087529812032445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70262115158266984661679413 6587073296087529812032445)
  ·
    refine ⟨2470152486032823679512167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6587073296087529812032445 2470152486032823679512167)
    ·
      refine ⟨3705228729049235519268251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2470152486032823679512167 3705228729049235519268251)
      ·
        refine ⟨5557843093573853278902377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705228729049235519268251 5557843093573853278902377)
        ·
          refine ⟨4168382320180389959176783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5557843093573853278902377 4168382320180389959176783)
          ·
            refine ⟨6252573480270584938765175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168382320180389959176783 6252573480270584938765175)
            ·
              refine ⟨9378860220405877408147763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252573480270584938765175 9378860220405877408147763)
              ·
                refine ⟨14068290330608816112221645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9378860220405877408147763 14068290330608816112221645)
                ·
                  refine ⟨5275608873978306042083117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14068290330608816112221645 5275608873978306042083117)
                  ·
                    refine ⟨1978353327741864765781169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5275608873978306042083117 1978353327741864765781169)
                    ·
                      refine ⟨1483764995806398574335877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978353327741864765781169 1483764995806398574335877)
                      ·
                        rfl

theorem cell23_2889622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2889622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889622 prefixEnd_2889622 := by exact prefixLift 2889622
  have htrace : WordTrace (prefixWord ++ tailWord_2889622) baseStart_2889622 baseEnd_2889622 := by
    simpa [prefixWord, tailWord_2889622, baseEnd_2889622] using wordTrace_append hprefix tailTrace_2889622
  have hstable : (prefixWord ++ tailWord_2889622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889622).length < 2 ^ (prefixWord ++ tailWord_2889622).sum := by decide
  have hdescent : baseEnd_2889622 < baseStart_2889622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889637 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_2889637 : Nat := 118140960795 + 2889637 * 2 ^ 59
def prefixEnd_2889637 : Nat := 4983230072969 + 3 ^ 40 * 2889637 * 2
def baseEnd_2889637 : Nat := 494590899338738671882769

theorem tailTrace_2889637 : CollatzResearch.WordTrace tailWord_2889637 prefixEnd_2889637 494590899338738671882769 := by
  unfold tailWord_2889637
  simp only [CollatzResearch.WordTrace]
  refine ⟨105393719832346134554315165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70262479888230756369543443 105393719832346134554315165)
  ·
    refine ⟨39522644937129800457868187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105393719832346134554315165 39522644937129800457868187)
    ·
      refine ⟨59283967405694700686802281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39522644937129800457868187 59283967405694700686802281)
      ·
        refine ⟨44462975554271025515101711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59283967405694700686802281 44462975554271025515101711)
        ·
          refine ⟨66694463331406538272652567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44462975554271025515101711 66694463331406538272652567)
          ·
            refine ⟨100041694997109807408978851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66694463331406538272652567 100041694997109807408978851)
            ·
              refine ⟨150062542495664711113468277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100041694997109807408978851 150062542495664711113468277)
              ·
                refine ⟨14068363358968566666887651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150062542495664711113468277 14068363358968566666887651)
                ·
                  refine ⟨21102545038452850000331477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14068363358968566666887651 21102545038452850000331477)
                  ·
                    refine ⟨494590899338738671882769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21102545038452850000331477 494590899338738671882769)
                    ·
                      rfl

theorem cell23_2889637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_2889637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889637 prefixEnd_2889637 := by exact prefixLift 2889637
  have htrace : WordTrace (prefixWord ++ tailWord_2889637) baseStart_2889637 baseEnd_2889637 := by
    simpa [prefixWord, tailWord_2889637, baseEnd_2889637] using wordTrace_append hprefix tailTrace_2889637
  have hstable : (prefixWord ++ tailWord_2889637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889637).length < 2 ^ (prefixWord ++ tailWord_2889637).sum := by decide
  have hdescent : baseEnd_2889637 < baseStart_2889637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889644 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 7, 2]
def baseStart_2889644 : Nat := 118140960795 + 2889644 * 2 ^ 59
def prefixEnd_2889644 : Nat := 4983230072969 + 3 ^ 40 * 2889644 * 2
def baseEnd_2889644 : Nat := 1483776292380797488260775

theorem tailTrace_2889644 : CollatzResearch.WordTrace tailWord_2889644 prefixEnd_2889644 1483776292380797488260775 := by
  unfold tailWord_2889644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52696987571660387374909993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70262650095547183166546657 52696987571660387374909993)
  ·
    refine ⟨39522740678745290531182495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52696987571660387374909993 39522740678745290531182495)
    ·
      refine ⟨59284111018117935796773743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39522740678745290531182495 59284111018117935796773743)
      ·
        refine ⟨88926166527176903695160615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59284111018117935796773743 88926166527176903695160615)
        ·
          refine ⟨133389249790765355542740923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88926166527176903695160615 133389249790765355542740923)
          ·
            refine ⟨200083874686148033314111385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133389249790765355542740923 200083874686148033314111385)
            ·
              refine ⟨150062906014611024985583539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200083874686148033314111385 150062906014611024985583539)
              ·
                refine ⟨225094359021916537478375309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150062906014611024985583539 225094359021916537478375309)
                ·
                  refine ⟨84410384633218701554390741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225094359021916537478375309 84410384633218701554390741)
                  ·
                    refine ⟨1978368389841063317681033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 84410384633218701554390741 1978368389841063317681033)
                    ·
                      refine ⟨1483776292380797488260775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978368389841063317681033 1483776292380797488260775)
                      ·
                        rfl

theorem cell23_2889644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 7, 2].length) (baseStart_2889644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889644 prefixEnd_2889644 := by exact prefixLift 2889644
  have htrace : WordTrace (prefixWord ++ tailWord_2889644) baseStart_2889644 baseEnd_2889644 := by
    simpa [prefixWord, tailWord_2889644, baseEnd_2889644] using wordTrace_append hprefix tailTrace_2889644
  have hstable : (prefixWord ++ tailWord_2889644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889644).length < 2 ^ (prefixWord ++ tailWord_2889644).sum := by decide
  have hdescent : baseEnd_2889644 < baseStart_2889644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889647 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_2889647 : Nat := 118140960795 + 2889647 * 2 ^ 59
def prefixEnd_2889647 : Nat := 4983230072969 + 3 ^ 40 * 2889647 * 2
def baseEnd_2889647 : Nat := 1483777832822760976523261

theorem tailTrace_2889647 : CollatzResearch.WordTrace tailWord_2889647 prefixEnd_2889647 1483777832822760976523261 := by
  unfold tailWord_2889647
  simp only [CollatzResearch.WordTrace]
  refine ⟨105394084562309906262179195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70262723041539937508119463 105394084562309906262179195)
  ·
    refine ⟨158091126843464859393268793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105394084562309906262179195 158091126843464859393268793)
    ·
      refine ⟨118568345132598644544951595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158091126843464859393268793 118568345132598644544951595)
      ·
        refine ⟨177852517698897966817427393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118568345132598644544951595 177852517698897966817427393)
        ·
          refine ⟨133389388274173475113070545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177852517698897966817427393 133389388274173475113070545)
          ·
            refine ⟨100042041205630106334802909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133389388274173475113070545 100042041205630106334802909)
            ·
              refine ⟨37515765452111289875551091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100042041205630106334802909 37515765452111289875551091)
              ·
                refine ⟨56273648178166934813326637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37515765452111289875551091 56273648178166934813326637)
                ·
                  refine ⟨21102618066812600554997489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56273648178166934813326637 21102618066812600554997489)
                  ·
                    refine ⟨15826963550109450416248117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21102618066812600554997489 15826963550109450416248117)
                    ·
                      refine ⟨1483777832822760976523261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15826963550109450416248117 1483777832822760976523261)
                      ·
                        rfl

theorem cell23_2889647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_2889647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889647 prefixEnd_2889647 := by exact prefixLift 2889647
  have htrace : WordTrace (prefixWord ++ tailWord_2889647) baseStart_2889647 baseEnd_2889647 := by
    simpa [prefixWord, tailWord_2889647, baseEnd_2889647] using wordTrace_append hprefix tailTrace_2889647
  have hstable : (prefixWord ++ tailWord_2889647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889647).length < 2 ^ (prefixWord ++ tailWord_2889647).sum := by decide
  have hdescent : baseEnd_2889647 < baseStart_2889647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889661 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_2889661 : Nat := 118140960795 + 2889661 * 2 ^ 59
def prefixEnd_2889661 : Nat := 4983230072969 + 3 ^ 40 * 2889661 * 2
def baseEnd_2889661 : Nat := 1483785021551923921748197

theorem tailTrace_2889661 : CollatzResearch.WordTrace tailWord_2889661 prefixEnd_2889661 1483785021551923921748197 := by
  unfold tailWord_2889661
  simp only [CollatzResearch.WordTrace]
  refine ⟨105394595184259186653188837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70263063456172791102125891 105394595184259186653188837)
  ·
    refine ⟨19761486597048597497472907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105394595184259186653188837 19761486597048597497472907)
    ·
      refine ⟨29642229895572896246209361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19761486597048597497472907 29642229895572896246209361)
      ·
        refine ⟨22231672421679672184657021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29642229895572896246209361 22231672421679672184657021)
        ·
          refine ⟨8336877158129877069246383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22231672421679672184657021 8336877158129877069246383)
          ·
            refine ⟨12505315737194815603869575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336877158129877069246383 12505315737194815603869575)
            ·
              refine ⟨18757973605792223405804363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12505315737194815603869575 18757973605792223405804363)
              ·
                refine ⟨28136960408688335108706545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18757973605792223405804363 28136960408688335108706545)
                ·
                  refine ⟨21102720306516251331529909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28136960408688335108706545 21102720306516251331529909)
                  ·
                    refine ⟨1978380028735898562330929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21102720306516251331529909 1978380028735898562330929)
                    ·
                      refine ⟨1483785021551923921748197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978380028735898562330929 1483785021551923921748197)
                      ·
                        rfl

theorem cell23_2889661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_2889661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889661 prefixEnd_2889661 := by exact prefixLift 2889661
  have htrace : WordTrace (prefixWord ++ tailWord_2889661) baseStart_2889661 baseEnd_2889661 := by
    simpa [prefixWord, tailWord_2889661, baseEnd_2889661] using wordTrace_append hprefix tailTrace_2889661
  have hstable : (prefixWord ++ tailWord_2889661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889661).length < 2 ^ (prefixWord ++ tailWord_2889661).sum := by decide
  have hdescent : baseEnd_2889661 < baseStart_2889661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889674 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_2889674 : Nat := 118140960795 + 2889674 * 2 ^ 59
def prefixEnd_2889674 : Nat := 4983230072969 + 3 ^ 40 * 2889674 * 2
def baseEnd_2889674 : Nat := 1483791696800432370885637

theorem tailTrace_2889674 : CollatzResearch.WordTrace tailWord_2889674 prefixEnd_2889674 1483791696800432370885637 := by
  unfold tailWord_2889674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348767333303022468353019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70263379555474726582274717 26348767333303022468353019)
  ·
    refine ⟨39523150999954533702529529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26348767333303022468353019 39523150999954533702529529)
    ·
      refine ⟨29642363249965900276897147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39523150999954533702529529 29642363249965900276897147)
      ·
        refine ⟨44463544874948850415345721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29642363249965900276897147 44463544874948850415345721)
        ·
          refine ⟨33347658656211637811509291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44463544874948850415345721 33347658656211637811509291)
          ·
            refine ⟨50021487984317456717263937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33347658656211637811509291 50021487984317456717263937)
            ·
              refine ⟨37516115988238092537947953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50021487984317456717263937 37516115988238092537947953)
              ·
                refine ⟨28137086991178569403460965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37516115988238092537947953 28137086991178569403460965)
                ·
                  refine ⟨5275703810845981763148931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28137086991178569403460965 5275703810845981763148931)
                  ·
                    refine ⟨7913555716268972644723397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5275703810845981763148931 7913555716268972644723397)
                    ·
                      refine ⟨1483791696800432370885637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7913555716268972644723397 1483791696800432370885637)
                      ·
                        rfl

theorem cell23_2889674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_2889674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889674 prefixEnd_2889674 := by exact prefixLift 2889674
  have htrace : WordTrace (prefixWord ++ tailWord_2889674) baseStart_2889674 baseEnd_2889674 := by
    simpa [prefixWord, tailWord_2889674, baseEnd_2889674] using wordTrace_append hprefix tailTrace_2889674
  have hstable : (prefixWord ++ tailWord_2889674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889674).length < 2 ^ (prefixWord ++ tailWord_2889674).sum := by decide
  have hdescent : baseEnd_2889674 < baseStart_2889674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889692 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 5]
def baseStart_2889692 : Nat := 118140960795 + 2889692 * 2 ^ 59
def prefixEnd_2889692 : Nat := 4983230072969 + 3 ^ 40 * 2889692 * 2
def baseEnd_2889692 : Nat := 164866771050245922273395

theorem tailTrace_2889692 : CollatzResearch.WordTrace tailWord_2889692 prefixEnd_2889692 164866771050245922273395 := by
  unfold tailWord_2889692
  simp only [CollatzResearch.WordTrace]
  refine ⟨52697862923573439473783665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70263817231431252631711553 52697862923573439473783665)
  ·
    refine ⟨39523397192680079605337749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52697862923573439473783665 39523397192680079605337749)
    ·
      refine ⟨1852659243406878731500207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39523397192680079605337749 1852659243406878731500207)
      ·
        refine ⟨2778988865110318097250311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852659243406878731500207 2778988865110318097250311)
        ·
          refine ⟨4168483297665477145875467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778988865110318097250311 4168483297665477145875467)
          ·
            refine ⟨6252724946498215718813201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168483297665477145875467 6252724946498215718813201)
            ·
              refine ⟨4689543709873661789109901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6252724946498215718813201 4689543709873661789109901)
              ·
                refine ⟨1758578891202623170916213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689543709873661789109901 1758578891202623170916213)
                ·
                  refine ⟨164866771050245922273395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1758578891202623170916213 164866771050245922273395)
                  ·
                    rfl

theorem cell23_2889692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_2889692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889692 prefixEnd_2889692 := by exact prefixLift 2889692
  have htrace : WordTrace (prefixWord ++ tailWord_2889692) baseStart_2889692 baseEnd_2889692 := by
    simpa [prefixWord, tailWord_2889692, baseEnd_2889692] using wordTrace_append hprefix tailTrace_2889692
  have hstable : (prefixWord ++ tailWord_2889692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889692).length < 2 ^ (prefixWord ++ tailWord_2889692).sum := by decide
  have hdescent : baseEnd_2889692 < baseStart_2889692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889801 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_2889801 : Nat := 118140960795 + 2889801 * 2 ^ 59
def prefixEnd_2889801 : Nat := 4983230072969 + 3 ^ 40 * 2889801 * 2
def baseEnd_2889801 : Nat := 1483856908843553373997553

theorem tailTrace_2889801 : CollatzResearch.WordTrace tailWord_2889801 prefixEnd_2889801 1483856908843553373997553 := by
  unfold tailWord_2889801
  simp only [CollatzResearch.WordTrace]
  refine ⟨105399701403751990563285257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70266467602501327042190171 105399701403751990563285257)
  ·
    refine ⟨79049776052813992922463943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105399701403751990563285257 79049776052813992922463943)
    ·
      refine ⟨118574664079220989383695915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79049776052813992922463943 118574664079220989383695915)
      ·
        refine ⟨177861996118831484075543873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118574664079220989383695915 177861996118831484075543873)
        ·
          refine ⟨133396497089123613056657905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177861996118831484075543873 133396497089123613056657905)
          ·
            refine ⟨100047372816842709792493429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133396497089123613056657905 100047372816842709792493429)
            ·
              refine ⟨9379441201579004043046259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100047372816842709792493429 9379441201579004043046259)
              ·
                refine ⟨14069161802368506064569389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9379441201579004043046259 14069161802368506064569389)
                ·
                  refine ⟨5275935675888189774213521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14069161802368506064569389 5275935675888189774213521)
                  ·
                    refine ⟨3956951756916142330660141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275935675888189774213521 3956951756916142330660141)
                    ·
                      refine ⟨1483856908843553373997553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956951756916142330660141 1483856908843553373997553)
                      ·
                        rfl

theorem cell23_2889801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_2889801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889801 prefixEnd_2889801 := by exact prefixLift 2889801
  have htrace : WordTrace (prefixWord ++ tailWord_2889801) baseStart_2889801 baseEnd_2889801 := by
    simpa [prefixWord, tailWord_2889801, baseEnd_2889801] using wordTrace_append hprefix tailTrace_2889801
  have hstable : (prefixWord ++ tailWord_2889801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889801).length < 2 ^ (prefixWord ++ tailWord_2889801).sum := by decide
  have hdescent : baseEnd_2889801 < baseStart_2889801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889804 : List Nat := [2, 2, 1, 3, 1, 1, 4, 9]
def baseStart_2889804 : Nat := 118140960795 + 2889804 * 2 ^ 59
def prefixEnd_2889804 : Nat := 4983230072969 + 3 ^ 40 * 2889804 * 2
def baseEnd_2889804 : Nat := 54957720343908031935557

theorem tailTrace_2889804 : CollatzResearch.WordTrace tailWord_2889804 prefixEnd_2889804 54957720343908031935557 := by
  unfold tailWord_2889804
  simp only [CollatzResearch.WordTrace]
  refine ⟨52699905411370561037822233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70266540548494081383762977 52699905411370561037822233)
  ·
    refine ⟨39524929058527920778366675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52699905411370561037822233 39524929058527920778366675)
    ·
      refine ⟨59287393587791881167550013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39524929058527920778366675 59287393587791881167550013)
      ·
        refine ⟨22232772595421955437831255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59287393587791881167550013 22232772595421955437831255)
        ·
          refine ⟨33349158893132933156746883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22232772595421955437831255 33349158893132933156746883)
          ·
            refine ⟨50023738339699399735120325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33349158893132933156746883 50023738339699399735120325)
            ·
              refine ⟨9379450938693637450335061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50023738339699399735120325 9379450938693637450335061)
              ·
                refine ⟨54957720343908031935557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9379450938693637450335061 54957720343908031935557)
                ·
                  rfl

theorem cell23_2889804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 9].length) (baseStart_2889804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889804 prefixEnd_2889804 := by exact prefixLift 2889804
  have htrace : WordTrace (prefixWord ++ tailWord_2889804) baseStart_2889804 baseEnd_2889804 := by
    simpa [prefixWord, tailWord_2889804, baseEnd_2889804] using wordTrace_append hprefix tailTrace_2889804
  have hstable : (prefixWord ++ tailWord_2889804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889804).length < 2 ^ (prefixWord ++ tailWord_2889804).sum := by decide
  have hdescent : baseEnd_2889804 < baseStart_2889804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889821 : List Nat := [1, 4, 4, 1, 1, 12]
def baseStart_2889821 : Nat := 118140960795 + 2889821 * 2 ^ 59
def prefixEnd_2889821 : Nat := 4983230072969 + 3 ^ 40 * 2889821 * 2
def baseEnd_2889821 : Nat := 6106449294060260476327

theorem tailTrace_2889821 : CollatzResearch.WordTrace tailWord_2889821 prefixEnd_2889821 6106449294060260476327 := by
  unfold tailWord_2889821
  simp only [CollatzResearch.WordTrace]
  refine ⟨105400430863679533979013317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70266953909119689319342211 105400430863679533979013317)
  ·
    refine ⟨19762580786939912621064997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105400430863679533979013317 19762580786939912621064997)
    ·
      refine ⟨3705483897551233616449687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19762580786939912621064997 3705483897551233616449687)
      ·
        refine ⟨5558225846326850424674531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705483897551233616449687 5558225846326850424674531)
        ·
          refine ⟨8337338769490275637011797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5558225846326850424674531 8337338769490275637011797)
          ·
            refine ⟨6106449294060260476327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8337338769490275637011797 6106449294060260476327)
            ·
              rfl

theorem cell23_2889821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 12].length) (baseStart_2889821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889821 prefixEnd_2889821 := by exact prefixLift 2889821
  have htrace : WordTrace (prefixWord ++ tailWord_2889821) baseStart_2889821 baseEnd_2889821 := by
    simpa [prefixWord, tailWord_2889821, baseEnd_2889821] using wordTrace_append hprefix tailTrace_2889821
  have hstable : (prefixWord ++ tailWord_2889821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889821).length < 2 ^ (prefixWord ++ tailWord_2889821).sum := by decide
  have hdescent : baseEnd_2889821 < baseStart_2889821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889826 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2889826 : Nat := 118140960795 + 2889826 * 2 ^ 59
def prefixEnd_2889826 : Nat := 4983230072969 + 3 ^ 40 * 2889826 * 2
def baseEnd_2889826 : Nat := 1483869745859915776184939

theorem tailTrace_2889826 : CollatzResearch.WordTrace tailWord_2889826 prefixEnd_2889826 1483869745859915776184939 := by
  unfold tailWord_2889826
  simp only [CollatzResearch.WordTrace]
  refine ⟨26350153307165354958236333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70267075485774279888630221 26350153307165354958236333)
  ·
    refine ⟨9881307490187008109338625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26350153307165354958236333 9881307490187008109338625)
    ·
      refine ⟨7410980617640256082003969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9881307490187008109338625 7410980617640256082003969)
      ·
        refine ⟨5558235463230192061502977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7410980617640256082003969 5558235463230192061502977)
        ·
          refine ⟨4168676597422644046127233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5558235463230192061502977 4168676597422644046127233)
          ·
            refine ⟨3126507448066983034595425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168676597422644046127233 3126507448066983034595425)
            ·
              refine ⟨2344880586050237275946569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126507448066983034595425 2344880586050237275946569)
              ·
                refine ⟨1758660439537677956959927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344880586050237275946569 1758660439537677956959927)
                ·
                  refine ⟨2637990659306516935439891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758660439537677956959927 2637990659306516935439891)
                  ·
                    refine ⟨3956985988959775403159837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2637990659306516935439891 3956985988959775403159837)
                    ·
                      refine ⟨1483869745859915776184939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956985988959775403159837 1483869745859915776184939)
                      ·
                        rfl

theorem cell23_2889826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2889826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889826 prefixEnd_2889826 := by exact prefixLift 2889826
  have htrace : WordTrace (prefixWord ++ tailWord_2889826) baseStart_2889826 baseEnd_2889826 := by
    simpa [prefixWord, tailWord_2889826, baseEnd_2889826] using wordTrace_append hprefix tailTrace_2889826
  have hstable : (prefixWord ++ tailWord_2889826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889826).length < 2 ^ (prefixWord ++ tailWord_2889826).sum := by decide
  have hdescent : baseEnd_2889826 < baseStart_2889826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889831 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_2889831 : Nat := 118140960795 + 2889831 * 2 ^ 59
def prefixEnd_2889831 : Nat := 4983230072969 + 3 ^ 40 * 2889831 * 2
def baseEnd_2889831 : Nat := 1483872313263188256622415

theorem tailTrace_2889831 : CollatzResearch.WordTrace tailWord_2889831 prefixEnd_2889831 1483872313263188256622415 := by
  unfold tailWord_2889831
  simp only [CollatzResearch.WordTrace]
  refine ⟨105400795593643305686877347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70267197062428870457918231 105400795593643305686877347)
  ·
    refine ⟨158101193390464958530316021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105400795593643305686877347 158101193390464958530316021)
    ·
      refine ⟨14821986880356089862217127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158101193390464958530316021 14821986880356089862217127)
      ·
        refine ⟨22232980320534134793325691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14821986880356089862217127 22232980320534134793325691)
        ·
          refine ⟨33349470480801202189988537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22232980320534134793325691 33349470480801202189988537)
          ·
            refine ⟨25012102860600901642491403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33349470480801202189988537 25012102860600901642491403)
            ·
              refine ⟨37518154290901352463737105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25012102860600901642491403 37518154290901352463737105)
              ·
                refine ⟨28138615718176014347802829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37518154290901352463737105 28138615718176014347802829)
                ·
                  refine ⟨10551980894316005380426061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28138615718176014347802829 10551980894316005380426061)
                  ·
                    refine ⟨3956992835368502017659773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10551980894316005380426061 3956992835368502017659773)
                    ·
                      refine ⟨1483872313263188256622415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3956992835368502017659773 1483872313263188256622415)
                      ·
                        rfl

theorem cell23_2889831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_2889831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889831 prefixEnd_2889831 := by exact prefixLift 2889831
  have htrace : WordTrace (prefixWord ++ tailWord_2889831) baseStart_2889831 baseEnd_2889831 := by
    simpa [prefixWord, tailWord_2889831, baseEnd_2889831] using wordTrace_append hprefix tailTrace_2889831
  have hstable : (prefixWord ++ tailWord_2889831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889831).length < 2 ^ (prefixWord ++ tailWord_2889831).sum := by decide
  have hdescent : baseEnd_2889831 < baseStart_2889831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889909 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2889909 : Nat := 118140960795 + 2889909 * 2 ^ 59
def prefixEnd_2889909 : Nat := 4983230072969 + 3 ^ 40 * 2889909 * 2
def baseEnd_2889909 : Nat := 1483912364754238951447057

theorem tailTrace_2889909 : CollatzResearch.WordTrace tailWord_2889909 prefixEnd_2889909 1483912364754238951447057 := by
  unfold tailWord_2889909
  simp only [CollatzResearch.WordTrace]
  refine ⟨105403640487360725008216781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70269093658240483338811187 105403640487360725008216781)
  ·
    refine ⟨39526365182760271878081293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105403640487360725008216781 39526365182760271878081293)
    ·
      refine ⟨14822386943535101954280485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39526365182760271878081293 14822386943535101954280485)
      ·
        refine ⟨2779197551912831616427591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14822386943535101954280485 2779197551912831616427591)
        ·
          refine ⟨4168796327869247424641387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779197551912831616427591 4168796327869247424641387)
          ·
            refine ⟨6253194491803871136962081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168796327869247424641387 6253194491803871136962081)
            ·
              refine ⟨4689895868852903352721561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6253194491803871136962081 4689895868852903352721561)
              ·
                refine ⟨3517421901639677514541171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4689895868852903352721561 3517421901639677514541171)
                ·
                  refine ⟨5276132852459516271811757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517421901639677514541171 5276132852459516271811757)
                  ·
                    refine ⟨1978549819672318601929409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5276132852459516271811757 1978549819672318601929409)
                    ·
                      refine ⟨1483912364754238951447057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978549819672318601929409 1483912364754238951447057)
                      ·
                        rfl

theorem cell23_2889909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2889909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889909 prefixEnd_2889909 := by exact prefixLift 2889909
  have htrace : WordTrace (prefixWord ++ tailWord_2889909) baseStart_2889909 baseEnd_2889909 := by
    simpa [prefixWord, tailWord_2889909, baseEnd_2889909] using wordTrace_append hprefix tailTrace_2889909
  have hstable : (prefixWord ++ tailWord_2889909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889909).length < 2 ^ (prefixWord ++ tailWord_2889909).sum := by decide
  have hdescent : baseEnd_2889909 < baseStart_2889909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889911 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 7]
def baseStart_2889911 : Nat := 118140960795 + 2889911 * 2 ^ 59
def prefixEnd_2889911 : Nat := 4983230072969 + 3 ^ 40 * 2889911 * 2
def baseEnd_2889911 : Nat := 164879265746171993735783

theorem tailTrace_2889911 : CollatzResearch.WordTrace tailWord_2889911 prefixEnd_2889911 164879265746171993735783 := by
  unfold tailWord_2889911
  simp only [CollatzResearch.WordTrace]
  refine ⟨105403713433353479349789587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70269142288902319566526391 105403713433353479349789587)
  ·
    refine ⟨158105570150030219024684381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105403713433353479349789587 158105570150030219024684381)
    ·
      refine ⟨59289588806261332134256643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158105570150030219024684381 59289588806261332134256643)
      ·
        refine ⟨88934383209391998201384965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59289588806261332134256643 88934383209391998201384965)
        ·
          refine ⟨16675196851760999662759681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88934383209391998201384965 16675196851760999662759681)
          ·
            refine ⟨12506397638820749747069761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16675196851760999662759681 12506397638820749747069761)
            ·
              refine ⟨9379798229115562310302321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12506397638820749747069761 9379798229115562310302321)
              ·
                refine ⟨7034848671836671732726741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9379798229115562310302321 7034848671836671732726741)
                ·
                  refine ⟨164879265746171993735783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7034848671836671732726741 164879265746171993735783)
                  ·
                    rfl

theorem cell23_2889911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 7].length) (baseStart_2889911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889911 prefixEnd_2889911 := by exact prefixLift 2889911
  have htrace : WordTrace (prefixWord ++ tailWord_2889911) baseStart_2889911 baseEnd_2889911 := by
    simpa [prefixWord, tailWord_2889911, baseEnd_2889911] using wordTrace_append hprefix tailTrace_2889911
  have hstable : (prefixWord ++ tailWord_2889911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889911).length < 2 ^ (prefixWord ++ tailWord_2889911).sum := by decide
  have hdescent : baseEnd_2889911 < baseStart_2889911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889978 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_2889978 : Nat := 118140960795 + 2889978 * 2 ^ 59
def prefixEnd_2889978 : Nat := 4983230072969 + 3 ^ 40 * 2889978 * 2
def baseEnd_2889978 : Nat := 1483947794919399181484239

theorem tailTrace_2889978 : CollatzResearch.WordTrace tailWord_2889978 prefixEnd_2889978 1483947794919399181484239 := by
  unfold tailWord_2889978
  simp only [CollatzResearch.WordTrace]
  refine ⟨26351539281027687448119647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70270771416073833194985725 26351539281027687448119647)
  ·
    refine ⟨39527308921541531172179471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26351539281027687448119647 39527308921541531172179471)
    ·
      refine ⟨59290963382312296758269207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39527308921541531172179471 59290963382312296758269207)
      ·
        refine ⟨88936445073468445137403811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59290963382312296758269207 88936445073468445137403811)
        ·
          refine ⟨133404667610202667706105717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88936445073468445137403811 133404667610202667706105717)
          ·
            refine ⟨12506687588456500097447411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133404667610202667706105717 12506687588456500097447411)
            ·
              refine ⟨18760031382684750146171117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12506687588456500097447411 18760031382684750146171117)
              ·
                refine ⟨7035011768506781304814169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18760031382684750146171117 7035011768506781304814169)
                ·
                  refine ⟨5276258826380085978610627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7035011768506781304814169 5276258826380085978610627)
                  ·
                    refine ⟨7914388239570128967915941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5276258826380085978610627 7914388239570128967915941)
                    ·
                      refine ⟨1483947794919399181484239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7914388239570128967915941 1483947794919399181484239)
                      ·
                        rfl

theorem cell23_2889978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_2889978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2889978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2889978 prefixEnd_2889978 := by exact prefixLift 2889978
  have htrace : WordTrace (prefixWord ++ tailWord_2889978) baseStart_2889978 baseEnd_2889978 := by
    simpa [prefixWord, tailWord_2889978, baseEnd_2889978] using wordTrace_append hprefix tailTrace_2889978
  have hstable : (prefixWord ++ tailWord_2889978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889978).length < 2 ^ (prefixWord ++ tailWord_2889978).sum := by decide
  have hdescent : baseEnd_2889978 < baseStart_2889978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890029 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2890029 : Nat := 118140960795 + 2890029 * 2 ^ 59
def prefixEnd_2890029 : Nat := 4983230072969 + 3 ^ 40 * 2890029 * 2
def baseEnd_2890029 : Nat := 1483973982432778481946505

theorem tailTrace_2890029 : CollatzResearch.WordTrace tailWord_2890029 prefixEnd_2890029 1483973982432778481946505 := by
  unfold tailWord_2890029
  simp only [CollatzResearch.WordTrace]
  refine ⟨105408017246925985502585141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70272011497950657001723427 105408017246925985502585141)
  ·
    refine ⟨9882001616899311140867357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105408017246925985502585141 9882001616899311140867357)
    ·
      refine ⟨3705750606337241677825259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9882001616899311140867357 3705750606337241677825259)
      ·
        refine ⟨5558625909505862516737889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705750606337241677825259 5558625909505862516737889)
        ·
          refine ⟨4168969432129396887553417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5558625909505862516737889 4168969432129396887553417)
          ·
            refine ⟨3126727074097047665665063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168969432129396887553417 3126727074097047665665063)
            ·
              refine ⟨4690090611145571498497595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126727074097047665665063 4690090611145571498497595)
              ·
                refine ⟨7035135916718357247746393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690090611145571498497595 7035135916718357247746393)
                ·
                  refine ⟨5276351937538767935809795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7035135916718357247746393 5276351937538767935809795)
                  ·
                    refine ⟨7914527906308151903714693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5276351937538767935809795 7914527906308151903714693)
                    ·
                      refine ⟨1483973982432778481946505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7914527906308151903714693 1483973982432778481946505)
                      ·
                        rfl

theorem cell23_2890029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2890029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890029 prefixEnd_2890029 := by exact prefixLift 2890029
  have htrace : WordTrace (prefixWord ++ tailWord_2890029) baseStart_2890029 baseEnd_2890029 := by
    simpa [prefixWord, tailWord_2890029, baseEnd_2890029] using wordTrace_append hprefix tailTrace_2890029
  have hstable : (prefixWord ++ tailWord_2890029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890029).length < 2 ^ (prefixWord ++ tailWord_2890029).sum := by decide
  have hdescent : baseEnd_2890029 < baseStart_2890029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890055 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_2890055 : Nat := 118140960795 + 2890055 * 2 ^ 59
def prefixEnd_2890055 : Nat := 4983230072969 + 3 ^ 40 * 2890055 * 2
def baseEnd_2890055 : Nat := 1483987332929795380221385

theorem tailTrace_2890055 : CollatzResearch.WordTrace tailWord_2890055 prefixEnd_2890055 1483987332929795380221385 := by
  unfold tailWord_2890055
  simp only [CollatzResearch.WordTrace]
  refine ⟨105408965544831791943031619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70272643696554527962021079 105408965544831791943031619)
  ·
    refine ⟨158113448317247687914547429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105408965544831791943031619 158113448317247687914547429)
    ·
      refine ⟨29646271559483941483977643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158113448317247687914547429 29646271559483941483977643)
      ·
        refine ⟨44469407339225912225966465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29646271559483941483977643 44469407339225912225966465)
        ·
          refine ⟨33352055504419434169474849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44469407339225912225966465 33352055504419434169474849)
          ·
            refine ⟨25014041628314575627106137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33352055504419434169474849 25014041628314575627106137)
            ·
              refine ⟨18760531221235931720329603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25014041628314575627106137 18760531221235931720329603)
              ·
                refine ⟨28140796831853897580494405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18760531221235931720329603 28140796831853897580494405)
                ·
                  refine ⟨5276399405972605796342701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28140796831853897580494405 5276399405972605796342701)
                  ·
                    refine ⟨1978649777239727173628513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5276399405972605796342701 1978649777239727173628513)
                    ·
                      refine ⟨1483987332929795380221385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978649777239727173628513 1483987332929795380221385)
                      ·
                        rfl

theorem cell23_2890055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_2890055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890055 prefixEnd_2890055 := by exact prefixLift 2890055
  have htrace : WordTrace (prefixWord ++ tailWord_2890055) baseStart_2890055 baseEnd_2890055 := by
    simpa [prefixWord, tailWord_2890055, baseEnd_2890055] using wordTrace_append hprefix tailTrace_2890055
  have hstable : (prefixWord ++ tailWord_2890055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890055).length < 2 ^ (prefixWord ++ tailWord_2890055).sum := by decide
  have hdescent : baseEnd_2890055 < baseStart_2890055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890082 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2890082 : Nat := 118140960795 + 2890082 * 2 ^ 59
def prefixEnd_2890082 : Nat := 4983230072969 + 3 ^ 40 * 2890082 * 2
def baseEnd_2890082 : Nat := 494667065635822258194587

theorem tailTrace_2890082 : CollatzResearch.WordTrace tailWord_2890082 prefixEnd_2890082 494667065635822258194587 := by
  unfold tailWord_2890082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26352487578933493888566125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70273300210489317036176333 26352487578933493888566125)
  ·
    refine ⟨9882182842100060208212297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26352487578933493888566125 9882182842100060208212297)
    ·
      refine ⟨7411637131575045156159223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9882182842100060208212297 7411637131575045156159223)
      ·
        refine ⟨11117455697362567734238835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7411637131575045156159223 11117455697362567734238835)
        ·
          refine ⟨16676183546043851601358253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11117455697362567734238835 16676183546043851601358253)
          ·
            refine ⟨6253568829766444350509345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16676183546043851601358253 6253568829766444350509345)
            ·
              refine ⟨4690176622324833262882009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6253568829766444350509345 4690176622324833262882009)
              ·
                refine ⟨3517632466743624947161507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4690176622324833262882009 3517632466743624947161507)
                ·
                  refine ⟨5276448700115437420742261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517632466743624947161507 5276448700115437420742261)
                  ·
                    refine ⟨494667065635822258194587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5276448700115437420742261 494667065635822258194587)
                    ·
                      rfl

theorem cell23_2890082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2890082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890082 prefixEnd_2890082 := by exact prefixLift 2890082
  have htrace : WordTrace (prefixWord ++ tailWord_2890082) baseStart_2890082 baseEnd_2890082 := by
    simpa [prefixWord, tailWord_2890082, baseEnd_2890082] using wordTrace_append hprefix tailTrace_2890082
  have hstable : (prefixWord ++ tailWord_2890082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890082).length < 2 ^ (prefixWord ++ tailWord_2890082).sum := by decide
  have hdescent : baseEnd_2890082 < baseStart_2890082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890085 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2890085 : Nat := 118140960795 + 2890085 * 2 ^ 59
def prefixEnd_2890085 : Nat := 4983230072969 + 3 ^ 40 * 2890085 * 2
def baseEnd_2890085 : Nat := 1484002737349430262846247

theorem tailTrace_2890085 : CollatzResearch.WordTrace tailWord_2890085 prefixEnd_2890085 1484002737349430262846247 := by
  unfold tailWord_2890085
  simp only [CollatzResearch.WordTrace]
  refine ⟨105410059734723107066623709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70273373156482071377749139 105410059734723107066623709)
  ·
    refine ⟨39528772400521165149983891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105410059734723107066623709 39528772400521165149983891)
    ·
      refine ⟨59293158600781747724975837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39528772400521165149983891 59293158600781747724975837)
      ·
        refine ⟨22234934475293155396865939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59293158600781747724975837 22234934475293155396865939)
        ·
          refine ⟨33352401712939733095298909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22234934475293155396865939 33352401712939733095298909)
          ·
            refine ⟨12507150642352399910737091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33352401712939733095298909 12507150642352399910737091)
            ·
              refine ⟨18760725963528599866105637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12507150642352399910737091 18760725963528599866105637)
              ·
                refine ⟨3517636118161612474894807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18760725963528599866105637 3517636118161612474894807)
                ·
                  refine ⟨5276454177242418712342211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517636118161612474894807 5276454177242418712342211)
                  ·
                    refine ⟨7914681265863628068513317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5276454177242418712342211 7914681265863628068513317)
                    ·
                      refine ⟨1484002737349430262846247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7914681265863628068513317 1484002737349430262846247)
                      ·
                        rfl

theorem cell23_2890085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2890085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890085 prefixEnd_2890085 := by exact prefixLift 2890085
  have htrace : WordTrace (prefixWord ++ tailWord_2890085) baseStart_2890085 baseEnd_2890085 := by
    simpa [prefixWord, tailWord_2890085, baseEnd_2890085] using wordTrace_append hprefix tailTrace_2890085
  have hstable : (prefixWord ++ tailWord_2890085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890085).length < 2 ^ (prefixWord ++ tailWord_2890085).sum := by decide
  have hdescent : baseEnd_2890085 < baseStart_2890085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890091 : List Nat := [1, 1, 1, 1, 2, 2, 2, 13]
def baseStart_2890091 : Nat := 118140960795 + 2890091 * 2 ^ 59
def prefixEnd_2890091 : Nat := 4983230072969 + 3 ^ 40 * 2890091 * 2
def baseEnd_2890091 : Nat := 54963178453087305161897

theorem tailTrace_2890091 : CollatzResearch.WordTrace tailWord_2890091 prefixEnd_2890091 54963178453087305161897 := by
  unfold tailWord_2890091
  simp only [CollatzResearch.WordTrace]
  refine ⟨105410278572701370091342127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70273519048467580060894751 105410278572701370091342127)
  ·
    refine ⟨158115417859052055137013191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105410278572701370091342127 158115417859052055137013191)
    ·
      refine ⟨237173126788578082705519787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158115417859052055137013191 237173126788578082705519787)
      ·
        refine ⟨355759690182867124058279681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237173126788578082705519787 355759690182867124058279681)
        ·
          refine ⟨266819767637150343043709761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355759690182867124058279681 266819767637150343043709761)
          ·
            refine ⟨200114825727862757282782321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266819767637150343043709761 200114825727862757282782321)
            ·
              refine ⟨150086119295897067962086741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200114825727862757282782321 150086119295897067962086741)
              ·
                refine ⟨54963178453087305161897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 150086119295897067962086741 54963178453087305161897)
                ·
                  rfl

theorem cell23_2890091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 13].length) (baseStart_2890091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890091 prefixEnd_2890091 := by exact prefixLift 2890091
  have htrace : WordTrace (prefixWord ++ tailWord_2890091) baseStart_2890091 baseEnd_2890091 := by
    simpa [prefixWord, tailWord_2890091, baseEnd_2890091] using wordTrace_append hprefix tailTrace_2890091
  have hstable : (prefixWord ++ tailWord_2890091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890091).length < 2 ^ (prefixWord ++ tailWord_2890091).sum := by decide
  have hdescent : baseEnd_2890091 < baseStart_2890091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890148 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_2890148 : Nat := 118140960795 + 2890148 * 2 ^ 59
def prefixEnd_2890148 : Nat := 4983230072969 + 3 ^ 40 * 2890148 * 2
def baseEnd_2890148 : Nat := 1484035086630663516358457

theorem tailTrace_2890148 : CollatzResearch.WordTrace tailWord_2890148 prefixEnd_2890148 1484035086630663516358457 := by
  unfold tailWord_2890148
  simp only [CollatzResearch.WordTrace]
  refine ⟨52706178766747434413083549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70274905022329912550778065 52706178766747434413083549)
  ·
    refine ⟨19764817037530287904906331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52706178766747434413083549 19764817037530287904906331)
    ·
      refine ⟨29647225556295431857359497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19764817037530287904906331 29647225556295431857359497)
      ·
        refine ⟨22235419167221573893019623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29647225556295431857359497 22235419167221573893019623)
        ·
          refine ⟨33353128750832360839529435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22235419167221573893019623 33353128750832360839529435)
          ·
            refine ⟨50029693126248541259294153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33353128750832360839529435 50029693126248541259294153)
            ·
              refine ⟨37522269844686405944470615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50029693126248541259294153 37522269844686405944470615)
              ·
                refine ⟨56283404767029608916705923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37522269844686405944470615 56283404767029608916705923)
                ·
                  refine ⟨84425107150544413375058885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56283404767029608916705923 84425107150544413375058885)
                  ·
                    refine ⟨15829707590727077507823541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84425107150544413375058885 15829707590727077507823541)
                    ·
                      refine ⟨1484035086630663516358457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15829707590727077507823541 1484035086630663516358457)
                      ·
                        rfl

theorem cell23_2890148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_2890148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890148 prefixEnd_2890148 := by exact prefixLift 2890148
  have htrace : WordTrace (prefixWord ++ tailWord_2890148) baseStart_2890148 baseEnd_2890148 := by
    simpa [prefixWord, tailWord_2890148, baseEnd_2890148] using wordTrace_append hprefix tailTrace_2890148
  have hstable : (prefixWord ++ tailWord_2890148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890148).length < 2 ^ (prefixWord ++ tailWord_2890148).sum := by decide
  have hdescent : baseEnd_2890148 < baseStart_2890148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890152 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2890152 : Nat := 118140960795 + 2890152 * 2 ^ 59
def prefixEnd_2890152 : Nat := 4983230072969 + 3 ^ 40 * 2890152 * 2
def baseEnd_2890152 : Nat := 1484037140553281500708439

theorem tailTrace_2890152 : CollatzResearch.WordTrace tailWord_2890152 prefixEnd_2890152 1484037140553281500708439 := by
  unfold tailWord_2890152
  simp only [CollatzResearch.WordTrace]
  refine ⟨52706251712740188754656355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70275002283653585006208473 52706251712740188754656355)
  ·
    refine ⟨79059377569110283131984533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52706251712740188754656355 79059377569110283131984533)
    ·
      refine ⟨3705908323552044521811775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79059377569110283131984533 3705908323552044521811775)
      ·
        refine ⟨5558862485328066782717663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705908323552044521811775 5558862485328066782717663)
        ·
          refine ⟨8338293727992100174076495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5558862485328066782717663 8338293727992100174076495)
          ·
            refine ⟨12507440591988150261114743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8338293727992100174076495 12507440591988150261114743)
            ·
              refine ⟨18761160887982225391672115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12507440591988150261114743 18761160887982225391672115)
              ·
                refine ⟨28141741331973338087508173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18761160887982225391672115 28141741331973338087508173)
                ·
                  refine ⟨10553152999490001782815565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28141741331973338087508173 10553152999490001782815565)
                  ·
                    refine ⟨3957432374808750668555837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10553152999490001782815565 3957432374808750668555837)
                    ·
                      refine ⟨1484037140553281500708439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3957432374808750668555837 1484037140553281500708439)
                      ·
                        rfl

theorem cell23_2890152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2890152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890152 prefixEnd_2890152 := by exact prefixLift 2890152
  have htrace : WordTrace (prefixWord ++ tailWord_2890152) baseStart_2890152 baseEnd_2890152 := by
    simpa [prefixWord, tailWord_2890152, baseEnd_2890152] using wordTrace_append hprefix tailTrace_2890152
  have hstable : (prefixWord ++ tailWord_2890152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890152).length < 2 ^ (prefixWord ++ tailWord_2890152).sum := by decide
  have hdescent : baseEnd_2890152 < baseStart_2890152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890168 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 2, 6]
def baseStart_2890168 : Nat := 118140960795 + 2890168 * 2 ^ 59
def prefixEnd_2890168 : Nat := 4983230072969 + 3 ^ 40 * 2890168 * 2
def baseEnd_2890168 : Nat := 494681785414584479369455

theorem tailTrace_2890168 : CollatzResearch.WordTrace tailWord_2890168 prefixEnd_2890168 494681785414584479369455 := by
  unfold tailWord_2890168
  simp only [CollatzResearch.WordTrace]
  refine ⟨52706543496711206120947579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70275391328948274827930105 52706543496711206120947579)
  ·
    refine ⟨79059815245066809181421369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52706543496711206120947579 79059815245066809181421369)
    ·
      refine ⟨59294861433800106886066027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79059815245066809181421369 59294861433800106886066027)
      ·
        refine ⟨88942292150700160329099041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59294861433800106886066027 88942292150700160329099041)
        ·
          refine ⟨66706719113025120246824281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88942292150700160329099041 66706719113025120246824281)
          ·
            refine ⟨50030039334768840185118211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66706719113025120246824281 50030039334768840185118211)
            ·
              refine ⟨75045059002153260277677317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50030039334768840185118211 75045059002153260277677317)
              ·
                refine ⟨14070948562903736302064497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75045059002153260277677317 14070948562903736302064497)
                ·
                  refine ⟨10553211422177802226548373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14070948562903736302064497 10553211422177802226548373)
                  ·
                    refine ⟨494681785414584479369455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10553211422177802226548373 494681785414584479369455)
                    ·
                      rfl

theorem cell23_2890168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_2890168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890168 prefixEnd_2890168 := by exact prefixLift 2890168
  have htrace : WordTrace (prefixWord ++ tailWord_2890168) baseStart_2890168 baseEnd_2890168 := by
    simpa [prefixWord, tailWord_2890168, baseEnd_2890168] using wordTrace_append hprefix tailTrace_2890168
  have hstable : (prefixWord ++ tailWord_2890168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890168).length < 2 ^ (prefixWord ++ tailWord_2890168).sum := by decide
  have hdescent : baseEnd_2890168 < baseStart_2890168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890169 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2890169 : Nat := 118140960795 + 2890169 * 2 ^ 59
def prefixEnd_2890169 : Nat := 4983230072969 + 3 ^ 40 * 2890169 * 2
def baseEnd_2890169 : Nat := 1484045869724407934195861

theorem tailTrace_2890169 : CollatzResearch.WordTrace tailWord_2890169 prefixEnd_2890169 1484045869724407934195861 := by
  unfold tailWord_2890169
  simp only [CollatzResearch.WordTrace]
  refine ⟨105413123466418789412681561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70275415644279192941787707 105413123466418789412681561)
  ·
    refine ⟨79059842599814092059511171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105413123466418789412681561 79059842599814092059511171)
    ·
      refine ⟨118589763899721138089266757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79059842599814092059511171 118589763899721138089266757)
      ·
        refine ⟨22235580731197713391737517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118589763899721138089266757 22235580731197713391737517)
        ·
          refine ⟨8338342774199142521901569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22235580731197713391737517 8338342774199142521901569)
          ·
            refine ⟨6253757080649356891426177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8338342774199142521901569 6253757080649356891426177)
            ·
              refine ⟨4690317810487017668569633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6253757080649356891426177 4690317810487017668569633)
              ·
                refine ⟨3517738357865263251427225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4690317810487017668569633 3517738357865263251427225)
                ·
                  refine ⟨2638303768398947438570419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517738357865263251427225 2638303768398947438570419)
                  ·
                    refine ⟨3957455652598421157855629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2638303768398947438570419 3957455652598421157855629)
                    ·
                      refine ⟨1484045869724407934195861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3957455652598421157855629 1484045869724407934195861)
                      ·
                        rfl

theorem cell23_2890169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2890169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890169 prefixEnd_2890169 := by exact prefixLift 2890169
  have htrace : WordTrace (prefixWord ++ tailWord_2890169) baseStart_2890169 baseEnd_2890169 := by
    simpa [prefixWord, tailWord_2890169, baseEnd_2890169] using wordTrace_append hprefix tailTrace_2890169
  have hstable : (prefixWord ++ tailWord_2890169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890169).length < 2 ^ (prefixWord ++ tailWord_2890169).sum := by decide
  have hdescent : baseEnd_2890169 < baseStart_2890169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890205 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2890205 : Nat := 118140960795 + 2890205 * 2 ^ 59
def prefixEnd_2890205 : Nat := 4983230072969 + 3 ^ 40 * 2890205 * 2
def baseEnd_2890205 : Nat := 1484064355027969793345695

theorem tailTrace_2890205 : CollatzResearch.WordTrace tailWord_2890205 prefixEnd_2890205 1484064355027969793345695 := by
  unfold tailWord_2890205
  simp only [CollatzResearch.WordTrace]
  refine ⟨105414436494288367560992069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70276290996192245040661379 105414436494288367560992069)
  ·
    refine ⟨19765206842679068917686013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105414436494288367560992069 19765206842679068917686013)
    ·
      refine ⟨7411952566004650844132255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19765206842679068917686013 7411952566004650844132255)
      ·
        refine ⟨11117928849006976266198383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7411952566004650844132255 11117928849006976266198383)
        ·
          refine ⟨16676893273510464399297575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11117928849006976266198383 16676893273510464399297575)
          ·
            refine ⟨25015339910265696598946363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16676893273510464399297575 25015339910265696598946363)
            ·
              refine ⟨37523009865398544898419545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25015339910265696598946363 37523009865398544898419545)
              ·
                refine ⟨28142257399048908673814659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37523009865398544898419545 28142257399048908673814659)
                ·
                  refine ⟨42213386098573363010721989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28142257399048908673814659 42213386098573363010721989)
                  ·
                    refine ⟨7915009893482505564510373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42213386098573363010721989 7915009893482505564510373)
                    ·
                      refine ⟨1484064355027969793345695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7915009893482505564510373 1484064355027969793345695)
                      ·
                        rfl

theorem cell23_2890205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2890205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890205 prefixEnd_2890205 := by exact prefixLift 2890205
  have htrace : WordTrace (prefixWord ++ tailWord_2890205) baseStart_2890205 baseEnd_2890205 := by
    simpa [prefixWord, tailWord_2890205, baseEnd_2890205] using wordTrace_append hprefix tailTrace_2890205
  have hstable : (prefixWord ++ tailWord_2890205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890205).length < 2 ^ (prefixWord ++ tailWord_2890205).sum := by decide
  have hdescent : baseEnd_2890205 < baseStart_2890205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890213 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2890213 : Nat := 118140960795 + 2890213 * 2 ^ 59
def prefixEnd_2890213 : Nat := 4983230072969 + 3 ^ 40 * 2890213 * 2
def baseEnd_2890213 : Nat := 1484068462873205762045659

theorem tailTrace_2890213 : CollatzResearch.WordTrace tailWord_2890213 prefixEnd_2890213 1484068462873205762045659 := by
  unfold tailWord_2890213
  simp only [CollatzResearch.WordTrace]
  refine ⟨105414728278259384927283293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70276485518839589951522195 105414728278259384927283293)
  ·
    refine ⟨39530523104347269347731235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105414728278259384927283293 39530523104347269347731235)
    ·
      refine ⟨59295784656520904021596853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39530523104347269347731235 59295784656520904021596853)
      ·
        refine ⟨5558979811548834752024705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59295784656520904021596853 5558979811548834752024705)
        ·
          refine ⟨4169234858661626064018529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5558979811548834752024705 4169234858661626064018529)
          ·
            refine ⟨3126926143996219548013897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169234858661626064018529 3126926143996219548013897)
            ·
              refine ⟨2345194607997164661010423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126926143996219548013897 2345194607997164661010423)
              ·
                refine ⟨3517791911995746991515635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345194607997164661010423 3517791911995746991515635)
                ·
                  refine ⟨5276687867993620487273453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517791911995746991515635 5276687867993620487273453)
                  ·
                    refine ⟨1978757950497607682727545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5276687867993620487273453 1978757950497607682727545)
                    ·
                      refine ⟨1484068462873205762045659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978757950497607682727545 1484068462873205762045659)
                      ·
                        rfl

theorem cell23_2890213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2890213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890213 prefixEnd_2890213 := by exact prefixLift 2890213
  have htrace : WordTrace (prefixWord ++ tailWord_2890213) baseStart_2890213 baseEnd_2890213 := by
    simpa [prefixWord, tailWord_2890213, baseEnd_2890213] using wordTrace_append hprefix tailTrace_2890213
  have hstable : (prefixWord ++ tailWord_2890213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890213).length < 2 ^ (prefixWord ++ tailWord_2890213).sum := by decide
  have hdescent : baseEnd_2890213 < baseStart_2890213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890225 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_2890225 : Nat := 118140960795 + 2890225 * 2 ^ 59
def prefixEnd_2890225 : Nat := 4983230072969 + 3 ^ 40 * 2890225 * 2
def baseEnd_2890225 : Nat := 1484074624641059715095603

theorem tailTrace_2890225 : CollatzResearch.WordTrace tailWord_2890225 prefixEnd_2890225 1484074624641059715095603 := by
  unfold tailWord_2890225
  simp only [CollatzResearch.WordTrace]
  refine ⟨105415165954215910976720129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70276777302810607317813419 105415165954215910976720129)
  ·
    refine ⟨79061374465661933232540097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105415165954215910976720129 79061374465661933232540097)
    ·
      refine ⟨59296030849246449924405073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79061374465661933232540097 59296030849246449924405073)
      ·
        refine ⟨44472023136934837443303805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59296030849246449924405073 44472023136934837443303805)
        ·
          refine ⟨16677008676350564041238927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44472023136934837443303805 16677008676350564041238927)
          ·
            refine ⟨25015513014525846061858391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16677008676350564041238927 25015513014525846061858391)
            ·
              refine ⟨37523269521788769092787587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25015513014525846061858391 37523269521788769092787587)
              ·
                refine ⟨56284904282683153639181381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37523269521788769092787587 56284904282683153639181381)
                ·
                  refine ⟨10553419553003091307346509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56284904282683153639181381 10553419553003091307346509)
                  ·
                    refine ⟨3957532332376159240254941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10553419553003091307346509 3957532332376159240254941)
                    ·
                      refine ⟨1484074624641059715095603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3957532332376159240254941 1484074624641059715095603)
                      ·
                        rfl

theorem cell23_2890225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_2890225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890225 prefixEnd_2890225 := by exact prefixLift 2890225
  have htrace : WordTrace (prefixWord ++ tailWord_2890225) baseStart_2890225 baseEnd_2890225 := by
    simpa [prefixWord, tailWord_2890225, baseEnd_2890225] using wordTrace_append hprefix tailTrace_2890225
  have hstable : (prefixWord ++ tailWord_2890225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890225).length < 2 ^ (prefixWord ++ tailWord_2890225).sum := by decide
  have hdescent : baseEnd_2890225 < baseStart_2890225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890226 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2890226 : Nat := 118140960795 + 2890226 * 2 ^ 59
def prefixEnd_2890226 : Nat := 4983230072969 + 3 ^ 40 * 2890226 * 2
def baseEnd_2890226 : Nat := 1484075138121714211183099

theorem tailTrace_2890226 : CollatzResearch.WordTrace tailWord_2890226 prefixEnd_2890226 1484075138121714211183099 := by
  unfold tailWord_2890226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26353800606803072036876633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70276801618141525431671021 26353800606803072036876633)
  ·
    refine ⟨19765350455102304027657475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26353800606803072036876633 19765350455102304027657475)
    ·
      refine ⟨29648025682653456041486213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19765350455102304027657475 29648025682653456041486213)
      ·
        refine ⟨5559004815497523007778665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29648025682653456041486213 5559004815497523007778665)
        ·
          refine ⟨4169253611623142255833999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5559004815497523007778665 4169253611623142255833999)
          ·
            refine ⟨6253880417434713383750999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169253611623142255833999 6253880417434713383750999)
            ·
              refine ⟨9380820626152070075626499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253880417434713383750999 9380820626152070075626499)
              ·
                refine ⟨14071230939228105113439749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9380820626152070075626499 14071230939228105113439749)
                ·
                  refine ⟨2638355801105269708769953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14071230939228105113439749 2638355801105269708769953)
                  ·
                    refine ⟨1978766850828952281577465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2638355801105269708769953 1978766850828952281577465)
                    ·
                      refine ⟨1484075138121714211183099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978766850828952281577465 1484075138121714211183099)
                      ·
                        rfl

theorem cell23_2890226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2890226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890226 prefixEnd_2890226 := by exact prefixLift 2890226
  have htrace : WordTrace (prefixWord ++ tailWord_2890226) baseStart_2890226 baseEnd_2890226 := by
    simpa [prefixWord, tailWord_2890226, baseEnd_2890226] using wordTrace_append hprefix tailTrace_2890226
  have hstable : (prefixWord ++ tailWord_2890226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890226).length < 2 ^ (prefixWord ++ tailWord_2890226).sum := by decide
  have hdescent : baseEnd_2890226 < baseStart_2890226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890282 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2890282 : Nat := 118140960795 + 2890282 * 2 ^ 59
def prefixEnd_2890282 : Nat := 4983230072969 + 3 ^ 40 * 2890282 * 2
def baseEnd_2890282 : Nat := 1484103893038365992082841

theorem tailTrace_2890282 : CollatzResearch.WordTrace tailWord_2890282 prefixEnd_2890282 1484103893038365992082841 := by
  unfold tailWord_2890282
  simp only [CollatzResearch.WordTrace]
  refine ⟨26354311228752352427886275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70278163276672939807696733 26354311228752352427886275)
  ·
    refine ⟨39531466843128528641829413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26354311228752352427886275 39531466843128528641829413)
    ·
      refine ⟨7412150033086599120343015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39531466843128528641829413 7412150033086599120343015)
      ·
        refine ⟨11118225049629898680514523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7412150033086599120343015 11118225049629898680514523)
        ·
          refine ⟨16677337574444848020771785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118225049629898680514523 16677337574444848020771785)
          ·
            refine ⟨12508003180833636015578839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16677337574444848020771785 12508003180833636015578839)
            ·
              refine ⟨18762004771250454023368259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12508003180833636015578839 18762004771250454023368259)
              ·
                refine ⟨28143007156875681035052389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18762004771250454023368259 28143007156875681035052389)
                ·
                  refine ⟨5276813841914190194072323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28143007156875681035052389 5276813841914190194072323)
                  ·
                    refine ⟨7915220762871285291108485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5276813841914190194072323 7915220762871285291108485)
                    ·
                      refine ⟨1484103893038365992082841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7915220762871285291108485 1484103893038365992082841)
                      ·
                        rfl

theorem cell23_2890282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2890282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890282 prefixEnd_2890282 := by exact prefixLift 2890282
  have htrace : WordTrace (prefixWord ++ tailWord_2890282) baseStart_2890282 baseEnd_2890282 := by
    simpa [prefixWord, tailWord_2890282, baseEnd_2890282] using wordTrace_append hprefix tailTrace_2890282
  have hstable : (prefixWord ++ tailWord_2890282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890282).length < 2 ^ (prefixWord ++ tailWord_2890282).sum := by decide
  have hdescent : baseEnd_2890282 < baseStart_2890282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890315 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 3]
def baseStart_2890315 : Nat := 118140960795 + 2890315 * 2 ^ 59
def prefixEnd_2890315 : Nat := 4983230072969 + 3 ^ 40 * 2890315 * 2
def baseEnd_2890315 : Nat := 1484120837899964362970189

theorem tailTrace_2890315 : CollatzResearch.WordTrace tailWord_2890315 prefixEnd_2890315 1484120837899964362970189 := by
  unfold tailWord_2890315
  simp only [CollatzResearch.WordTrace]
  refine ⟨105418448523889856347496399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70278965682593237564997599 105418448523889856347496399)
  ·
    refine ⟨158127672785834784521244599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105418448523889856347496399 158127672785834784521244599)
    ·
      refine ⟨237191509178752176781866899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158127672785834784521244599 237191509178752176781866899)
      ·
        refine ⟨355787263768128265172800349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237191509178752176781866899 355787263768128265172800349)
        ·
          refine ⟨133420223913048099439800131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355787263768128265172800349 133420223913048099439800131)
          ·
            refine ⟨200130335869572149159700197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133420223913048099439800131 200130335869572149159700197)
            ·
              refine ⟨37524437975544777967443787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200130335869572149159700197 37524437975544777967443787)
              ·
                refine ⟨56286656963317166951165681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37524437975544777967443787 56286656963317166951165681)
                ·
                  refine ⟨42214992722487875213374261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56286656963317166951165681 42214992722487875213374261)
                  ·
                    refine ⟨3957655567733238301253837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42214992722487875213374261 3957655567733238301253837)
                    ·
                      refine ⟨1484120837899964362970189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3957655567733238301253837 1484120837899964362970189)
                      ·
                        rfl

theorem cell23_2890315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 3].length) (baseStart_2890315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890315 prefixEnd_2890315 := by exact prefixLift 2890315
  have htrace : WordTrace (prefixWord ++ tailWord_2890315) baseStart_2890315 baseEnd_2890315 := by
    simpa [prefixWord, tailWord_2890315, baseEnd_2890315] using wordTrace_append hprefix tailTrace_2890315
  have hstable : (prefixWord ++ tailWord_2890315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890315).length < 2 ^ (prefixWord ++ tailWord_2890315).sum := by decide
  have hdescent : baseEnd_2890315 < baseStart_2890315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890382 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_2890382 : Nat := 118140960795 + 2890382 * 2 ^ 59
def prefixEnd_2890382 : Nat := 4983230072969 + 3 ^ 40 * 2890382 * 2
def baseEnd_2890382 : Nat := 494718413701271866944127

theorem tailTrace_2890382 : CollatzResearch.WordTrace tailWord_2890382 prefixEnd_2890382 494718413701271866944127 := by
  unfold tailWord_2890382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177611526830890848773175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70280594809764751193456933 13177611526830890848773175)
  ·
    refine ⟨19766417290246336273159763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13177611526830890848773175 19766417290246336273159763)
    ·
      refine ⟨29649625935369504409739645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19766417290246336273159763 29649625935369504409739645)
      ·
        refine ⟨11118609725763564153652367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29649625935369504409739645 11118609725763564153652367)
        ·
          refine ⟨16677914588645346230478551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118609725763564153652367 16677914588645346230478551)
          ·
            refine ⟨25016871882968019345717827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16677914588645346230478551 25016871882968019345717827)
            ·
              refine ⟨37525307824452029018576741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25016871882968019345717827 37525307824452029018576741)
              ·
                refine ⟨7035995217084755440983139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37525307824452029018576741 7035995217084755440983139)
                ·
                  refine ⟨10553992825627133161474709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7035995217084755440983139 10553992825627133161474709)
                  ·
                    refine ⟨494718413701271866944127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10553992825627133161474709 494718413701271866944127)
                    ·
                      rfl

theorem cell23_2890382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_2890382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890382 prefixEnd_2890382 := by exact prefixLift 2890382
  have htrace : WordTrace (prefixWord ++ tailWord_2890382) baseStart_2890382 baseEnd_2890382 := by
    simpa [prefixWord, tailWord_2890382, baseEnd_2890382] using wordTrace_append hprefix tailTrace_2890382
  have hstable : (prefixWord ++ tailWord_2890382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890382).length < 2 ^ (prefixWord ++ tailWord_2890382).sum := by decide
  have hdescent : baseEnd_2890382 < baseStart_2890382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890385 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2890385 : Nat := 118140960795 + 2890385 * 2 ^ 59
def prefixEnd_2890385 : Nat := 4983230072969 + 3 ^ 40 * 2890385 * 2
def baseEnd_2890385 : Nat := 1484156781545779089094867

theorem tailTrace_2890385 : CollatzResearch.WordTrace tailWord_2890385 prefixEnd_2890385 1484156781545779089094867 := by
  unfold tailWord_2890385
  simp only [CollatzResearch.WordTrace]
  refine ⟨105421001633636258302544609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70280667755757505535029739 105421001633636258302544609)
  ·
    refine ⟨79065751225227193726908457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105421001633636258302544609 79065751225227193726908457)
    ·
      refine ⟨59299313418920395295181343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79065751225227193726908457 59299313418920395295181343)
      ·
        refine ⟨88948970128380592942772015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59299313418920395295181343 88948970128380592942772015)
        ·
          refine ⟨133423455192570889414158023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88948970128380592942772015 133423455192570889414158023)
          ·
            refine ⟨200135182788856334121237035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133423455192570889414158023 200135182788856334121237035)
            ·
              refine ⟨300202774183284501181855553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200135182788856334121237035 300202774183284501181855553)
              ·
                refine ⟨225152080637463375886391665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300202774183284501181855553 225152080637463375886391665)
                ·
                  refine ⟨168864060478097531914793749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225152080637463375886391665 168864060478097531914793749)
                  ·
                    refine ⟨7915502834910821808505957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 168864060478097531914793749 7915502834910821808505957)
                    ·
                      refine ⟨1484156781545779089094867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7915502834910821808505957 1484156781545779089094867)
                      ·
                        rfl

theorem cell23_2890385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2890385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890385 prefixEnd_2890385 := by exact prefixLift 2890385
  have htrace : WordTrace (prefixWord ++ tailWord_2890385) baseStart_2890385 baseEnd_2890385 := by
    simpa [prefixWord, tailWord_2890385, baseEnd_2890385] using wordTrace_append hprefix tailTrace_2890385
  have hstable : (prefixWord ++ tailWord_2890385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890385).length < 2 ^ (prefixWord ++ tailWord_2890385).sum := by decide
  have hdescent : baseEnd_2890385 < baseStart_2890385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890386 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2890386 : Nat := 118140960795 + 2890386 * 2 ^ 59
def prefixEnd_2890386 : Nat := 4983230072969 + 3 ^ 40 * 2890386 * 2
def baseEnd_2890386 : Nat := 494719098342144528394121

theorem tailTrace_2890386 : CollatzResearch.WordTrace tailWord_2890386 prefixEnd_2890386 494719098342144528394121 := by
  unfold tailWord_2890386
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355259526658158868332753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70280692071088423648887341 26355259526658158868332753)
  ·
    refine ⟨19766444644993619151249565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26355259526658158868332753 19766444644993619151249565)
    ·
      refine ⟨7412416741872607181718587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19766444644993619151249565 7412416741872607181718587)
      ·
        refine ⟨11118625112808910772577881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7412416741872607181718587 11118625112808910772577881)
        ·
          refine ⟨8338968834606683079433411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11118625112808910772577881 8338968834606683079433411)
          ·
            refine ⟨12508453251910024619150117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8338968834606683079433411 12508453251910024619150117)
            ·
              refine ⟨2345334984733129616090647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12508453251910024619150117 2345334984733129616090647)
              ·
                refine ⟨3518002477099694424135971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345334984733129616090647 3518002477099694424135971)
                ·
                  refine ⟨5277003715649541636203957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518002477099694424135971 5277003715649541636203957)
                  ·
                    refine ⟨494719098342144528394121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5277003715649541636203957 494719098342144528394121)
                    ·
                      rfl

theorem cell23_2890386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2890386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890386 prefixEnd_2890386 := by exact prefixLift 2890386
  have htrace : WordTrace (prefixWord ++ tailWord_2890386) baseStart_2890386 baseEnd_2890386 := by
    simpa [prefixWord, tailWord_2890386, baseEnd_2890386] using wordTrace_append hprefix tailTrace_2890386
  have hstable : (prefixWord ++ tailWord_2890386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890386).length < 2 ^ (prefixWord ++ tailWord_2890386).sum := by decide
  have hdescent : baseEnd_2890386 < baseStart_2890386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890392 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2890392 : Nat := 118140960795 + 2890392 * 2 ^ 59
def prefixEnd_2890392 : Nat := 4983230072969 + 3 ^ 40 * 2890392 * 2
def baseEnd_2890392 : Nat := 1484160375910360561707335

theorem tailTrace_2890392 : CollatzResearch.WordTrace tailWord_2890392 prefixEnd_2890392 1484160375910360561707335 := by
  unfold tailWord_2890392
  simp only [CollatzResearch.WordTrace]
  refine ⟨52710628472305449249024715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70280837963073932332032953 52710628472305449249024715)
  ·
    refine ⟨79065942708458173873537073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52710628472305449249024715 79065942708458173873537073)
    ·
      refine ⟨59299457031343630405152805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79065942708458173873537073 59299457031343630405152805)
      ·
        refine ⟨11118648193376930700966151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59299457031343630405152805 11118648193376930700966151)
        ·
          refine ⟨16677972290065396051449227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118648193376930700966151 16677972290065396051449227)
          ·
            refine ⟨25016958435098094077173841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16677972290065396051449227 25016958435098094077173841)
            ·
              refine ⟨18762718826323570557880381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25016958435098094077173841 18762718826323570557880381)
              ·
                refine ⟨7036019559871338959205143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18762718826323570557880381 7036019559871338959205143)
                ·
                  refine ⟨10554029339807008438807715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7036019559871338959205143 10554029339807008438807715)
                  ·
                    refine ⟨15831044009710512658211573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10554029339807008438807715 15831044009710512658211573)
                    ·
                      refine ⟨1484160375910360561707335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15831044009710512658211573 1484160375910360561707335)
                      ·
                        rfl

theorem cell23_2890392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2890392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890392 prefixEnd_2890392 := by exact prefixLift 2890392
  have htrace : WordTrace (prefixWord ++ tailWord_2890392) baseStart_2890392 baseEnd_2890392 := by
    simpa [prefixWord, tailWord_2890392, baseEnd_2890392] using wordTrace_append hprefix tailTrace_2890392
  have hstable : (prefixWord ++ tailWord_2890392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890392).length < 2 ^ (prefixWord ++ tailWord_2890392).sum := by decide
  have hdescent : baseEnd_2890392 < baseStart_2890392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890405 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2890405 : Nat := 118140960795 + 2890405 * 2 ^ 59
def prefixEnd_2890405 : Nat := 4983230072969 + 3 ^ 40 * 2890405 * 2
def baseEnd_2890405 : Nat := 1484167051158869010844775

theorem tailTrace_2890405 : CollatzResearch.WordTrace tailWord_2890405 prefixEnd_2890405 1484167051158869010844775 := by
  unfold tailWord_2890405
  simp only [CollatzResearch.WordTrace]
  refine ⟨105421731093563801718272669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70281154062375867812181779 105421731093563801718272669)
  ·
    refine ⟨39533149160086425644352251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105421731093563801718272669 39533149160086425644352251)
    ·
      refine ⟨59299723740129638466528377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39533149160086425644352251 59299723740129638466528377)
      ·
        refine ⟨44474792805097228849896283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59299723740129638466528377 44474792805097228849896283)
        ·
          refine ⟨66712189207645843274844425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44474792805097228849896283 66712189207645843274844425)
          ·
            refine ⟨50034141905734382456133319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66712189207645843274844425 50034141905734382456133319)
            ·
              refine ⟨75051212858601573684199979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50034141905734382456133319 75051212858601573684199979)
              ·
                refine ⟨112576819287902360526299969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75051212858601573684199979 112576819287902360526299969)
                ·
                  refine ⟨84432614465926770394724977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112576819287902360526299969 84432614465926770394724977)
                  ·
                    refine ⟨63324460849445077796043733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84432614465926770394724977 63324460849445077796043733)
                    ·
                      refine ⟨1484167051158869010844775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 63324460849445077796043733 1484167051158869010844775)
                      ·
                        rfl

theorem cell23_2890405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2890405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890405 prefixEnd_2890405 := by exact prefixLift 2890405
  have htrace : WordTrace (prefixWord ++ tailWord_2890405) baseStart_2890405 baseEnd_2890405 := by
    simpa [prefixWord, tailWord_2890405, baseEnd_2890405] using wordTrace_append hprefix tailTrace_2890405
  have hstable : (prefixWord ++ tailWord_2890405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890405).length < 2 ^ (prefixWord ++ tailWord_2890405).sum := by decide
  have hdescent : baseEnd_2890405 < baseStart_2890405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890419 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 4]
def baseStart_2890419 : Nat := 118140960795 + 2890419 * 2 ^ 59
def prefixEnd_2890419 : Nat := 4983230072969 + 3 ^ 40 * 2890419 * 2
def baseEnd_2890419 : Nat := 1484174239888031956069711

theorem tailTrace_2890419 : CollatzResearch.WordTrace tailWord_2890419 prefixEnd_2890419 1484174239888031956069711 := by
  unfold tailWord_2890419
  simp only [CollatzResearch.WordTrace]
  refine ⟨105422241715513082109282311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70281494477008721406188207 105422241715513082109282311)
  ·
    refine ⟨158133362573269623163923467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105422241715513082109282311 158133362573269623163923467)
    ·
      refine ⟨237200043859904434745885201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158133362573269623163923467 237200043859904434745885201)
      ·
        refine ⟨177900032894928326059413901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237200043859904434745885201 177900032894928326059413901)
        ·
          refine ⟨66712512335598122272280213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177900032894928326059413901 66712512335598122272280213)
          ·
            refine ⟨3127149015731161981513135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66712512335598122272280213 3127149015731161981513135)
            ·
              refine ⟨4690723523596742972269703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127149015731161981513135 4690723523596742972269703)
              ·
                refine ⟨7036085285395114458404555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690723523596742972269703 7036085285395114458404555)
                ·
                  refine ⟨10554127928092671687606833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7036085285395114458404555 10554127928092671687606833)
                  ·
                    refine ⟨7915595946069503765705125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10554127928092671687606833 7915595946069503765705125)
                    ·
                      refine ⟨1484174239888031956069711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7915595946069503765705125 1484174239888031956069711)
                      ·
                        rfl

theorem cell23_2890419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_2890419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890419 prefixEnd_2890419 := by exact prefixLift 2890419
  have htrace : WordTrace (prefixWord ++ tailWord_2890419) baseStart_2890419 baseEnd_2890419 := by
    simpa [prefixWord, tailWord_2890419, baseEnd_2890419] using wordTrace_append hprefix tailTrace_2890419
  have hstable : (prefixWord ++ tailWord_2890419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890419).length < 2 ^ (prefixWord ++ tailWord_2890419).sum := by decide
  have hdescent : baseEnd_2890419 < baseStart_2890419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890429 : List Nat := [1, 4, 1, 2, 1, 5, 2, 7]
def baseStart_2890429 : Nat := 118140960795 + 2890429 * 2 ^ 59
def prefixEnd_2890429 : Nat := 4983230072969 + 3 ^ 40 * 2890429 * 2
def baseEnd_2890429 : Nat := 54969606470169515442395

theorem tailTrace_2890429 : CollatzResearch.WordTrace tailWord_2890429 prefixEnd_2890429 54969606470169515442395 := by
  unfold tailWord_2890429
  simp only [CollatzResearch.WordTrace]
  refine ⟨105422606445476853817146341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70281737630317902544764227 105422606445476853817146341)
  ·
    refine ⟨19766738708526910090714939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105422606445476853817146341 19766738708526910090714939)
    ·
      refine ⟨29650108062790365136072409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19766738708526910090714939 29650108062790365136072409)
      ·
        refine ⟨22237581047092773852054307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29650108062790365136072409 22237581047092773852054307)
        ·
          refine ⟨33356371570639160778081461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22237581047092773852054307 33356371570639160778081461)
          ·
            refine ⟨3127159834747421322945137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33356371570639160778081461 3127159834747421322945137)
            ·
              refine ⟨2345369876060565992208853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3127159834747421322945137 2345369876060565992208853)
              ·
                refine ⟨54969606470169515442395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2345369876060565992208853 54969606470169515442395)
                ·
                  rfl

theorem cell23_2890429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 7].length) (baseStart_2890429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890429 prefixEnd_2890429 := by exact prefixLift 2890429
  have htrace : WordTrace (prefixWord ++ tailWord_2890429) baseStart_2890429 baseEnd_2890429 := by
    simpa [prefixWord, tailWord_2890429, baseEnd_2890429] using wordTrace_append hprefix tailTrace_2890429
  have hstable : (prefixWord ++ tailWord_2890429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890429).length < 2 ^ (prefixWord ++ tailWord_2890429).sum := by decide
  have hdescent : baseEnd_2890429 < baseStart_2890429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890440 : List Nat := [2, 1, 3, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_2890440 : Nat := 118140960795 + 2890440 * 2 ^ 59
def prefixEnd_2890440 : Nat := 4983230072969 + 3 ^ 40 * 2890440 * 2
def baseEnd_2890440 : Nat := 1484185022981776373907115

theorem tailTrace_2890440 : CollatzResearch.WordTrace tailWord_2890440 prefixEnd_2890440 1484185022981776373907115 := by
  unfold tailWord_2890440
  simp only [CollatzResearch.WordTrace]
  refine ⟨52711503824218501347898387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70282005098958001797197849 52711503824218501347898387)
  ·
    refine ⟨79067255736327752021847581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52711503824218501347898387 79067255736327752021847581)
    ·
      refine ⟨29650220901122907008192843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79067255736327752021847581 29650220901122907008192843)
      ·
        refine ⟨44475331351684360512289265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29650220901122907008192843 44475331351684360512289265)
        ·
          refine ⟨33356498513763270384216949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44475331351684360512289265 33356498513763270384216949)
          ·
            refine ⟨3127171735665306598520339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33356498513763270384216949 3127171735665306598520339)
            ·
              refine ⟨4690757603497959897780509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127171735665306598520339 4690757603497959897780509)
              ·
                refine ⟨1759034101311734961667691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690757603497959897780509 1759034101311734961667691)
                ·
                  refine ⟨2638551151967602442501537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759034101311734961667691 2638551151967602442501537)
                  ·
                    refine ⟨1978913363975701831876153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2638551151967602442501537 1978913363975701831876153)
                    ·
                      refine ⟨1484185022981776373907115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978913363975701831876153 1484185022981776373907115)
                      ·
                        rfl

theorem cell23_2890440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_2890440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890440 prefixEnd_2890440 := by exact prefixLift 2890440
  have htrace : WordTrace (prefixWord ++ tailWord_2890440) baseStart_2890440 baseEnd_2890440 := by
    simpa [prefixWord, tailWord_2890440, baseEnd_2890440] using wordTrace_append hprefix tailTrace_2890440
  have hstable : (prefixWord ++ tailWord_2890440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890440).length < 2 ^ (prefixWord ++ tailWord_2890440).sum := by decide
  have hdescent : baseEnd_2890440 < baseStart_2890440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890529 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2890529 : Nat := 118140960795 + 2890529 * 2 ^ 59
def prefixEnd_2890529 : Nat := 4983230072969 + 3 ^ 40 * 2890529 * 2
def baseEnd_2890529 : Nat := 1484230722760026525694205

theorem tailTrace_2890529 : CollatzResearch.WordTrace tailWord_2890529 prefixEnd_2890529 1484230722760026525694205 := by
  unfold tailWord_2890529
  simp only [CollatzResearch.WordTrace]
  refine ⟨105426253745114570895786641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70284169163409713930524427 105426253745114570895786641)
  ·
    refine ⟨79069690308835928171839981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105426253745114570895786641 79069690308835928171839981)
    ·
      refine ⟨29651133865813473064439993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79069690308835928171839981 29651133865813473064439993)
      ·
        refine ⟨22238350399360104798329995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29651133865813473064439993 22238350399360104798329995)
        ·
          refine ⟨33357525599040157197494993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22238350399360104798329995 33357525599040157197494993)
          ·
            refine ⟨25018144199280117898121245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33357525599040157197494993 25018144199280117898121245)
            ·
              refine ⟨9381804074730044211795467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25018144199280117898121245 9381804074730044211795467)
              ·
                refine ⟨14072706112095066317693201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9381804074730044211795467 14072706112095066317693201)
                ·
                  refine ⟨10554529584071299738269901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14072706112095066317693201 10554529584071299738269901)
                  ·
                    refine ⟨3957948594026737401851213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10554529584071299738269901 3957948594026737401851213)
                    ·
                      refine ⟨1484230722760026525694205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3957948594026737401851213 1484230722760026525694205)
                      ·
                        rfl

theorem cell23_2890529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2890529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890529 prefixEnd_2890529 := by exact prefixLift 2890529
  have htrace : WordTrace (prefixWord ++ tailWord_2890529) baseStart_2890529 baseEnd_2890529 := by
    simpa [prefixWord, tailWord_2890529, baseEnd_2890529] using wordTrace_append hprefix tailTrace_2890529
  have hstable : (prefixWord ++ tailWord_2890529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890529).length < 2 ^ (prefixWord ++ tailWord_2890529).sum := by decide
  have hdescent : baseEnd_2890529 < baseStart_2890529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890549 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2890549 : Nat := 118140960795 + 2890549 * 2 ^ 59
def prefixEnd_2890549 : Nat := 4983230072969 + 3 ^ 40 * 2890549 * 2
def baseEnd_2890549 : Nat := 494746997457705482481371

theorem tailTrace_2890549 : CollatzResearch.WordTrace tailWord_2890549 prefixEnd_2890549 494746997457705482481371 := by
  unfold tailWord_2890549
  simp only [CollatzResearch.WordTrace]
  refine ⟨105426983205042114311514701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70284655470028076207676467 105426983205042114311514701)
  ·
    refine ⟨39535118701890792866818013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105426983205042114311514701 39535118701890792866818013)
    ·
      refine ⟨14825669513209047325056755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39535118701890792866818013 14825669513209047325056755)
      ·
        refine ⟨22238504269813570987585133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14825669513209047325056755 22238504269813570987585133)
        ·
          refine ⟨8339439101180089120344425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22238504269813570987585133 8339439101180089120344425)
          ·
            refine ⟨6254579325885066840258319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8339439101180089120344425 6254579325885066840258319)
            ·
              refine ⟨9381868988827600260387479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6254579325885066840258319 9381868988827600260387479)
              ·
                refine ⟨14072803483241400390581219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9381868988827600260387479 14072803483241400390581219)
                ·
                  refine ⟨21109205224862100585871829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14072803483241400390581219 21109205224862100585871829)
                  ·
                    refine ⟨494746997457705482481371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21109205224862100585871829 494746997457705482481371)
                    ·
                      rfl

theorem cell23_2890549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2890549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890549 prefixEnd_2890549 := by exact prefixLift 2890549
  have htrace : WordTrace (prefixWord ++ tailWord_2890549) baseStart_2890549 baseEnd_2890549 := by
    simpa [prefixWord, tailWord_2890549, baseEnd_2890549] using wordTrace_append hprefix tailTrace_2890549
  have hstable : (prefixWord ++ tailWord_2890549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890549).length < 2 ^ (prefixWord ++ tailWord_2890549).sum := by decide
  have hdescent : baseEnd_2890549 < baseStart_2890549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890564 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2890564 : Nat := 118140960795 + 2890564 * 2 ^ 59
def prefixEnd_2890564 : Nat := 4983230072969 + 3 ^ 40 * 2890564 * 2
def baseEnd_2890564 : Nat := 1484248694582933888756545

theorem tailTrace_2890564 : CollatzResearch.WordTrace tailWord_2890564 prefixEnd_2890564 1484248694582933888756545 := by
  unfold tailWord_2890564
  simp only [CollatzResearch.WordTrace]
  refine ⟨52713765149993885936655373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70285020199991847915540497 52713765149993885936655373)
  ·
    refine ⟨19767661931247707226245765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52713765149993885936655373 19767661931247707226245765)
    ·
      refine ⟨3706436612108945104921081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19767661931247707226245765 3706436612108945104921081)
      ·
        refine ⟨2779827459081708828690811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3706436612108945104921081 2779827459081708828690811)
        ·
          refine ⟨4169741188622563243036217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779827459081708828690811 4169741188622563243036217)
          ·
            refine ⟨3127305891466922432277163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169741188622563243036217 3127305891466922432277163)
            ·
              refine ⟨4690958837200383648415745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127305891466922432277163 4690958837200383648415745)
              ·
                refine ⟨3518219127900287736311809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4690958837200383648415745 3518219127900287736311809)
                ·
                  refine ⟨2638664345925215802233857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3518219127900287736311809 2638664345925215802233857)
                  ·
                    refine ⟨1978998259443911851675393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2638664345925215802233857 1978998259443911851675393)
                    ·
                      refine ⟨1484248694582933888756545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1978998259443911851675393 1484248694582933888756545)
                      ·
                        rfl

theorem cell23_2890564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2890564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890564 prefixEnd_2890564 := by exact prefixLift 2890564
  have htrace : WordTrace (prefixWord ++ tailWord_2890564) baseStart_2890564 baseEnd_2890564 := by
    simpa [prefixWord, tailWord_2890564, baseEnd_2890564] using wordTrace_append hprefix tailTrace_2890564
  have hstable : (prefixWord ++ tailWord_2890564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890564).length < 2 ^ (prefixWord ++ tailWord_2890564).sum := by decide
  have hdescent : baseEnd_2890564 < baseStart_2890564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890586 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2]
def baseStart_2890586 : Nat := 118140960795 + 2890586 * 2 ^ 59
def prefixEnd_2890586 : Nat := 4983230072969 + 3 ^ 40 * 2890586 * 2
def baseEnd_2890586 : Nat := 1484259991157332802681443

theorem tailTrace_2890586 : CollatzResearch.WordTrace tailWord_2890586 prefixEnd_2890586 1484259991157332802681443 := by
  unfold tailWord_2890586
  simp only [CollatzResearch.WordTrace]
  refine ⟨26357083176477017407652903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70285555137272046420407741 26357083176477017407652903)
  ·
    refine ⟨39535624764715526111479355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26357083176477017407652903 39535624764715526111479355)
    ·
      refine ⟨59303437147073289167219033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39535624764715526111479355 59303437147073289167219033)
      ·
        refine ⟨44477577860304966875414275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59303437147073289167219033 44477577860304966875414275)
        ·
          refine ⟨66716366790457450313121413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44477577860304966875414275 66716366790457450313121413)
          ·
            refine ⟨12509318773210771933710265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66716366790457450313121413 12509318773210771933710265)
            ·
              refine ⟨9381989079908078950282699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12509318773210771933710265 9381989079908078950282699)
              ·
                refine ⟨14072983619862118425424049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9381989079908078950282699 14072983619862118425424049)
                ·
                  refine ⟨10554737714896588819068037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14072983619862118425424049 10554737714896588819068037)
                  ·
                    refine ⟨1979013321543110403575257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10554737714896588819068037 1979013321543110403575257)
                    ·
                      refine ⟨1484259991157332802681443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979013321543110403575257 1484259991157332802681443)
                      ·
                        rfl

theorem cell23_2890586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_2890586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890586 prefixEnd_2890586 := by exact prefixLift 2890586
  have htrace : WordTrace (prefixWord ++ tailWord_2890586) baseStart_2890586 baseEnd_2890586 := by
    simpa [prefixWord, tailWord_2890586, baseEnd_2890586] using wordTrace_append hprefix tailTrace_2890586
  have hstable : (prefixWord ++ tailWord_2890586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890586).length < 2 ^ (prefixWord ++ tailWord_2890586).sum := by decide
  have hdescent : baseEnd_2890586 < baseStart_2890586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890596 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_2890596 : Nat := 118140960795 + 2890596 * 2 ^ 59
def prefixEnd_2890596 : Nat := 4983230072969 + 3 ^ 40 * 2890596 * 2
def baseEnd_2890596 : Nat := 494755041987959254518799

theorem tailTrace_2890596 : CollatzResearch.WordTrace tailWord_2890596 prefixEnd_2890596 494755041987959254518799 := by
  unfold tailWord_2890596
  simp only [CollatzResearch.WordTrace]
  refine ⟨52714348717935920669237821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70285798290581227558983761 52714348717935920669237821)
  ·
    refine ⟨19767880769225970250964183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52714348717935920669237821 19767880769225970250964183)
    ·
      refine ⟨29651821153838955376446275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19767880769225970250964183 29651821153838955376446275)
      ·
        refine ⟨44477731730758433064669413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29651821153838955376446275 44477731730758433064669413)
        ·
          refine ⟨8339574699517206199625515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44477731730758433064669413 8339574699517206199625515)
          ·
            refine ⟨12509362049275809299438273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8339574699517206199625515 12509362049275809299438273)
            ·
              refine ⟨9382021536956856974578705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12509362049275809299438273 9382021536956856974578705)
              ·
                refine ⟨7036516152717642730934029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9382021536956856974578705 7036516152717642730934029)
                ·
                  refine ⟨2638693557269116024100261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7036516152717642730934029 2638693557269116024100261)
                  ·
                    refine ⟨494755041987959254518799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638693557269116024100261 494755041987959254518799)
                    ·
                      rfl

theorem cell23_2890596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_2890596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890596 prefixEnd_2890596 := by exact prefixLift 2890596
  have htrace : WordTrace (prefixWord ++ tailWord_2890596) baseStart_2890596 baseEnd_2890596 := by
    simpa [prefixWord, tailWord_2890596, baseEnd_2890596] using wordTrace_append hprefix tailTrace_2890596
  have hstable : (prefixWord ++ tailWord_2890596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890596).length < 2 ^ (prefixWord ++ tailWord_2890596).sum := by decide
  have hdescent : baseEnd_2890596 < baseStart_2890596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890656 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 1, 5]
def baseStart_2890656 : Nat := 118140960795 + 2890656 * 2 ^ 59
def prefixEnd_2890656 : Nat := 4983230072969 + 3 ^ 40 * 2890656 * 2
def baseEnd_2890656 : Nat := 494765311601049176268707

theorem tailTrace_2890656 : CollatzResearch.WordTrace tailWord_2890656 prefixEnd_2890656 494765311601049176268707 := by
  unfold tailWord_2890656
  simp only [CollatzResearch.WordTrace]
  refine ⟨52715442907827235792829911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70287257210436314390439881 52715442907827235792829911)
  ·
    refine ⟨79073164361740853689244867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52715442907827235792829911 79073164361740853689244867)
    ·
      refine ⟨118609746542611280533867301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79073164361740853689244867 118609746542611280533867301)
      ·
        refine ⟨22239327476739615100100119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118609746542611280533867301 22239327476739615100100119)
        ·
          refine ⟨33358991215109422650150179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22239327476739615100100119 33358991215109422650150179)
          ·
            refine ⟨50038486822664133975225269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33358991215109422650150179 50038486822664133975225269)
            ·
              refine ⟨4691108139624762560177369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50038486822664133975225269 4691108139624762560177369)
              ·
                refine ⟨3518331104718571920133027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4691108139624762560177369 3518331104718571920133027)
                ·
                  refine ⟨5277496657077857880199541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518331104718571920133027 5277496657077857880199541)
                  ·
                    refine ⟨494765311601049176268707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5277496657077857880199541 494765311601049176268707)
                    ·
                      rfl

theorem cell23_2890656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_2890656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890656 prefixEnd_2890656 := by exact prefixLift 2890656
  have htrace : WordTrace (prefixWord ++ tailWord_2890656) baseStart_2890656 baseEnd_2890656 := by
    simpa [prefixWord, tailWord_2890656, baseEnd_2890656] using wordTrace_append hprefix tailTrace_2890656
  have hstable : (prefixWord ++ tailWord_2890656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890656).length < 2 ^ (prefixWord ++ tailWord_2890656).sum := by decide
  have hdescent : baseEnd_2890656 < baseStart_2890656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890699 : List Nat := [1, 1, 1, 1, 3, 5, 3, 8]
def baseStart_2890699 : Nat := 118140960795 + 2890699 * 2 ^ 59
def prefixEnd_2890699 : Nat := 4983230072969 + 3 ^ 40 * 2890699 * 2
def baseEnd_2890699 : Nat := 54974741276714476317349

theorem tailTrace_2890699 : CollatzResearch.WordTrace tailWord_2890699 prefixEnd_2890699 54974741276714476317349 := by
  unfold tailWord_2890699
  simp only [CollatzResearch.WordTrace]
  refine ⟨105432454154498689929475151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70288302769665793286316767 105432454154498689929475151)
  ·
    refine ⟨158148681231748034894212727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105432454154498689929475151 158148681231748034894212727)
    ·
      refine ⟨237223021847622052341319091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158148681231748034894212727 237223021847622052341319091)
      ·
        refine ⟨355834532771433078511978637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237223021847622052341319091 355834532771433078511978637)
        ·
          refine ⟨133437949789287404441991989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355834532771433078511978637 133437949789287404441991989)
          ·
            refine ⟨12509807792745694166436749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133437949789287404441991989 12509807792745694166436749)
            ·
              refine ⟨4691177922279635312413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12509807792745694166436749 4691177922279635312413781)
              ·
                refine ⟨54974741276714476317349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4691177922279635312413781 54974741276714476317349)
                ·
                  rfl

theorem cell23_2890699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 8].length) (baseStart_2890699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890699 prefixEnd_2890699 := by exact prefixLift 2890699
  have htrace : WordTrace (prefixWord ++ tailWord_2890699) baseStart_2890699 baseEnd_2890699 := by
    simpa [prefixWord, tailWord_2890699, baseEnd_2890699] using wordTrace_append hprefix tailTrace_2890699
  have hstable : (prefixWord ++ tailWord_2890699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890699).length < 2 ^ (prefixWord ++ tailWord_2890699).sum := by decide
  have hdescent : baseEnd_2890699 < baseStart_2890699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890727 : List Nat := [1, 1, 5, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_2890727 : Nat := 118140960795 + 2890727 * 2 ^ 59
def prefixEnd_2890727 : Nat := 4983230072969 + 3 ^ 40 * 2890727 * 2
def baseEnd_2890727 : Nat := 1484332391929616751018295

theorem tailTrace_2890727 : CollatzResearch.WordTrace tailWord_2890727 prefixEnd_2890727 1484332391929616751018295 := by
  unfold tailWord_2890727
  simp only [CollatzResearch.WordTrace]
  refine ⟨105433475398397250711494435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70288983598931500474329623 105433475398397250711494435)
  ·
    refine ⟨158150213097595876067241653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105433475398397250711494435 158150213097595876067241653)
    ·
      refine ⟨14826582477899613381303905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158150213097595876067241653 14826582477899613381303905)
      ·
        refine ⟨11119936858424710035977929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14826582477899613381303905 11119936858424710035977929)
        ·
          refine ⟨8339952643818532526983447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11119936858424710035977929 8339952643818532526983447)
          ·
            refine ⟨12509928965727798790475171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8339952643818532526983447 12509928965727798790475171)
            ·
              refine ⟨18764893448591698185712757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12509928965727798790475171 18764893448591698185712757)
              ·
                refine ⟨1759208760805471704910571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18764893448591698185712757 1759208760805471704910571)
                ·
                  refine ⟨2638813141208207557365857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759208760805471704910571 2638813141208207557365857)
                  ·
                    refine ⟨1979109855906155668024393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2638813141208207557365857 1979109855906155668024393)
                    ·
                      refine ⟨1484332391929616751018295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979109855906155668024393 1484332391929616751018295)
                      ·
                        rfl

theorem cell23_2890727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_2890727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890727 prefixEnd_2890727 := by exact prefixLift 2890727
  have htrace : WordTrace (prefixWord ++ tailWord_2890727) baseStart_2890727 baseEnd_2890727 := by
    simpa [prefixWord, tailWord_2890727, baseEnd_2890727] using wordTrace_append hprefix tailTrace_2890727
  have hstable : (prefixWord ++ tailWord_2890727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890727).length < 2 ^ (prefixWord ++ tailWord_2890727).sum := by decide
  have hdescent : baseEnd_2890727 < baseStart_2890727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890730 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_2890730 : Nat := 118140960795 + 2890730 * 2 ^ 59
def prefixEnd_2890730 : Nat := 4983230072969 + 3 ^ 40 * 2890730 * 2
def baseEnd_2890730 : Nat := 1484333932371580239280781

theorem tailTrace_2890730 : CollatzResearch.WordTrace tailWord_2890730 prefixEnd_2890730 1484333932371580239280781 := by
  unfold tailWord_2890730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26358396204346595555963411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70289056544924254815902429 26358396204346595555963411)
  ·
    refine ⟨39537594306519893333945117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26358396204346595555963411 39537594306519893333945117)
    ·
      refine ⟨14826597864944960000229419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39537594306519893333945117 14826597864944960000229419)
      ·
        refine ⟨22239896797417440000344129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14826597864944960000229419 22239896797417440000344129)
        ·
          refine ⟨16679922598063080000258097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22239896797417440000344129 16679922598063080000258097)
          ·
            refine ⟨12509941948547310000193573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16679922598063080000258097 12509941948547310000193573)
            ·
              refine ⟨2345614115352620625036295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12509941948547310000193573 2345614115352620625036295)
              ·
                refine ⟨3518421173028930937554443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345614115352620625036295 3518421173028930937554443)
                ·
                  refine ⟨5277631759543396406331665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518421173028930937554443 5277631759543396406331665)
                  ·
                    refine ⟨3958223819657547304748749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5277631759543396406331665 3958223819657547304748749)
                    ·
                      refine ⟨1484333932371580239280781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3958223819657547304748749 1484333932371580239280781)
                      ·
                        rfl

theorem cell23_2890730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_2890730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890730 prefixEnd_2890730 := by exact prefixLift 2890730
  have htrace : WordTrace (prefixWord ++ tailWord_2890730) baseStart_2890730 baseEnd_2890730 := by
    simpa [prefixWord, tailWord_2890730, baseEnd_2890730] using wordTrace_append hprefix tailTrace_2890730
  have hstable : (prefixWord ++ tailWord_2890730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890730).length < 2 ^ (prefixWord ++ tailWord_2890730).sum := by decide
  have hdescent : baseEnd_2890730 < baseStart_2890730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890754 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2890754 : Nat := 118140960795 + 2890754 * 2 ^ 59
def prefixEnd_2890754 : Nat := 4983230072969 + 3 ^ 40 * 2890754 * 2
def baseEnd_2890754 : Nat := 494782085302429381793557

theorem tailTrace_2890754 : CollatzResearch.WordTrace tailWord_2890754 prefixEnd_2890754 494782085302429381793557 := by
  unfold tailWord_2890754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26358615042324858580681829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70289640112866289548484877 26358615042324858580681829)
  ·
    refine ⟨4942240320435910983877843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26358615042324858580681829 4942240320435910983877843)
    ·
      refine ⟨7413360480653866475816765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4942240320435910983877843 7413360480653866475816765)
      ·
        refine ⟨2780010180245199928431287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7413360480653866475816765 2780010180245199928431287)
        ·
          refine ⟨4170015270367799892646931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780010180245199928431287 4170015270367799892646931)
          ·
            refine ⟨6255022905551699838970397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4170015270367799892646931 6255022905551699838970397)
            ·
              refine ⟨2345633589581887439613899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6255022905551699838970397 2345633589581887439613899)
              ·
                refine ⟨3518450384372831159420849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345633589581887439613899 3518450384372831159420849)
                ·
                  refine ⟨2638837788279623369565637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3518450384372831159420849 2638837788279623369565637)
                  ·
                    refine ⟨494782085302429381793557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638837788279623369565637 494782085302429381793557)
                    ·
                      rfl

theorem cell23_2890754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2890754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890754 prefixEnd_2890754 := by exact prefixLift 2890754
  have htrace : WordTrace (prefixWord ++ tailWord_2890754) baseStart_2890754 baseEnd_2890754 := by
    simpa [prefixWord, tailWord_2890754, baseEnd_2890754] using wordTrace_append hprefix tailTrace_2890754
  have hstable : (prefixWord ++ tailWord_2890754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890754).length < 2 ^ (prefixWord ++ tailWord_2890754).sum := by decide
  have hdescent : baseEnd_2890754 < baseStart_2890754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890769 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2890769 : Nat := 118140960795 + 2890769 * 2 ^ 59
def prefixEnd_2890769 : Nat := 4983230072969 + 3 ^ 40 * 2890769 * 2
def baseEnd_2890769 : Nat := 1484353958117105586693101

theorem tailTrace_2890769 : CollatzResearch.WordTrace tailWord_2890769 prefixEnd_2890769 1484353958117105586693101 := by
  unfold tailWord_2890769
  simp only [CollatzResearch.WordTrace]
  refine ⟨105435007264245091884523361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70290004842830061256348907 105435007264245091884523361)
  ·
    refine ⟨79076255448183818913392521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105435007264245091884523361 79076255448183818913392521)
    ·
      refine ⟨59307191586137864185044391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79076255448183818913392521 59307191586137864185044391)
      ·
        refine ⟨88960787379206796277566587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59307191586137864185044391 88960787379206796277566587)
        ·
          refine ⟨133441181068810194416349881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88960787379206796277566587 133441181068810194416349881)
          ·
            refine ⟨100080885801607645812262411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133441181068810194416349881 100080885801607645812262411)
            ·
              refine ⟨150121328702411468718393617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100080885801607645812262411 150121328702411468718393617)
              ·
                refine ⟨112590996526808601538795213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150121328702411468718393617 112590996526808601538795213)
                ·
                  refine ⟨42221623697553225577048205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112590996526808601538795213 42221623697553225577048205)
                  ·
                    refine ⟨15833108886582459591393077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42221623697553225577048205 15833108886582459591393077)
                    ·
                      refine ⟨1484353958117105586693101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15833108886582459591393077 1484353958117105586693101)
                      ·
                        rfl

theorem cell23_2890769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2890769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890769 prefixEnd_2890769 := by exact prefixLift 2890769
  have htrace : WordTrace (prefixWord ++ tailWord_2890769) baseStart_2890769 baseEnd_2890769 := by
    simpa [prefixWord, tailWord_2890769, baseEnd_2890769] using wordTrace_append hprefix tailTrace_2890769
  have hstable : (prefixWord ++ tailWord_2890769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890769).length < 2 ^ (prefixWord ++ tailWord_2890769).sum := by decide
  have hdescent : baseEnd_2890769 < baseStart_2890769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890786 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2890786 : Nat := 118140960795 + 2890786 * 2 ^ 59
def prefixEnd_2890786 : Nat := 4983230072969 + 3 ^ 40 * 2890786 * 2
def baseEnd_2890786 : Nat := 1484362687288232020180523

theorem tailTrace_2890786 : CollatzResearch.WordTrace tailWord_2890786 prefixEnd_2890786 1484362687288232020180523 := by
  unfold tailWord_2890786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26358906826295875946973053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70290418203455669191928141 26358906826295875946973053)
  ·
    refine ⟨9884590059860953480114895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26358906826295875946973053 9884590059860953480114895)
    ·
      refine ⟨14826885089791430220172343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9884590059860953480114895 14826885089791430220172343)
      ·
        refine ⟨22240327634687145330258515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14826885089791430220172343 22240327634687145330258515)
        ·
          refine ⟨33360491452030717995387773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22240327634687145330258515 33360491452030717995387773)
          ·
            refine ⟨12510184294511519248270415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33360491452030717995387773 12510184294511519248270415)
            ·
              refine ⟨18765276441767278872405623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12510184294511519248270415 18765276441767278872405623)
              ·
                refine ⟨28147914662650918308608435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18765276441767278872405623 28147914662650918308608435)
                ·
                  refine ⟨42221871993976377462912653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28147914662650918308608435 42221871993976377462912653)
                  ·
                    refine ⟨15833201997741141548592245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42221871993976377462912653 15833201997741141548592245)
                    ·
                      refine ⟨1484362687288232020180523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15833201997741141548592245 1484362687288232020180523)
                      ·
                        rfl

theorem cell23_2890786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2890786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890786 prefixEnd_2890786 := by exact prefixLift 2890786
  have htrace : WordTrace (prefixWord ++ tailWord_2890786) baseStart_2890786 baseEnd_2890786 := by
    simpa [prefixWord, tailWord_2890786, baseEnd_2890786] using wordTrace_append hprefix tailTrace_2890786
  have hstable : (prefixWord ++ tailWord_2890786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890786).length < 2 ^ (prefixWord ++ tailWord_2890786).sum := by decide
  have hdescent : baseEnd_2890786 < baseStart_2890786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890800 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 2, 2, 2]
def baseStart_2890800 : Nat := 118140960795 + 2890800 * 2 ^ 59
def prefixEnd_2890800 : Nat := 4983230072969 + 3 ^ 40 * 2890800 * 2
def baseEnd_2890800 : Nat := 1484369876017394965405459

theorem tailTrace_2890800 : CollatzResearch.WordTrace tailWord_2890800 prefixEnd_2890800 1484369876017394965405459 := by
  unfold tailWord_2890800
  simp only [CollatzResearch.WordTrace]
  refine ⟨52718068963566392089450927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70290758618088522785934569 52718068963566392089450927)
  ·
    refine ⟨79077103445349588134176391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52718068963566392089450927 79077103445349588134176391)
    ·
      refine ⟨118615655168024382201264587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79077103445349588134176391 118615655168024382201264587)
      ·
        refine ⟨177923482752036573301896881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118615655168024382201264587 177923482752036573301896881)
        ·
          refine ⟨133442612064027429976422661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177923482752036573301896881 133442612064027429976422661)
          ·
            refine ⟨25020489762005143120579249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133442612064027429976422661 25020489762005143120579249)
            ·
              refine ⟨18765367321503857340434437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25020489762005143120579249 18765367321503857340434437)
              ·
                refine ⟨3518506372781973251331457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18765367321503857340434437 3518506372781973251331457)
                ·
                  refine ⟨2638879779586479938498593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3518506372781973251331457 2638879779586479938498593)
                  ·
                    refine ⟨1979159834689859953873945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2638879779586479938498593 1979159834689859953873945)
                    ·
                      refine ⟨1484369876017394965405459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979159834689859953873945 1484369876017394965405459)
                      ·
                        rfl

theorem cell23_2890800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 2, 2, 2].length) (baseStart_2890800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890800 prefixEnd_2890800 := by exact prefixLift 2890800
  have htrace : WordTrace (prefixWord ++ tailWord_2890800) baseStart_2890800 baseEnd_2890800 := by
    simpa [prefixWord, tailWord_2890800, baseEnd_2890800] using wordTrace_append hprefix tailTrace_2890800
  have hstable : (prefixWord ++ tailWord_2890800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890800).length < 2 ^ (prefixWord ++ tailWord_2890800).sum := by decide
  have hdescent : baseEnd_2890800 < baseStart_2890800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890816 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_2890816 : Nat := 118140960795 + 2890816 * 2 ^ 59
def prefixEnd_2890816 : Nat := 4983230072969 + 3 ^ 40 * 2890816 * 2
def baseEnd_2890816 : Nat := 1484378091707866902805385

theorem tailTrace_2890816 : CollatzResearch.WordTrace tailWord_2890816 prefixEnd_2890816 1484378091707866902805385 := by
  unfold tailWord_2890816
  simp only [CollatzResearch.WordTrace]
  refine ⟨52718360747537409455742151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70291147663383212607656201 52718360747537409455742151)
  ·
    refine ⟨79077541121306114183613227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52718360747537409455742151 79077541121306114183613227)
    ·
      refine ⟨118616311681959171275419841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79077541121306114183613227 118616311681959171275419841)
      ·
        refine ⟨88962233761469378456564881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118616311681959171275419841 88962233761469378456564881)
        ·
          refine ⟨66721675321102033842423661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88962233761469378456564881 66721675321102033842423661)
          ·
            refine ⟨25020628245413262690908873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66721675321102033842423661 25020628245413262690908873)
            ·
              refine ⟨18765471184059947018181655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25020628245413262690908873 18765471184059947018181655)
              ·
                refine ⟨28148206776089920527272483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18765471184059947018181655 28148206776089920527272483)
                ·
                  refine ⟨42222310164134880790908725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28148206776089920527272483 42222310164134880790908725)
                  ·
                    refine ⟨3958341577887645074147693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42222310164134880790908725 3958341577887645074147693)
                    ·
                      refine ⟨1484378091707866902805385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3958341577887645074147693 1484378091707866902805385)
                      ·
                        rfl

theorem cell23_2890816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_2890816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890816 prefixEnd_2890816 := by exact prefixLift 2890816
  have htrace : WordTrace (prefixWord ++ tailWord_2890816) baseStart_2890816 baseEnd_2890816 := by
    simpa [prefixWord, tailWord_2890816, baseEnd_2890816] using wordTrace_append hprefix tailTrace_2890816
  have hstable : (prefixWord ++ tailWord_2890816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890816).length < 2 ^ (prefixWord ++ tailWord_2890816).sum := by decide
  have hdescent : baseEnd_2890816 < baseStart_2890816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890836 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_2890836 : Nat := 118140960795 + 2890836 * 2 ^ 59
def prefixEnd_2890836 : Nat := 4983230072969 + 3 ^ 40 * 2890836 * 2
def baseEnd_2890836 : Nat := 494796120440318941518431

theorem tailTrace_2890836 : CollatzResearch.WordTrace tailWord_2890836 prefixEnd_2890836 494796120440318941518431 := by
  unfold tailWord_2890836
  simp only [CollatzResearch.WordTrace]
  refine ⟨52718725477501181163606181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70291633970001574884808241 52718725477501181163606181)
  ·
    refine ⟨9884761027031471468176159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52718725477501181163606181 9884761027031471468176159)
    ·
      refine ⟨14827141540547207202264239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9884761027031471468176159 14827141540547207202264239)
      ·
        refine ⟨22240712310820810803396359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14827141540547207202264239 22240712310820810803396359)
        ·
          refine ⟨33361068466231216205094539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22240712310820810803396359 33361068466231216205094539)
          ·
            refine ⟨50041602699346824307641809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33361068466231216205094539 50041602699346824307641809)
            ·
              refine ⟨37531202024510118230731357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50041602699346824307641809 37531202024510118230731357)
              ·
                refine ⟨14074200759191294336524259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37531202024510118230731357 14074200759191294336524259)
                ·
                  refine ⟨21111301138786941504786389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14074200759191294336524259 21111301138786941504786389)
                  ·
                    refine ⟨494796120440318941518431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21111301138786941504786389 494796120440318941518431)
                    ·
                      rfl

theorem cell23_2890836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_2890836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890836 prefixEnd_2890836 := by exact prefixLift 2890836
  have htrace : WordTrace (prefixWord ++ tailWord_2890836) baseStart_2890836 baseEnd_2890836 := by
    simpa [prefixWord, tailWord_2890836, baseEnd_2890836] using wordTrace_append hprefix tailTrace_2890836
  have hstable : (prefixWord ++ tailWord_2890836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890836).length < 2 ^ (prefixWord ++ tailWord_2890836).sum := by decide
  have hdescent : baseEnd_2890836 < baseStart_2890836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890883 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 3, 4]
def baseStart_2890883 : Nat := 118140960795 + 2890883 * 2 ^ 59
def prefixEnd_2890883 : Nat := 4983230072969 + 3 ^ 40 * 2890883 * 2
def baseEnd_2890883 : Nat := 494804164970572713555859

theorem tailTrace_2890883 : CollatzResearch.WordTrace tailWord_2890883 prefixEnd_2890883 494804164970572713555859 := by
  unfold tailWord_2890883
  simp only [CollatzResearch.WordTrace]
  refine ⟨105439165185832089354173303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70292776790554726236115535 105439165185832089354173303)
  ·
    refine ⟨158158747778748134031259955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105439165185832089354173303 158158747778748134031259955)
    ·
      refine ⟨237238121668122201046889933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158158747778748134031259955 237238121668122201046889933)
      ·
        refine ⟨88964295625545825392583725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237238121668122201046889933 88964295625545825392583725)
        ·
          refine ⟨33361610859579684522218897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88964295625545825392583725 33361610859579684522218897)
          ·
            refine ⟨25021208144684763391664173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33361610859579684522218897 25021208144684763391664173)
            ·
              refine ⟨9382953054256786271874065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25021208144684763391664173 9382953054256786271874065)
              ·
                refine ⟨7037214790692589703905549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9382953054256786271874065 7037214790692589703905549)
                ·
                  refine ⟨2638955546509721138964581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7037214790692589703905549 2638955546509721138964581)
                  ·
                    refine ⟨494804164970572713555859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2638955546509721138964581 494804164970572713555859)
                    ·
                      rfl

theorem cell23_2890883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 4].length) (baseStart_2890883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890883 prefixEnd_2890883 := by exact prefixLift 2890883
  have htrace : WordTrace (prefixWord ++ tailWord_2890883) baseStart_2890883 baseEnd_2890883 := by
    simpa [prefixWord, tailWord_2890883, baseEnd_2890883] using wordTrace_append hprefix tailTrace_2890883
  have hstable : (prefixWord ++ tailWord_2890883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890883).length < 2 ^ (prefixWord ++ tailWord_2890883).sum := by decide
  have hdescent : baseEnd_2890883 < baseStart_2890883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890930 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_2890930 : Nat := 118140960795 + 2890930 * 2 ^ 59
def prefixEnd_2890930 : Nat := 4983230072969 + 3 ^ 40 * 2890930 * 2
def baseEnd_2890930 : Nat := 164937403166942161864429

theorem tailTrace_2890930 : CollatzResearch.WordTrace tailWord_2890930 prefixEnd_2890930 164937403166942161864429 := by
  unfold tailWord_2890930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26360219854165454095283561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70293919611107877587422829 26360219854165454095283561)
  ·
    refine ⟨19770164890624090571462671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26360219854165454095283561 19770164890624090571462671)
    ·
      refine ⟨29655247335936135857194007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19770164890624090571462671 29655247335936135857194007)
      ·
        refine ⟨44482871003904203785791011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29655247335936135857194007 44482871003904203785791011)
        ·
          refine ⟨66724306505856305678686517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44482871003904203785791011 66724306505856305678686517)
          ·
            refine ⟨6255403734924028657376861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66724306505856305678686517 6255403734924028657376861)
            ·
              refine ⟨2345776400596510746516323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6255403734924028657376861 2345776400596510746516323)
              ·
                refine ⟨3518664600894766119774485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345776400596510746516323 3518664600894766119774485)
                ·
                  refine ⟨164937403166942161864429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3518664600894766119774485 164937403166942161864429)
                  ·
                    rfl

theorem cell23_2890930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_2890930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890930 prefixEnd_2890930 := by exact prefixLift 2890930
  have htrace : WordTrace (prefixWord ++ tailWord_2890930) baseStart_2890930 baseEnd_2890930 := by
    simpa [prefixWord, tailWord_2890930, baseEnd_2890930] using wordTrace_append hprefix tailTrace_2890930
  have hstable : (prefixWord ++ tailWord_2890930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890930).length < 2 ^ (prefixWord ++ tailWord_2890930).sum := by decide
  have hdescent : baseEnd_2890930 < baseStart_2890930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890943 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 1, 5]
def baseStart_2890943 : Nat := 118140960795 + 2890943 * 2 ^ 59
def prefixEnd_2890943 : Nat := 4983230072969 + 3 ^ 40 * 2890943 * 2
def baseEnd_2890943 : Nat := 494814434583662635305767

theorem tailTrace_2890943 : CollatzResearch.WordTrace tailWord_2890943 prefixEnd_2890943 494814434583662635305767 := by
  unfold tailWord_2890943
  simp only [CollatzResearch.WordTrace]
  refine ⟨105441353565614719601357483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70294235710409813067571655 105441353565614719601357483)
  ·
    refine ⟨158162030348422079402036225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105441353565614719601357483 158162030348422079402036225)
    ·
      refine ⟨118621522761316559551527169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158162030348422079402036225 118621522761316559551527169)
      ·
        refine ⟨88966142070987419663645377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118621522761316559551527169 88966142070987419663645377)
        ·
          refine ⟨66724606553240564747734033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88966142070987419663645377 66724606553240564747734033)
          ·
            refine ⟨50043454914930423560800525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66724606553240564747734033 50043454914930423560800525)
            ·
              refine ⟨18766295593098908835300197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50043454914930423560800525 18766295593098908835300197)
              ·
                refine ⟨3518680423706045406618787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18766295593098908835300197 3518680423706045406618787)
                ·
                  refine ⟨5278020635559068109928181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518680423706045406618787 5278020635559068109928181)
                  ·
                    refine ⟨494814434583662635305767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5278020635559068109928181 494814434583662635305767)
                    ·
                      rfl

theorem cell23_2890943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_2890943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890943 prefixEnd_2890943 := by exact prefixLift 2890943
  have htrace : WordTrace (prefixWord ++ tailWord_2890943) baseStart_2890943 baseEnd_2890943 := by
    simpa [prefixWord, tailWord_2890943, baseEnd_2890943] using wordTrace_append hprefix tailTrace_2890943
  have hstable : (prefixWord ++ tailWord_2890943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890943).length < 2 ^ (prefixWord ++ tailWord_2890943).sum := by decide
  have hdescent : baseEnd_2890943 < baseStart_2890943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890963 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 8, 2]
def baseStart_2890963 : Nat := 118140960795 + 2890963 * 2 ^ 59
def prefixEnd_2890963 : Nat := 4983230072969 + 3 ^ 40 * 2890963 * 2
def baseEnd_2890963 : Nat := 1484453573364077827667209

theorem tailTrace_2890963 : CollatzResearch.WordTrace tailWord_2890963 prefixEnd_2890963 1484453573364077827667209 := by
  unfold tailWord_2890963
  simp only [CollatzResearch.WordTrace]
  refine ⟨105442083025542263017085543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70294722017028175344723695 105442083025542263017085543)
  ·
    refine ⟨158163124538313394525628315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105442083025542263017085543 158163124538313394525628315)
    ·
      refine ⟨237244686807470091788442473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158163124538313394525628315 237244686807470091788442473)
      ·
        refine ⟨177933515105602568841331855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237244686807470091788442473 177933515105602568841331855)
        ·
          refine ⟨266900272658403853261997783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177933515105602568841331855 266900272658403853261997783)
          ·
            refine ⟨400350408987605779892996675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266900272658403853261997783 400350408987605779892996675)
            ·
              refine ⟨600525613481408669839495013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400350408987605779892996675 600525613481408669839495013)
              ·
                refine ⟨112598552527764125594905315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600525613481408669839495013 112598552527764125594905315)
                ·
                  refine ⟨168897828791646188392357973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112598552527764125594905315 168897828791646188392357973)
                  ·
                    refine ⟨1979271431152103770222945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 168897828791646188392357973 1979271431152103770222945)
                    ·
                      refine ⟨1484453573364077827667209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979271431152103770222945 1484453573364077827667209)
                      ·
                        rfl

theorem cell23_2890963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 8, 2].length) (baseStart_2890963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890963 prefixEnd_2890963 := by exact prefixLift 2890963
  have htrace : WordTrace (prefixWord ++ tailWord_2890963) baseStart_2890963 baseEnd_2890963 := by
    simpa [prefixWord, tailWord_2890963, baseEnd_2890963] using wordTrace_append hprefix tailTrace_2890963
  have hstable : (prefixWord ++ tailWord_2890963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890963).length < 2 ^ (prefixWord ++ tailWord_2890963).sum := by decide
  have hdescent : baseEnd_2890963 < baseStart_2890963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890993 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2890993 : Nat := 118140960795 + 2890993 * 2 ^ 59
def prefixEnd_2890993 : Nat := 4983230072969 + 3 ^ 40 * 2890993 * 2
def baseEnd_2890993 : Nat := 1484468977783712710292071

theorem tailTrace_2890993 : CollatzResearch.WordTrace tailWord_2890993 prefixEnd_2890993 1484468977783712710292071 := by
  unfold tailWord_2890993
  simp only [CollatzResearch.WordTrace]
  refine ⟨105443177215433578140677633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70295451476955718760451755 105443177215433578140677633)
  ·
    refine ⟨79082382911575183605508225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105443177215433578140677633 79082382911575183605508225)
    ·
      refine ⟨59311787183681387704131169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79082382911575183605508225 59311787183681387704131169)
      ·
        refine ⟨44483840387761040778098377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59311787183681387704131169 44483840387761040778098377)
        ·
          refine ⟨33362880290820780583573783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44483840387761040778098377 33362880290820780583573783)
          ·
            refine ⟨50044320436231170875360675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33362880290820780583573783 50044320436231170875360675)
            ·
              refine ⟨75066480654346756313041013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50044320436231170875360675 75066480654346756313041013)
              ·
                refine ⟨7037482561345008404347595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75066480654346756313041013 7037482561345008404347595)
                ·
                  refine ⟨10556223842017512606521393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7037482561345008404347595 10556223842017512606521393)
                  ·
                    refine ⟨7917167881513134454891045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10556223842017512606521393 7917167881513134454891045)
                    ·
                      refine ⟨1484468977783712710292071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7917167881513134454891045 1484468977783712710292071)
                      ·
                        rfl

theorem cell23_2890993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2890993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890993 prefixEnd_2890993 := by exact prefixLift 2890993
  have htrace : WordTrace (prefixWord ++ tailWord_2890993) baseStart_2890993 baseEnd_2890993 := by
    simpa [prefixWord, tailWord_2890993, baseEnd_2890993] using wordTrace_append hprefix tailTrace_2890993
  have hstable : (prefixWord ++ tailWord_2890993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890993).length < 2 ^ (prefixWord ++ tailWord_2890993).sum := by decide
  have hdescent : baseEnd_2890993 < baseStart_2890993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890994 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_2890994 : Nat := 118140960795 + 2890994 * 2 ^ 59
def prefixEnd_2890994 : Nat := 4983230072969 + 3 ^ 40 * 2890994 * 2
def baseEnd_2890994 : Nat := 494823163754789068793189

theorem tailTrace_2890994 : CollatzResearch.WordTrace tailWord_2890994 prefixEnd_2890994 494823163754789068793189 := by
  unfold tailWord_2890994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26360803422107488827866009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70295475792286636874309357 26360803422107488827866009)
  ·
    refine ⟨19770602566580616620899507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26360803422107488827866009 19770602566580616620899507)
    ·
      refine ⟨29655903849870924931349261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19770602566580616620899507 29655903849870924931349261)
      ·
        refine ⟨11120963943701596849255973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29655903849870924931349261 11120963943701596849255973)
        ·
          refine ⟨2085180739444049409235495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11120963943701596849255973 2085180739444049409235495)
          ·
            refine ⟨3127771109166074113853243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085180739444049409235495 3127771109166074113853243)
            ·
              refine ⟨4691656663749111170779865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127771109166074113853243 4691656663749111170779865)
              ·
                refine ⟨3518742497811833378084899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4691656663749111170779865 3518742497811833378084899)
                ·
                  refine ⟨5278113746717750067127349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518742497811833378084899 5278113746717750067127349)
                  ·
                    refine ⟨494823163754789068793189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5278113746717750067127349 494823163754789068793189)
                    ·
                      rfl

theorem cell23_2890994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_2890994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2890994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2890994 prefixEnd_2890994 := by exact prefixLift 2890994
  have htrace : WordTrace (prefixWord ++ tailWord_2890994) baseStart_2890994 baseEnd_2890994 := by
    simpa [prefixWord, tailWord_2890994, baseEnd_2890994] using wordTrace_append hprefix tailTrace_2890994
  have hstable : (prefixWord ++ tailWord_2890994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890994).length < 2 ^ (prefixWord ++ tailWord_2890994).sum := by decide
  have hdescent : baseEnd_2890994 < baseStart_2890994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891017 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 1, 2, 3]
def baseStart_2891017 : Nat := 118140960795 + 2891017 * 2 ^ 59
def prefixEnd_2891017 : Nat := 4983230072969 + 3 ^ 40 * 2891017 * 2
def baseEnd_2891017 : Nat := 1484481301319420616391961

theorem tailTrace_2891017 : CollatzResearch.WordTrace tailWord_2891017 prefixEnd_2891017 1484481301319420616391961 := by
  unfold tailWord_2891017
  simp only [CollatzResearch.WordTrace]
  refine ⟨105444052567346630239551305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70296035044897753493034203 105444052567346630239551305)
  ·
    refine ⟨79083039425509972679663479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105444052567346630239551305 79083039425509972679663479)
    ·
      refine ⟨118624559138264959019495219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79083039425509972679663479 118624559138264959019495219)
      ·
        refine ⟨177936838707397438529242829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118624559138264959019495219 177936838707397438529242829)
        ·
          refine ⟨66726314515274039448466061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177936838707397438529242829 66726314515274039448466061)
          ·
            refine ⟨25022367943227764793174773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66726314515274039448466061 25022367943227764793174773)
            ·
              refine ⟨2345846994677602949360135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25022367943227764793174773 2345846994677602949360135)
              ·
                refine ⟨3518770492016404424040203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345846994677602949360135 3518770492016404424040203)
                ·
                  refine ⟨5278155738024606636060305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518770492016404424040203 5278155738024606636060305)
                  ·
                    refine ⟨3958616803518454977045229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5278155738024606636060305 3958616803518454977045229)
                    ·
                      refine ⟨1484481301319420616391961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3958616803518454977045229 1484481301319420616391961)
                      ·
                        rfl

theorem cell23_2891017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 2, 3].length) (baseStart_2891017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891017 prefixEnd_2891017 := by exact prefixLift 2891017
  have htrace : WordTrace (prefixWord ++ tailWord_2891017) baseStart_2891017 baseEnd_2891017 := by
    simpa [prefixWord, tailWord_2891017, baseEnd_2891017] using wordTrace_append hprefix tailTrace_2891017
  have hstable : (prefixWord ++ tailWord_2891017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891017).length < 2 ^ (prefixWord ++ tailWord_2891017).sum := by decide
  have hdescent : baseEnd_2891017 < baseStart_2891017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891057 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 3, 3, 2]
def baseStart_2891057 : Nat := 118140960795 + 2891057 * 2 ^ 59
def prefixEnd_2891057 : Nat := 4983230072969 + 3 ^ 40 * 2891057 * 2
def baseEnd_2891057 : Nat := 1484501840545600459891777

theorem tailTrace_2891057 : CollatzResearch.WordTrace tailWord_2891057 prefixEnd_2891057 1484501840545600459891777 := by
  unfold tailWord_2891057
  simp only [CollatzResearch.WordTrace]
  refine ⟨105445511487201717071007425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70297007658134478047338283 105445511487201717071007425)
  ·
    refine ⟨79084133615401287803255569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105445511487201717071007425 79084133615401287803255569)
    ·
      refine ⟨59313100211550965852441677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79084133615401287803255569 59313100211550965852441677)
      ·
        refine ⟨22242412579331612194665629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59313100211550965852441677 22242412579331612194665629)
        ·
          refine ⟨8340904717249354572999611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22242412579331612194665629 8340904717249354572999611)
          ·
            refine ⟨12511357075874031859499417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340904717249354572999611 12511357075874031859499417)
            ·
              refine ⟨9383517806905523894624563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12511357075874031859499417 9383517806905523894624563)
              ·
                refine ⟨14075276710358285841936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9383517806905523894624563 14075276710358285841936845)
                ·
                  refine ⟨5278228766384357190726317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14075276710358285841936845 5278228766384357190726317)
                  ·
                    refine ⟨1979335787394133946522369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5278228766384357190726317 1979335787394133946522369)
                    ·
                      refine ⟨1484501840545600459891777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979335787394133946522369 1484501840545600459891777)
                      ·
                        rfl

theorem cell23_2891057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_2891057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891057 prefixEnd_2891057 := by exact prefixLift 2891057
  have htrace : WordTrace (prefixWord ++ tailWord_2891057) baseStart_2891057 baseEnd_2891057 := by
    simpa [prefixWord, tailWord_2891057, baseEnd_2891057] using wordTrace_append hprefix tailTrace_2891057
  have hstable : (prefixWord ++ tailWord_2891057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891057).length < 2 ^ (prefixWord ++ tailWord_2891057).sum := by decide
  have hdescent : baseEnd_2891057 < baseStart_2891057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891060 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2891060 : Nat := 118140960795 + 2891060 * 2 ^ 59
def prefixEnd_2891060 : Nat := 4983230072969 + 3 ^ 40 * 2891060 * 2
def baseEnd_2891060 : Nat := 1484503380987563948154263

theorem tailTrace_2891060 : CollatzResearch.WordTrace tailWord_2891060 prefixEnd_2891060 1484503380987563948154263 := by
  unfold tailWord_2891060
  simp only [CollatzResearch.WordTrace]
  refine ⟨52722810453095424291683317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70297080604127232388911089 52722810453095424291683317)
  ·
    refine ⟨4942763479977696027345311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52722810453095424291683317 4942763479977696027345311)
    ·
      refine ⟨7414145219966544041017967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4942763479977696027345311 7414145219966544041017967)
      ·
        refine ⟨11121217829949816061526951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7414145219966544041017967 11121217829949816061526951)
        ·
          refine ⟨16681826744924724092290427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11121217829949816061526951 16681826744924724092290427)
          ·
            refine ⟨25022740117387086138435641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16681826744924724092290427 25022740117387086138435641)
            ·
              refine ⟨18767055088040314603826731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25022740117387086138435641 18767055088040314603826731)
              ·
                refine ⟨28150582632060471905740097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18767055088040314603826731 28150582632060471905740097)
                ·
                  refine ⟨21112936974045353929305073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28150582632060471905740097 21112936974045353929305073)
                  ·
                    refine ⟨15834702730534015446978805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21112936974045353929305073 15834702730534015446978805)
                    ·
                      refine ⟨1484503380987563948154263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15834702730534015446978805 1484503380987563948154263)
                      ·
                        rfl

theorem cell23_2891060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2891060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891060 prefixEnd_2891060 := by exact prefixLift 2891060
  have htrace : WordTrace (prefixWord ++ tailWord_2891060) baseStart_2891060 baseEnd_2891060 := by
    simpa [prefixWord, tailWord_2891060, baseEnd_2891060] using wordTrace_append hprefix tailTrace_2891060
  have hstable : (prefixWord ++ tailWord_2891060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891060).length < 2 ^ (prefixWord ++ tailWord_2891060).sum := by decide
  have hdescent : baseEnd_2891060 < baseStart_2891060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891104 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 1, 4, 2]
def baseStart_2891104 : Nat := 118140960795 + 2891104 * 2 ^ 59
def prefixEnd_2891104 : Nat := 4983230072969 + 3 ^ 40 * 2891104 * 2
def baseEnd_2891104 : Nat := 1484525974136361776004061

theorem tailTrace_2891104 : CollatzResearch.WordTrace tailWord_2891104 prefixEnd_2891104 1484525974136361776004061 := by
  unfold tailWord_2891104
  simp only [CollatzResearch.WordTrace]
  refine ⟨52723612859015722048984183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70298150478687629398645577 52723612859015722048984183)
  ·
    refine ⟨79085419288523583073476275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52723612859015722048984183 79085419288523583073476275)
    ·
      refine ⟨118628128932785374610214413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79085419288523583073476275 118628128932785374610214413)
      ·
        refine ⟨44485548349794515478830405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118628128932785374610214413 44485548349794515478830405)
        ·
          refine ⟨8341040315586471652280701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44485548349794515478830405 8341040315586471652280701)
          ·
            refine ⟨3127890118344926869605263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8341040315586471652280701 3127890118344926869605263)
            ·
              refine ⟨4691835177517390304407895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127890118344926869605263 4691835177517390304407895)
              ·
                refine ⟨7037752766276085456611843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691835177517390304407895 7037752766276085456611843)
                ·
                  refine ⟨10556629149414128184917765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7037752766276085456611843 10556629149414128184917765)
                  ·
                    refine ⟨1979367965515149034672081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10556629149414128184917765 1979367965515149034672081)
                    ·
                      refine ⟨1484525974136361776004061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979367965515149034672081 1484525974136361776004061)
                      ·
                        rfl

theorem cell23_2891104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_2891104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891104 prefixEnd_2891104 := by exact prefixLift 2891104
  have htrace : WordTrace (prefixWord ++ tailWord_2891104) baseStart_2891104 baseEnd_2891104 := by
    simpa [prefixWord, tailWord_2891104, baseEnd_2891104] using wordTrace_append hprefix tailTrace_2891104
  have hstable : (prefixWord ++ tailWord_2891104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891104).length < 2 ^ (prefixWord ++ tailWord_2891104).sum := by decide
  have hdescent : baseEnd_2891104 < baseStart_2891104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891140 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2891140 : Nat := 118140960795 + 2891140 * 2 ^ 59
def prefixEnd_2891140 : Nat := 4983230072969 + 3 ^ 40 * 2891140 * 2
def baseEnd_2891140 : Nat := 494848153146641211717965

theorem tailTrace_2891140 : CollatzResearch.WordTrace tailWord_2891140 prefixEnd_2891140 494848153146641211717965 := by
  unfold tailWord_2891140
  simp only [CollatzResearch.WordTrace]
  refine ⟨52724269372950511123139437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70299025830600681497519249 52724269372950511123139437)
  ·
    refine ⟨19771601014856441671177289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52724269372950511123139437 19771601014856441671177289)
    ·
      refine ⟨14828700761142331253382967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19771601014856441671177289 14828700761142331253382967)
      ·
        refine ⟨22243051141713496880074451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14828700761142331253382967 22243051141713496880074451)
        ·
          refine ⟨33364576712570245320111677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22243051141713496880074451 33364576712570245320111677)
          ·
            refine ⟨12511716267213841995041879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33364576712570245320111677 12511716267213841995041879)
            ·
              refine ⟨18767574400820762992562819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12511716267213841995041879 18767574400820762992562819)
              ·
                refine ⟨28151361601231144488844229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18767574400820762992562819 28151361601231144488844229)
                ·
                  refine ⟨5278380300230839591658293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28151361601231144488844229 5278380300230839591658293)
                  ·
                    refine ⟨494848153146641211717965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5278380300230839591658293 494848153146641211717965)
                    ·
                      rfl

theorem cell23_2891140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2891140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891140 prefixEnd_2891140 := by exact prefixLift 2891140
  have htrace : WordTrace (prefixWord ++ tailWord_2891140) baseStart_2891140 baseEnd_2891140 := by
    simpa [prefixWord, tailWord_2891140, baseEnd_2891140] using wordTrace_append hprefix tailTrace_2891140
  have hstable : (prefixWord ++ tailWord_2891140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891140).length < 2 ^ (prefixWord ++ tailWord_2891140).sum := by decide
  have hdescent : baseEnd_2891140 < baseStart_2891140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891144 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 5]
def baseStart_2891144 : Nat := 118140960795 + 2891144 * 2 ^ 59
def prefixEnd_2891144 : Nat := 4983230072969 + 3 ^ 40 * 2891144 * 2
def baseEnd_2891144 : Nat := 164949612595837957722653

theorem tailTrace_2891144 : CollatzResearch.WordTrace tailWord_2891144 prefixEnd_2891144 164949612595837957722653 := by
  unfold tailWord_2891144
  simp only [CollatzResearch.WordTrace]
  refine ⟨52724342318943265464712243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70299123091924353952949657 52724342318943265464712243)
  ·
    refine ⟨79086513478414898197068365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52724342318943265464712243 79086513478414898197068365)
    ·
      refine ⟨29657442554405586823900637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79086513478414898197068365 29657442554405586823900637)
      ·
        refine ⟨11121540957902095058962739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29657442554405586823900637 11121540957902095058962739)
        ·
          refine ⟨16682311436853142588444109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11121540957902095058962739 16682311436853142588444109)
          ·
            refine ⟨6255866788819928470666541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16682311436853142588444109 6255866788819928470666541)
            ·
              refine ⟨2345950045807473176499953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6255866788819928470666541 2345950045807473176499953)
              ·
                refine ⟨1759462534355604882374965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345950045807473176499953 1759462534355604882374965)
                ·
                  refine ⟨164949612595837957722653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1759462534355604882374965 164949612595837957722653)
                  ·
                    rfl

theorem cell23_2891144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 5].length) (baseStart_2891144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891144 prefixEnd_2891144 := by exact prefixLift 2891144
  have htrace : WordTrace (prefixWord ++ tailWord_2891144) baseStart_2891144 baseEnd_2891144 := by
    simpa [prefixWord, tailWord_2891144, baseEnd_2891144] using wordTrace_append hprefix tailTrace_2891144
  have hstable : (prefixWord ++ tailWord_2891144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891144).length < 2 ^ (prefixWord ++ tailWord_2891144).sum := by decide
  have hdescent : baseEnd_2891144 < baseStart_2891144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891163 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_2891163 : Nat := 118140960795 + 2891163 * 2 ^ 59
def prefixEnd_2891163 : Nat := 4983230072969 + 3 ^ 40 * 2891163 * 2
def baseEnd_2891163 : Nat := 1484556269494977045166289

theorem tailTrace_2891163 : CollatzResearch.WordTrace tailWord_2891163 prefixEnd_2891163 1484556269494977045166289 := by
  unfold tailWord_2891163
  simp only [CollatzResearch.WordTrace]
  refine ⟨105449377624817697174366143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70299585083211798116244095 105449377624817697174366143)
  ·
    refine ⟨158174066437226545761549215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105449377624817697174366143 158174066437226545761549215)
    ·
      refine ⟨237261099655839818642323823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158174066437226545761549215 237261099655839818642323823)
      ·
        refine ⟨355891649483759727963485735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237261099655839818642323823 355891649483759727963485735)
        ·
          refine ⟨533837474225639591945228603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355891649483759727963485735 533837474225639591945228603)
          ·
            refine ⟨800756211338459387917842905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533837474225639591945228603 800756211338459387917842905)
            ·
              refine ⟨600567158503844540938382179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800756211338459387917842905 600567158503844540938382179)
              ·
                refine ⟨900850737755766811407573269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600567158503844540938382179 900850737755766811407573269)
                ·
                  refine ⟨42227378332301569284729997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 900850737755766811407573269 42227378332301569284729997)
                  ·
                    refine ⟨15835266874613088481773749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42227378332301569284729997 15835266874613088481773749)
                    ·
                      refine ⟨1484556269494977045166289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15835266874613088481773749 1484556269494977045166289)
                      ·
                        rfl

theorem cell23_2891163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_2891163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891163 prefixEnd_2891163 := by exact prefixLift 2891163
  have htrace : WordTrace (prefixWord ++ tailWord_2891163) baseStart_2891163 baseEnd_2891163 := by
    simpa [prefixWord, tailWord_2891163, baseEnd_2891163] using wordTrace_append hprefix tailTrace_2891163
  have hstable : (prefixWord ++ tailWord_2891163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891163).length < 2 ^ (prefixWord ++ tailWord_2891163).sum := by decide
  have hdescent : baseEnd_2891163 < baseStart_2891163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891180 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_2891180 : Nat := 118140960795 + 2891180 * 2 ^ 59
def prefixEnd_2891180 : Nat := 4983230072969 + 3 ^ 40 * 2891180 * 2
def baseEnd_2891180 : Nat := 1484564998666103478653711

theorem tailTrace_2891180 : CollatzResearch.WordTrace tailWord_2891180 prefixEnd_2891180 1484564998666103478653711 := by
  unfold tailWord_2891180
  simp only [CollatzResearch.WordTrace]
  refine ⟨52724998832878054538867497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70299998443837406051823329 52724998832878054538867497)
  ·
    refine ⟨39543749124658540904150623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52724998832878054538867497 39543749124658540904150623)
    ·
      refine ⟨59315623686987811356225935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39543749124658540904150623 59315623686987811356225935)
      ·
        refine ⟨88973435530481717034338903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59315623686987811356225935 88973435530481717034338903)
        ·
          refine ⟨133460153295722575551508355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88973435530481717034338903 133460153295722575551508355)
          ·
            refine ⟨200190229943583863327262533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133460153295722575551508355 200190229943583863327262533)
            ·
              refine ⟨37535668114421974373861725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200190229943583863327262533 37535668114421974373861725)
              ·
                refine ⟨14075875542908240390198147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37535668114421974373861725 14075875542908240390198147)
                ·
                  refine ⟨21113813314362360585297221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14075875542908240390198147 21113813314362360585297221)
                  ·
                    refine ⟨3958839996442942609743229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21113813314362360585297221 3958839996442942609743229)
                    ·
                      refine ⟨1484564998666103478653711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3958839996442942609743229 1484564998666103478653711)
                      ·
                        rfl

theorem cell23_2891180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_2891180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891180 prefixEnd_2891180 := by exact prefixLift 2891180
  have htrace : WordTrace (prefixWord ++ tailWord_2891180) baseStart_2891180 baseEnd_2891180 := by
    simpa [prefixWord, tailWord_2891180, baseEnd_2891180] using wordTrace_append hprefix tailTrace_2891180
  have hstable : (prefixWord ++ tailWord_2891180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891180).length < 2 ^ (prefixWord ++ tailWord_2891180).sum := by decide
  have hdescent : baseEnd_2891180 < baseStart_2891180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891183 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 10]
def baseStart_2891183 : Nat := 118140960795 + 2891183 * 2 ^ 59
def prefixEnd_2891183 : Nat := 4983230072969 + 3 ^ 40 * 2891183 * 2
def baseEnd_2891183 : Nat := 164951837678674107435133

theorem tailTrace_2891183 : CollatzResearch.WordTrace tailWord_2891183 prefixEnd_2891183 164951837678674107435133 := by
  unfold tailWord_2891183
  simp only [CollatzResearch.WordTrace]
  refine ⟨105450107084745240590094203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70300071389830160393396135 105450107084745240590094203)
  ·
    refine ⟨158175160627117860885141305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105450107084745240590094203 158175160627117860885141305)
    ·
      refine ⟨118631370470338395663855979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158175160627117860885141305 118631370470338395663855979)
      ·
        refine ⟨177947055705507593495783969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118631370470338395663855979 177947055705507593495783969)
        ·
          refine ⟨133460291779130695121837977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177947055705507593495783969 133460291779130695121837977)
          ·
            refine ⟨100095218834348021341378483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133460291779130695121837977 100095218834348021341378483)
            ·
              refine ⟨150142828251522032012067725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100095218834348021341378483 150142828251522032012067725)
              ·
                refine ⟨56303560594320762004525397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150142828251522032012067725 56303560594320762004525397)
                ·
                  refine ⟨164951837678674107435133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 56303560594320762004525397 164951837678674107435133)
                  ·
                    rfl

theorem cell23_2891183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 10].length) (baseStart_2891183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891183 prefixEnd_2891183 := by exact prefixLift 2891183
  have htrace : WordTrace (prefixWord ++ tailWord_2891183) baseStart_2891183 baseEnd_2891183 := by
    simpa [prefixWord, tailWord_2891183, baseEnd_2891183] using wordTrace_append hprefix tailTrace_2891183
  have hstable : (prefixWord ++ tailWord_2891183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891183).length < 2 ^ (prefixWord ++ tailWord_2891183).sum := by decide
  have hdescent : baseEnd_2891183 < baseStart_2891183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891197 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2891197 : Nat := 118140960795 + 2891197 * 2 ^ 59
def prefixEnd_2891197 : Nat := 4983230072969 + 3 ^ 40 * 2891197 * 2
def baseEnd_2891197 : Nat := 1484573727837229912141133

theorem tailTrace_2891197 : CollatzResearch.WordTrace tailWord_2891197 prefixEnd_2891197 1484573727837229912141133 := by
  unfold tailWord_2891197
  simp only [CollatzResearch.WordTrace]
  refine ⟨105450617706694520981103845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70300411804463013987402563 105450617706694520981103845)
  ·
    refine ⟨19771990820005222683956971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105450617706694520981103845 19771990820005222683956971)
    ·
      refine ⟨29657986230007834025935457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19771990820005222683956971 29657986230007834025935457)
      ·
        refine ⟨22243489672505875519451593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29657986230007834025935457 22243489672505875519451593)
        ·
          refine ⟨16682617254379406639588695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22243489672505875519451593 16682617254379406639588695)
          ·
            refine ⟨25023925881569109959383043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16682617254379406639588695 25023925881569109959383043)
            ·
              refine ⟨37535888822353664939074565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25023925881569109959383043 37535888822353664939074565)
              ·
                refine ⟨7037979154191312176076481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37535888822353664939074565 7037979154191312176076481)
                ·
                  refine ⟨5278484365643484132057361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7037979154191312176076481 5278484365643484132057361)
                  ·
                    refine ⟨3958863274232613099043021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5278484365643484132057361 3958863274232613099043021)
                    ·
                      refine ⟨1484573727837229912141133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3958863274232613099043021 1484573727837229912141133)
                      ·
                        rfl

theorem cell23_2891197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2891197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891197 prefixEnd_2891197 := by exact prefixLift 2891197
  have htrace : WordTrace (prefixWord ++ tailWord_2891197) baseStart_2891197 baseEnd_2891197 := by
    simpa [prefixWord, tailWord_2891197, baseEnd_2891197] using wordTrace_append hprefix tailTrace_2891197
  have hstable : (prefixWord ++ tailWord_2891197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891197).length < 2 ^ (prefixWord ++ tailWord_2891197).sum := by decide
  have hdescent : baseEnd_2891197 < baseStart_2891197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891200 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 6]
def baseStart_2891200 : Nat := 118140960795 + 2891200 * 2 ^ 59
def prefixEnd_2891200 : Nat := 4983230072969 + 3 ^ 40 * 2891200 * 2
def baseEnd_2891200 : Nat := 164952807586577044489291

theorem tailTrace_2891200 : CollatzResearch.WordTrace tailWord_2891200 prefixEnd_2891200 164952807586577044489291 := by
  unfold tailWord_2891200
  simp only [CollatzResearch.WordTrace]
  refine ⟨52725363562841826246731527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70300484750455768328975369 52725363562841826246731527)
  ·
    refine ⟨79088045344262739370097291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52725363562841826246731527 79088045344262739370097291)
    ·
      refine ⟨118632068016394109055145937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79088045344262739370097291 118632068016394109055145937)
      ·
        refine ⟨88974051012295581791359453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118632068016394109055145937 88974051012295581791359453)
        ·
          refine ⟨33365269129610843171759795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88974051012295581791359453 33365269129610843171759795)
          ·
            refine ⟨50047903694416264757639693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33365269129610843171759795 50047903694416264757639693)
            ·
              refine ⟨18767963885406099284114885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50047903694416264757639693 18767963885406099284114885)
              ·
                refine ⟨3518993228513643615771541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18767963885406099284114885 3518993228513643615771541)
                ·
                  refine ⟨164952807586577044489291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3518993228513643615771541 164952807586577044489291)
                  ·
                    rfl

theorem cell23_2891200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_2891200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891200 prefixEnd_2891200 := by exact prefixLift 2891200
  have htrace : WordTrace (prefixWord ++ tailWord_2891200) baseStart_2891200 baseEnd_2891200 := by
    simpa [prefixWord, tailWord_2891200, baseEnd_2891200] using wordTrace_append hprefix tailTrace_2891200
  have hstable : (prefixWord ++ tailWord_2891200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891200).length < 2 ^ (prefixWord ++ tailWord_2891200).sum := by decide
  have hdescent : baseEnd_2891200 < baseStart_2891200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891260 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_2891260 : Nat := 118140960795 + 2891260 * 2 ^ 59
def prefixEnd_2891260 : Nat := 4983230072969 + 3 ^ 40 * 2891260 * 2
def baseEnd_2891260 : Nat := 494868692372821055217781

theorem tailTrace_2891260 : CollatzResearch.WordTrace tailWord_2891260 prefixEnd_2891260 494868692372821055217781 := by
  unfold tailWord_2891260
  simp only [CollatzResearch.WordTrace]
  refine ⟨52726457752733141370323617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70301943670310855160431489 52726457752733141370323617)
  ·
    refine ⟨39544843314549856027742713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52726457752733141370323617 39544843314549856027742713)
    ·
      refine ⟨29658632485912392020807035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39544843314549856027742713 29658632485912392020807035)
      ·
        refine ⟨44487948728868588031210553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29658632485912392020807035 44487948728868588031210553)
        ·
          refine ⟨33365961546651441023407915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44487948728868588031210553 33365961546651441023407915)
          ·
            refine ⟨50048942319977161535111873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33365961546651441023407915 50048942319977161535111873)
            ·
              refine ⟨37536706739982871151333905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50048942319977161535111873 37536706739982871151333905)
              ·
                refine ⟨28152530054987153363500429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37536706739982871151333905 28152530054987153363500429)
                ·
                  refine ⟨10557198770620182511312661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28152530054987153363500429 10557198770620182511312661)
                  ·
                    refine ⟨494868692372821055217781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10557198770620182511312661 494868692372821055217781)
                    ·
                      rfl

theorem cell23_2891260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_2891260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891260 prefixEnd_2891260 := by exact prefixLift 2891260
  have htrace : WordTrace (prefixWord ++ tailWord_2891260) baseStart_2891260 baseEnd_2891260 := by
    simpa [prefixWord, tailWord_2891260, baseEnd_2891260] using wordTrace_append hprefix tailTrace_2891260
  have hstable : (prefixWord ++ tailWord_2891260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891260).length < 2 ^ (prefixWord ++ tailWord_2891260).sum := by decide
  have hdescent : baseEnd_2891260 < baseStart_2891260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891261 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_2891261 : Nat := 118140960795 + 2891261 * 2 ^ 59
def prefixEnd_2891261 : Nat := 4983230072969 + 3 ^ 40 * 2891261 * 2
def baseEnd_2891261 : Nat := 1484606590599117661740839

theorem tailTrace_2891261 : CollatzResearch.WordTrace tailWord_2891261 prefixEnd_2891261 1484606590599117661740839 := by
  unfold tailWord_2891261
  simp only [CollatzResearch.WordTrace]
  refine ⟨105452951978462659911433637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70301967985641773274289091 105452951978462659911433637)
  ·
    refine ⟨19772428495961748733393807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105452951978462659911433637 19772428495961748733393807)
    ·
      refine ⟨29658642743942623100090711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19772428495961748733393807 29658642743942623100090711)
      ·
        refine ⟨44487964115913934650136067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29658642743942623100090711 44487964115913934650136067)
        ·
          refine ⟨66731946173870901975204101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44487964115913934650136067 66731946173870901975204101)
          ·
            refine ⟨12512239907600794120350769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66731946173870901975204101 12512239907600794120350769)
            ·
              refine ⟨9384179930700595590263077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12512239907600794120350769 9384179930700595590263077)
              ·
                refine ⟨1759533737006361673174327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9384179930700595590263077 1759533737006361673174327)
                ·
                  refine ⟨2639300605509542509761491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759533737006361673174327 2639300605509542509761491)
                  ·
                    refine ⟨3958950908264313764642237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639300605509542509761491 3958950908264313764642237)
                    ·
                      refine ⟨1484606590599117661740839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3958950908264313764642237 1484606590599117661740839)
                      ·
                        rfl

theorem cell23_2891261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_2891261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891261 prefixEnd_2891261 := by exact prefixLift 2891261
  have htrace : WordTrace (prefixWord ++ tailWord_2891261) baseStart_2891261 baseEnd_2891261 := by
    simpa [prefixWord, tailWord_2891261, baseEnd_2891261] using wordTrace_append hprefix tailTrace_2891261
  have hstable : (prefixWord ++ tailWord_2891261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891261).length < 2 ^ (prefixWord ++ tailWord_2891261).sum := by decide
  have hdescent : baseEnd_2891261 < baseStart_2891261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891344 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 3, 3, 2]
def baseStart_2891344 : Nat := 118140960795 + 2891344 * 2 ^ 59
def prefixEnd_2891344 : Nat := 4983230072969 + 3 ^ 40 * 2891344 * 2
def baseEnd_2891344 : Nat := 1484649209493440837002957

theorem tailTrace_2891344 : CollatzResearch.WordTrace tailWord_2891344 prefixEnd_2891344 1484649209493440837002957 := by
  unfold tailWord_2891344
  simp only [CollatzResearch.WordTrace]
  refine ⟨52727989618580982543352543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70303986158107976724470057 52727989618580982543352543)
  ·
    refine ⟨79091984427871473815028815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52727989618580982543352543 79091984427871473815028815)
    ·
      refine ⟨118637976641807210722543223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79091984427871473815028815 118637976641807210722543223)
      ·
        refine ⟨177956964962710816083814835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118637976641807210722543223 177956964962710816083814835)
        ·
          refine ⟨266935447444066224125722253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177956964962710816083814835 266935447444066224125722253)
          ·
            refine ⟨100100792791524834047145845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266935447444066224125722253 100100792791524834047145845)
            ·
              refine ⟨9384449324205453191919923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100100792791524834047145845 9384449324205453191919923)
              ·
                refine ⟨14076673986308179787879885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9384449324205453191919923 14076673986308179787879885)
                ·
                  refine ⟨5278752744865567420454957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14076673986308179787879885 5278752744865567420454957)
                  ·
                    refine ⟨1979532279324587782670609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5278752744865567420454957 1979532279324587782670609)
                    ·
                      refine ⟨1484649209493440837002957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979532279324587782670609 1484649209493440837002957)
                      ·
                        rfl

theorem cell23_2891344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 3, 2].length) (baseStart_2891344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891344 prefixEnd_2891344 := by exact prefixLift 2891344
  have htrace : WordTrace (prefixWord ++ tailWord_2891344) baseStart_2891344 baseEnd_2891344 := by
    simpa [prefixWord, tailWord_2891344, baseEnd_2891344] using wordTrace_append hprefix tailTrace_2891344
  have hstable : (prefixWord ++ tailWord_2891344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891344).length < 2 ^ (prefixWord ++ tailWord_2891344).sum := by decide
  have hdescent : baseEnd_2891344 < baseStart_2891344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891368 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2891368 : Nat := 118140960795 + 2891368 * 2 ^ 59
def prefixEnd_2891368 : Nat := 4983230072969 + 3 ^ 40 * 2891368 * 2
def baseEnd_2891368 : Nat := 1484661533029148743102847

theorem tailTrace_2891368 : CollatzResearch.WordTrace tailWord_2891368 prefixEnd_2891368 1484661533029148743102847 := by
  unfold tailWord_2891368
  simp only [CollatzResearch.WordTrace]
  refine ⟨52728427294537508592789379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70304569726050011457052505 52728427294537508592789379)
  ·
    refine ⟨79092640941806262889184069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52728427294537508592789379 79092640941806262889184069)
    ·
      refine ⟨14829870176588674291722013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79092640941806262889184069 14829870176588674291722013)
      ·
        refine ⟨5561201316220752859395755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14829870176588674291722013 5561201316220752859395755)
        ·
          refine ⟨8341801974331129289093633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561201316220752859395755 8341801974331129289093633)
          ·
            refine ⟨6256351480748346966820225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8341801974331129289093633 6256351480748346966820225)
            ·
              refine ⟨4692263610561260225115169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6256351480748346966820225 4692263610561260225115169)
              ·
                refine ⟨3519197707920945168836377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692263610561260225115169 3519197707920945168836377)
                ·
                  refine ⟨2639398280940708876627283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519197707920945168836377 2639398280940708876627283)
                  ·
                    refine ⟨3959097421411063314940925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639398280940708876627283 3959097421411063314940925)
                    ·
                      refine ⟨1484661533029148743102847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959097421411063314940925 1484661533029148743102847)
                      ·
                        rfl

theorem cell23_2891368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2891368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891368 prefixEnd_2891368 := by exact prefixLift 2891368
  have htrace : WordTrace (prefixWord ++ tailWord_2891368) baseStart_2891368 baseEnd_2891368 := by
    simpa [prefixWord, tailWord_2891368, baseEnd_2891368] using wordTrace_append hprefix tailTrace_2891368
  have hstable : (prefixWord ++ tailWord_2891368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891368).length < 2 ^ (prefixWord ++ tailWord_2891368).sum := by decide
  have hdescent : baseEnd_2891368 < baseStart_2891368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891387 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4]
def baseStart_2891387 : Nat := 118140960795 + 2891387 * 2 ^ 59
def prefixEnd_2891387 : Nat := 4983230072969 + 3 ^ 40 * 2891387 * 2
def baseEnd_2891387 : Nat := 1484671289161584168765259

theorem tailTrace_2891387 : CollatzResearch.WordTrace tailWord_2891387 prefixEnd_2891387 1484671289161584168765259 := by
  unfold tailWord_2891387
  simp only [CollatzResearch.WordTrace]
  refine ⟨105457547576006183430520415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70305031717337455620346943 105457547576006183430520415)
  ·
    refine ⟨158186321364009275145780623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105457547576006183430520415 158186321364009275145780623)
    ·
      refine ⟨237279482046013912718670935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158186321364009275145780623 237279482046013912718670935)
      ·
        refine ⟨355919223069020869078006403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237279482046013912718670935 355919223069020869078006403)
        ·
          refine ⟨533878834603531303617009605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355919223069020869078006403 533878834603531303617009605)
          ·
            refine ⟨100102281488162119428189301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 533878834603531303617009605 100102281488162119428189301)
            ·
              refine ⟨9384588889515198696392747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100102281488162119428189301 9384588889515198696392747)
              ·
                refine ⟨14076883334272798044589121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9384588889515198696392747 14076883334272798044589121)
                ·
                  refine ⟨10557662500704598533441841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14076883334272798044589121 10557662500704598533441841)
                  ·
                    refine ⟨7918246875528448900081381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10557662500704598533441841 7918246875528448900081381)
                    ·
                      refine ⟨1484671289161584168765259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7918246875528448900081381 1484671289161584168765259)
                      ·
                        rfl

theorem cell23_2891387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_2891387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891387 prefixEnd_2891387 := by exact prefixLift 2891387
  have htrace : WordTrace (prefixWord ++ tailWord_2891387) baseStart_2891387 baseEnd_2891387 := by
    simpa [prefixWord, tailWord_2891387, baseEnd_2891387] using wordTrace_append hprefix tailTrace_2891387
  have hstable : (prefixWord ++ tailWord_2891387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891387).length < 2 ^ (prefixWord ++ tailWord_2891387).sum := by decide
  have hdescent : baseEnd_2891387 < baseStart_2891387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891397 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 7]
def baseStart_2891397 : Nat := 118140960795 + 2891397 * 2 ^ 59
def prefixEnd_2891397 : Nat := 4983230072969 + 3 ^ 40 * 2891397 * 2
def baseEnd_2891397 : Nat := 164964047107569903293357

theorem tailTrace_2891397 : CollatzResearch.WordTrace tailWord_2891397 prefixEnd_2891397 164964047107569903293357 := by
  unfold tailWord_2891397
  simp only [CollatzResearch.WordTrace]
  refine ⟨105457912305969955138384445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70305274870646636758922963 105457912305969955138384445)
  ·
    refine ⟨39546717114738733176894167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105457912305969955138384445 39546717114738733176894167)
    ·
      refine ⟨59320075672108099765341251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39546717114738733176894167 59320075672108099765341251)
      ·
        refine ⟨88980113508162149648011877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59320075672108099765341251 88980113508162149648011877)
        ·
          refine ⟨16683771282780403059002227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88980113508162149648011877 16683771282780403059002227)
          ·
            refine ⟨25025656924170604588503341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16683771282780403059002227 25025656924170604588503341)
            ·
              refine ⟨9384621346563976720688753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25025656924170604588503341 9384621346563976720688753)
              ·
                refine ⟨7038466009922982540516565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9384621346563976720688753 7038466009922982540516565)
                ·
                  refine ⟨164964047107569903293357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7038466009922982540516565 164964047107569903293357)
                  ·
                    rfl

theorem cell23_2891397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_2891397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891397 prefixEnd_2891397 := by exact prefixLift 2891397
  have htrace : WordTrace (prefixWord ++ tailWord_2891397) baseStart_2891397 baseEnd_2891397 := by
    simpa [prefixWord, tailWord_2891397, baseEnd_2891397] using wordTrace_append hprefix tailTrace_2891397
  have hstable : (prefixWord ++ tailWord_2891397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891397).length < 2 ^ (prefixWord ++ tailWord_2891397).sum := by decide
  have hdescent : baseEnd_2891397 < baseStart_2891397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891407 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_2891407 : Nat := 118140960795 + 2891407 * 2 ^ 59
def prefixEnd_2891407 : Nat := 4983230072969 + 3 ^ 40 * 2891407 * 2
def baseEnd_2891407 : Nat := 1484681558774674090515167

theorem tailTrace_2891407 : CollatzResearch.WordTrace tailWord_2891407 prefixEnd_2891407 1484681558774674090515167 := by
  unfold tailWord_2891407
  simp only [CollatzResearch.WordTrace]
  refine ⟨105458277035933726846248475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70305518023955817897498983 105458277035933726846248475)
  ·
    refine ⟨158187415553900590269372713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105458277035933726846248475 158187415553900590269372713)
    ·
      refine ⟨118640561665425442702029535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158187415553900590269372713 118640561665425442702029535)
      ·
        refine ⟨177960842498138164053044303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118640561665425442702029535 177960842498138164053044303)
        ·
          refine ⟨266941263747207246079566455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177960842498138164053044303 266941263747207246079566455)
          ·
            refine ⟨400411895620810869119349683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266941263747207246079566455 400411895620810869119349683)
            ·
              refine ⟨600617843431216303679024525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400411895620810869119349683 600617843431216303679024525)
              ·
                refine ⟨225231691286706113879634197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 600617843431216303679024525 225231691286706113879634197)
                ·
                  refine ⟨10557735529064349088107853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225231691286706113879634197 10557735529064349088107853)
                  ·
                    refine ⟨3959150823399130908040445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10557735529064349088107853 3959150823399130908040445)
                    ·
                      refine ⟨1484681558774674090515167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959150823399130908040445 1484681558774674090515167)
                      ·
                        rfl

theorem cell23_2891407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_2891407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891407 prefixEnd_2891407 := by exact prefixLift 2891407
  have htrace : WordTrace (prefixWord ++ tailWord_2891407) baseStart_2891407 baseEnd_2891407 := by
    simpa [prefixWord, tailWord_2891407, baseEnd_2891407] using wordTrace_append hprefix tailTrace_2891407
  have hstable : (prefixWord ++ tailWord_2891407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891407).length < 2 ^ (prefixWord ++ tailWord_2891407).sum := by decide
  have hdescent : baseEnd_2891407 < baseStart_2891407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891412 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2891412 : Nat := 118140960795 + 2891412 * 2 ^ 59
def prefixEnd_2891412 : Nat := 4983230072969 + 3 ^ 40 * 2891412 * 2
def baseEnd_2891412 : Nat := 1484684126177946570952645

theorem tailTrace_2891412 : CollatzResearch.WordTrace tailWord_2891412 prefixEnd_2891412 1484684126177946570952645 := by
  unfold tailWord_2891412
  simp only [CollatzResearch.WordTrace]
  refine ⟨52729229700457806350090245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70305639600610408466786993 52729229700457806350090245)
  ·
    refine ⟨9886730568835838690641921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52729229700457806350090245 9886730568835838690641921)
    ·
      refine ⟨7415047926626879017981441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9886730568835838690641921 7415047926626879017981441)
      ·
        refine ⟨5561285944970159263486081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7415047926626879017981441 5561285944970159263486081)
        ·
          refine ⟨4170964458727619447614561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5561285944970159263486081 4170964458727619447614561)
          ·
            refine ⟨3128223344045714585710921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4170964458727619447614561 3128223344045714585710921)
            ·
              refine ⟨2346167508034285939283191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3128223344045714585710921 2346167508034285939283191)
              ·
                refine ⟨3519251262051428908924787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346167508034285939283191 3519251262051428908924787)
                ·
                  refine ⟨5278876893077143363387181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519251262051428908924787 5278876893077143363387181)
                  ·
                    refine ⟨1979578834903928761270193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5278876893077143363387181 1979578834903928761270193)
                    ·
                      refine ⟨1484684126177946570952645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979578834903928761270193 1484684126177946570952645)
                      ·
                        rfl

theorem cell23_2891412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2891412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891412 prefixEnd_2891412 := by exact prefixLift 2891412
  have htrace : WordTrace (prefixWord ++ tailWord_2891412) baseStart_2891412 baseEnd_2891412 := by
    simpa [prefixWord, tailWord_2891412, baseEnd_2891412] using wordTrace_append hprefix tailTrace_2891412
  have hstable : (prefixWord ++ tailWord_2891412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891412).length < 2 ^ (prefixWord ++ tailWord_2891412).sum := by decide
  have hdescent : baseEnd_2891412 < baseStart_2891412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891424 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_2891424 : Nat := 118140960795 + 2891424 * 2 ^ 59
def prefixEnd_2891424 : Nat := 4983230072969 + 3 ^ 40 * 2891424 * 2
def baseEnd_2891424 : Nat := 1484690287945800524002589

theorem tailTrace_2891424 : CollatzResearch.WordTrace tailWord_2891424 prefixEnd_2891424 1484690287945800524002589 := by
  unfold tailWord_2891424
  simp only [CollatzResearch.WordTrace]
  refine ⟨52729448538436069374808663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70305931384581425833078217 52729448538436069374808663)
  ·
    refine ⟨79094172807654104062212995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52729448538436069374808663 79094172807654104062212995)
    ·
      refine ⟨118641259211481156093319493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79094172807654104062212995 118641259211481156093319493)
      ·
        refine ⟨22245236102152716767497405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118641259211481156093319493 22245236102152716767497405)
        ·
          refine ⟨8341963538307268787811527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22245236102152716767497405 8341963538307268787811527)
          ·
            refine ⟨12512945307460903181717291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341963538307268787811527 12512945307460903181717291)
            ·
              refine ⟨18769417961191354772575937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12512945307460903181717291 18769417961191354772575937)
              ·
                refine ⟨14077063470893516079431953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18769417961191354772575937 14077063470893516079431953)
                ·
                  refine ⟨10557797603170137059573965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14077063470893516079431953 10557797603170137059573965)
                  ·
                    refine ⟨3959174101188801397340237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10557797603170137059573965 3959174101188801397340237)
                    ·
                      refine ⟨1484690287945800524002589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959174101188801397340237 1484690287945800524002589)
                      ·
                        rfl

theorem cell23_2891424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_2891424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891424 prefixEnd_2891424 := by exact prefixLift 2891424
  have htrace : WordTrace (prefixWord ++ tailWord_2891424) baseStart_2891424 baseEnd_2891424 := by
    simpa [prefixWord, tailWord_2891424, baseEnd_2891424] using wordTrace_append hprefix tailTrace_2891424
  have hstable : (prefixWord ++ tailWord_2891424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891424).length < 2 ^ (prefixWord ++ tailWord_2891424).sum := by decide
  have hdescent : baseEnd_2891424 < baseStart_2891424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891425 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2891425 : Nat := 118140960795 + 2891425 * 2 ^ 59
def prefixEnd_2891425 : Nat := 4983230072969 + 3 ^ 40 * 2891425 * 2
def baseEnd_2891425 : Nat := 1484690801426455020090085

theorem tailTrace_2891425 : CollatzResearch.WordTrace tailWord_2891425 prefixEnd_2891425 1484690801426455020090085 := by
  unfold tailWord_2891425
  simp only [CollatzResearch.WordTrace]
  refine ⟨105458933549868515920403729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70305955699912343946935819 105458933549868515920403729)
  ·
    refine ⟨79094200162401386940302797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105458933549868515920403729 79094200162401386940302797)
    ·
      refine ⟨29660325060900520102613549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79094200162401386940302797 29660325060900520102613549)
      ·
        refine ⟨11122621897837695038480081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29660325060900520102613549 11122621897837695038480081)
        ·
          refine ⟨8341966423378271278860061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11122621897837695038480081 8341966423378271278860061)
          ·
            refine ⟨3128237408766851729572523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8341966423378271278860061 3128237408766851729572523)
            ·
              refine ⟨4692356113150277594358785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128237408766851729572523 4692356113150277594358785)
              ·
                refine ⟨3519267084862708195769089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692356113150277594358785 3519267084862708195769089)
                ·
                  refine ⟨2639450313647031146826817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519267084862708195769089 2639450313647031146826817)
                  ·
                    refine ⟨1979587735235273360120113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2639450313647031146826817 1979587735235273360120113)
                    ·
                      refine ⟨1484690801426455020090085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979587735235273360120113 1484690801426455020090085)
                      ·
                        rfl

theorem cell23_2891425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2891425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891425 prefixEnd_2891425 := by exact prefixLift 2891425
  have htrace : WordTrace (prefixWord ++ tailWord_2891425) baseStart_2891425 baseEnd_2891425 := by
    simpa [prefixWord, tailWord_2891425, baseEnd_2891425] using wordTrace_append hprefix tailTrace_2891425
  have hstable : (prefixWord ++ tailWord_2891425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891425).length < 2 ^ (prefixWord ++ tailWord_2891425).sum := by decide
  have hdescent : baseEnd_2891425 < baseStart_2891425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891427 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 4, 5]
def baseStart_2891427 : Nat := 118140960795 + 2891427 * 2 ^ 59
def prefixEnd_2891427 : Nat := 4983230072969 + 3 ^ 40 * 2891427 * 2
def baseEnd_2891427 : Nat := 494897276129254670755025

theorem tailTrace_2891427 : CollatzResearch.WordTrace tailWord_2891427 prefixEnd_2891427 494897276129254670755025 := by
  unfold tailWord_2891427
  simp only [CollatzResearch.WordTrace]
  refine ⟨105459006495861270261976535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70306004330574180174651023 105459006495861270261976535)
  ·
    refine ⟨158188509743791905392964803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105459006495861270261976535 158188509743791905392964803)
    ·
      refine ⟨237282764615687858089447205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158188509743791905392964803 237282764615687858089447205)
      ·
        refine ⟨44490518365441473391771351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237282764615687858089447205 44490518365441473391771351)
        ·
          refine ⟨66735777548162210087657027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44490518365441473391771351 66735777548162210087657027)
          ·
            refine ⟨100103666322243315131485541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66735777548162210087657027 100103666322243315131485541)
            ·
              refine ⟨18769437435420621587153539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100103666322243315131485541 18769437435420621587153539)
              ·
                refine ⟨28154156153130932380730309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18769437435420621587153539 28154156153130932380730309)
                ·
                  refine ⟨5278904278712049821386933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28154156153130932380730309 5278904278712049821386933)
                  ·
                    refine ⟨494897276129254670755025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5278904278712049821386933 494897276129254670755025)
                    ·
                      rfl

theorem cell23_2891427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 5].length) (baseStart_2891427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891427 prefixEnd_2891427 := by exact prefixLift 2891427
  have htrace : WordTrace (prefixWord ++ tailWord_2891427) baseStart_2891427 baseEnd_2891427 := by
    simpa [prefixWord, tailWord_2891427, baseEnd_2891427] using wordTrace_append hprefix tailTrace_2891427
  have hstable : (prefixWord ++ tailWord_2891427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891427).length < 2 ^ (prefixWord ++ tailWord_2891427).sum := by decide
  have hdescent : baseEnd_2891427 < baseStart_2891427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891464 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_2891464 : Nat := 118140960795 + 2891464 * 2 ^ 59
def prefixEnd_2891464 : Nat := 4983230072969 + 3 ^ 40 * 2891464 * 2
def baseEnd_2891464 : Nat := 1484710827171980367502405

theorem tailTrace_2891464 : CollatzResearch.WordTrace tailWord_2891464 prefixEnd_2891464 1484710827171980367502405 := by
  unfold tailWord_2891464
  simp only [CollatzResearch.WordTrace]
  refine ⟨52730177998363612790536723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70306903997818150387382297 52730177998363612790536723)
  ·
    refine ⟨79095266997545419185805085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52730177998363612790536723 79095266997545419185805085)
    ·
      refine ⟨29660725124079532194676907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79095266997545419185805085 29660725124079532194676907)
      ·
        refine ⟨44491087686119298292015361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29660725124079532194676907 44491087686119298292015361)
        ·
          refine ⟨33368315764589473719011521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44491087686119298292015361 33368315764589473719011521)
          ·
            refine ⟨25026236823442105289258641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33368315764589473719011521 25026236823442105289258641)
            ·
              refine ⟨18769677617581578966943981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25026236823442105289258641 18769677617581578966943981)
              ·
                refine ⟨7038629106593092112603993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18769677617581578966943981 7038629106593092112603993)
                ·
                  refine ⟨5278971829944819084452995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7038629106593092112603993 5278971829944819084452995)
                  ·
                    refine ⟨7918457744917228626679493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278971829944819084452995 7918457744917228626679493)
                    ·
                      refine ⟨1484710827171980367502405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7918457744917228626679493 1484710827171980367502405)
                      ·
                        rfl

theorem cell23_2891464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_2891464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891464 prefixEnd_2891464 := by exact prefixLift 2891464
  have htrace : WordTrace (prefixWord ++ tailWord_2891464) baseStart_2891464 baseEnd_2891464 := by
    simpa [prefixWord, tailWord_2891464, baseEnd_2891464] using wordTrace_append hprefix tailTrace_2891464
  have hstable : (prefixWord ++ tailWord_2891464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891464).length < 2 ^ (prefixWord ++ tailWord_2891464).sum := by decide
  have hdescent : baseEnd_2891464 < baseStart_2891464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891487 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 8]
def baseStart_2891487 : Nat := 118140960795 + 2891487 * 2 ^ 59
def prefixEnd_2891487 : Nat := 4983230072969 + 3 ^ 40 * 2891487 * 2
def baseEnd_2891487 : Nat := 164969181914114864168311

theorem tailTrace_2891487 : CollatzResearch.WordTrace tailWord_2891487 prefixEnd_2891487 164969181914114864168311 := by
  unfold tailWord_2891487
  simp only [CollatzResearch.WordTrace]
  refine ⟨105461194875643900509160715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70307463250429267006107143 105461194875643900509160715)
  ·
    refine ⟨158191792313465850763741073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105461194875643900509160715 158191792313465850763741073)
    ·
      refine ⟨118643844235099388072805805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158191792313465850763741073 118643844235099388072805805)
      ·
        refine ⟨44491441588162270527302177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118643844235099388072805805 44491441588162270527302177)
        ·
          refine ⟨33368581191121702895476633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44491441588162270527302177 33368581191121702895476633)
          ·
            refine ⟨25026435893341277171607475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33368581191121702895476633 25026435893341277171607475)
            ·
              refine ⟨37539653840011915757411213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25026435893341277171607475 37539653840011915757411213)
              ·
                refine ⟨14077370190004468409029205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37539653840011915757411213 14077370190004468409029205)
                ·
                  refine ⟨164969181914114864168311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14077370190004468409029205 164969181914114864168311)
                  ·
                    rfl

theorem cell23_2891487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 8].length) (baseStart_2891487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891487 prefixEnd_2891487 := by exact prefixLift 2891487
  have htrace : WordTrace (prefixWord ++ tailWord_2891487) baseStart_2891487 baseEnd_2891487 := by
    simpa [prefixWord, tailWord_2891487, baseEnd_2891487] using wordTrace_append hprefix tailTrace_2891487
  have hstable : (prefixWord ++ tailWord_2891487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891487).length < 2 ^ (prefixWord ++ tailWord_2891487).sum := by decide
  have hdescent : baseEnd_2891487 < baseStart_2891487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891507 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_2891507 : Nat := 118140960795 + 2891507 * 2 ^ 59
def prefixEnd_2891507 : Nat := 4983230072969 + 3 ^ 40 * 2891507 * 2
def baseEnd_2891507 : Nat := 1484732906840123699264707

theorem tailTrace_2891507 : CollatzResearch.WordTrace tailWord_2891507 prefixEnd_2891507 1484732906840123699264707 := by
  unfold tailWord_2891507
  simp only [CollatzResearch.WordTrace]
  refine ⟨105461924335571443924888775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70307949557047629283259183 105461924335571443924888775)
  ·
    refine ⟨158192886503357165887333163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105461924335571443924888775 158192886503357165887333163)
    ·
      refine ⟨237289329755035748830999745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158192886503357165887333163 237289329755035748830999745)
      ·
        refine ⟨177966997316276811623249809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237289329755035748830999745 177966997316276811623249809)
        ·
          refine ⟨133475247987207608717437357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177966997316276811623249809 133475247987207608717437357)
          ·
            refine ⟨50053217995202853269039009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133475247987207608717437357 50053217995202853269039009)
            ·
              refine ⟨37539913496402139951779257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50053217995202853269039009 37539913496402139951779257)
              ·
                refine ⟨28154935122301604963834443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37539913496402139951779257 28154935122301604963834443)
                ·
                  refine ⟨42232402683452407445751665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28154935122301604963834443 42232402683452407445751665)
                  ·
                    refine ⟨31674302012589305584313749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42232402683452407445751665 31674302012589305584313749)
                    ·
                      refine ⟨1484732906840123699264707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31674302012589305584313749 1484732906840123699264707)
                      ·
                        rfl

theorem cell23_2891507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_2891507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891507 prefixEnd_2891507 := by exact prefixLift 2891507
  have htrace : WordTrace (prefixWord ++ tailWord_2891507) baseStart_2891507 baseEnd_2891507 := by
    simpa [prefixWord, tailWord_2891507, baseEnd_2891507] using wordTrace_append hprefix tailTrace_2891507
  have hstable : (prefixWord ++ tailWord_2891507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891507).length < 2 ^ (prefixWord ++ tailWord_2891507).sum := by decide
  have hdescent : baseEnd_2891507 < baseStart_2891507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891538 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_2891538 : Nat := 118140960795 + 2891538 * 2 ^ 59
def prefixEnd_2891538 : Nat := 4983230072969 + 3 ^ 40 * 2891538 * 2
def baseEnd_2891538 : Nat := 164972091637823675330785

theorem tailTrace_2891538 : CollatzResearch.WordTrace tailWord_2891538 prefixEnd_2891538 164972091637823675330785 := by
  unfold tailWord_2891538
  simp only [CollatzResearch.WordTrace]
  refine ⟨26365763749614784054816817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70308703332306090812844845 26365763749614784054816817)
  ·
    refine ⟨19774322812211088041112613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26365763749614784054816817 19774322812211088041112613)
    ·
      refine ⟨3707685527289579007708615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19774322812211088041112613 3707685527289579007708615)
      ·
        refine ⟨5561528290934368511562923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707685527289579007708615 5561528290934368511562923)
        ·
          refine ⟨8342292436401552767344385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561528290934368511562923 8342292436401552767344385)
          ·
            refine ⟨6256719327301164575508289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342292436401552767344385 6256719327301164575508289)
            ·
              refine ⟨4692539495475873431631217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6256719327301164575508289 4692539495475873431631217)
              ·
                refine ⟨3519404621606905073723413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692539495475873431631217 3519404621606905073723413)
                ·
                  refine ⟨164972091637823675330785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3519404621606905073723413 164972091637823675330785)
                  ·
                    rfl

theorem cell23_2891538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_2891538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891538 prefixEnd_2891538 := by exact prefixLift 2891538
  have htrace : WordTrace (prefixWord ++ tailWord_2891538) baseStart_2891538 baseEnd_2891538 := by
    simpa [prefixWord, tailWord_2891538, baseEnd_2891538] using wordTrace_append hprefix tailTrace_2891538
  have hstable : (prefixWord ++ tailWord_2891538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891538).length < 2 ^ (prefixWord ++ tailWord_2891538).sum := by decide
  have hdescent : baseEnd_2891538 < baseStart_2891538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891564 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_2891564 : Nat := 118140960795 + 2891564 * 2 ^ 59
def prefixEnd_2891564 : Nat := 4983230072969 + 3 ^ 40 * 2891564 * 2
def baseEnd_2891564 : Nat := 494920725079143325417315

theorem tailTrace_2891564 : CollatzResearch.WordTrace tailWord_2891564 prefixEnd_2891564 494920725079143325417315 := by
  unfold tailWord_2891564
  simp only [CollatzResearch.WordTrace]
  refine ⟨52732001648182471329856873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70309335530909961773142497 52732001648182471329856873)
  ·
    refine ⟨39549001236136853497392655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52732001648182471329856873 39549001236136853497392655)
    ·
      refine ⟨59323501854205280246088983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39549001236136853497392655 59323501854205280246088983)
      ·
        refine ⟨88985252781307920369133475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59323501854205280246088983 88985252781307920369133475)
        ·
          refine ⟨133477879171961880553700213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88985252781307920369133475 133477879171961880553700213)
          ·
            refine ⟨12513551172371426301909395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133477879171961880553700213 12513551172371426301909395)
            ·
              refine ⟨18770326758557139452864093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12513551172371426301909395 18770326758557139452864093)
              ·
                refine ⟨7038872534458927294824035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18770326758557139452864093 7038872534458927294824035)
                ·
                  refine ⟨10558308801688390942236053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7038872534458927294824035 10558308801688390942236053)
                  ·
                    refine ⟨494920725079143325417315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10558308801688390942236053 494920725079143325417315)
                    ·
                      rfl

theorem cell23_2891564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_2891564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891564 prefixEnd_2891564 := by exact prefixLift 2891564
  have htrace : WordTrace (prefixWord ++ tailWord_2891564) baseStart_2891564 baseEnd_2891564 := by
    simpa [prefixWord, tailWord_2891564, baseEnd_2891564] using wordTrace_append hprefix tailTrace_2891564
  have hstable : (prefixWord ++ tailWord_2891564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891564).length < 2 ^ (prefixWord ++ tailWord_2891564).sum := by decide
  have hdescent : baseEnd_2891564 < baseStart_2891564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891581 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_2891581 : Nat := 118140960795 + 2891581 * 2 ^ 59
def prefixEnd_2891581 : Nat := 4983230072969 + 3 ^ 40 * 2891581 * 2
def baseEnd_2891581 : Nat := 494923634802852136579789

theorem tailTrace_2891581 : CollatzResearch.WordTrace tailWord_2891581 prefixEnd_2891581 494923634802852136579789 := by
  unfold tailWord_2891581
  simp only [CollatzResearch.WordTrace]
  refine ⟨105464623337303354563082597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70309748891535569708721731 105464623337303354563082597)
  ·
    refine ⟨19774616875744378980577987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105464623337303354563082597 19774616875744378980577987)
    ·
      refine ⟨29661925313616568470866981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19774616875744378980577987 29661925313616568470866981)
      ·
        refine ⟨5561610996303106588287559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29661925313616568470866981 5561610996303106588287559)
        ·
          refine ⟨8342416494454659882431339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561610996303106588287559 8342416494454659882431339)
          ·
            refine ⟨12513624741681989823647009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8342416494454659882431339 12513624741681989823647009)
            ·
              refine ⟨9385218556261492367735257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12513624741681989823647009 9385218556261492367735257)
              ·
                refine ⟨7038913917196119275801443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9385218556261492367735257 7038913917196119275801443)
                ·
                  refine ⟨10558370875794178913702165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7038913917196119275801443 10558370875794178913702165)
                  ·
                    refine ⟨494923634802852136579789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10558370875794178913702165 494923634802852136579789)
                    ·
                      rfl

theorem cell23_2891581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_2891581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891581 prefixEnd_2891581 := by exact prefixLift 2891581
  have htrace : WordTrace (prefixWord ++ tailWord_2891581) baseStart_2891581 baseEnd_2891581 := by
    simpa [prefixWord, tailWord_2891581, baseEnd_2891581] using wordTrace_append hprefix tailTrace_2891581
  have hstable : (prefixWord ++ tailWord_2891581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891581).length < 2 ^ (prefixWord ++ tailWord_2891581).sum := by decide
  have hdescent : baseEnd_2891581 < baseStart_2891581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891582 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_2891582 : Nat := 118140960795 + 2891582 * 2 ^ 59
def prefixEnd_2891582 : Nat := 4983230072969 + 3 ^ 40 * 2891582 * 2
def baseEnd_2891582 : Nat := 1484771417889210905826863

theorem tailTrace_2891582 : CollatzResearch.WordTrace tailWord_2891582 prefixEnd_2891582 1484771417889210905826863 := by
  unfold tailWord_2891582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183082476287466466733625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70309773206866487822579333 13183082476287466466733625)
  ·
    refine ⟨9887311857215599850050219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13183082476287466466733625 9887311857215599850050219)
    ·
      refine ⟨14830967785823399775075329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887311857215599850050219 14830967785823399775075329)
      ·
        refine ⟨11123225839367549831306497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14830967785823399775075329 11123225839367549831306497)
        ·
          refine ⟨8342419379525662373479873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11123225839367549831306497 8342419379525662373479873)
          ·
            refine ⟨6256814534644246780109905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342419379525662373479873 6256814534644246780109905)
            ·
              refine ⟨4692610900983185085082429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6256814534644246780109905 4692610900983185085082429)
              ·
                refine ⟨1759729087868694406905911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4692610900983185085082429 1759729087868694406905911)
                ·
                  refine ⟨2639593631803041610358867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759729087868694406905911 2639593631803041610358867)
                  ·
                    refine ⟨3959390447704562415538301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639593631803041610358867 3959390447704562415538301)
                    ·
                      refine ⟨1484771417889210905826863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959390447704562415538301 1484771417889210905826863)
                      ·
                        rfl

theorem cell23_2891582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_2891582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891582 prefixEnd_2891582 := by exact prefixLift 2891582
  have htrace : WordTrace (prefixWord ++ tailWord_2891582) baseStart_2891582 baseEnd_2891582 := by
    simpa [prefixWord, tailWord_2891582, baseEnd_2891582] using wordTrace_append hprefix tailTrace_2891582
  have hstable : (prefixWord ++ tailWord_2891582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891582).length < 2 ^ (prefixWord ++ tailWord_2891582).sum := by decide
  have hdescent : baseEnd_2891582 < baseStart_2891582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891605 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2891605 : Nat := 118140960795 + 2891605 * 2 ^ 59
def prefixEnd_2891605 : Nat := 4983230072969 + 3 ^ 40 * 2891605 * 2
def baseEnd_2891605 : Nat := 1484783227944264315839257

theorem tailTrace_2891605 : CollatzResearch.WordTrace tailWord_2891605 prefixEnd_2891605 1484783227944264315839257 := by
  unfold tailWord_2891605
  simp only [CollatzResearch.WordTrace]
  refine ⟨105465498689216406661956269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70310332459477604441304179 105465498689216406661956269)
  ·
    refine ⟨39549562008456152498233601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105465498689216406661956269 39549562008456152498233601)
    ·
      refine ⟨29662171506342114373675201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39549562008456152498233601 29662171506342114373675201)
      ·
        refine ⟨22246628629756585780256401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29662171506342114373675201 22246628629756585780256401)
        ·
          refine ⟨16684971472317439335192301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22246628629756585780256401 16684971472317439335192301)
          ·
            refine ⟨6256864302119039750697113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16684971472317439335192301 6256864302119039750697113)
            ·
              refine ⟨4692648226589279813022835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6256864302119039750697113 4692648226589279813022835)
              ·
                refine ⟨7038972339883919719534253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692648226589279813022835 7038972339883919719534253)
                ·
                  refine ⟨2639614627456469894825345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7038972339883919719534253 2639614627456469894825345)
                  ·
                    refine ⟨1979710970592352421119009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2639614627456469894825345 1979710970592352421119009)
                    ·
                      refine ⟨1484783227944264315839257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979710970592352421119009 1484783227944264315839257)
                      ·
                        rfl

theorem cell23_2891605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2891605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891605 prefixEnd_2891605 := by exact prefixLift 2891605
  have htrace : WordTrace (prefixWord ++ tailWord_2891605) baseStart_2891605 baseEnd_2891605 := by
    simpa [prefixWord, tailWord_2891605, baseEnd_2891605] using wordTrace_append hprefix tailTrace_2891605
  have hstable : (prefixWord ++ tailWord_2891605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891605).length < 2 ^ (prefixWord ++ tailWord_2891605).sum := by decide
  have hdescent : baseEnd_2891605 < baseStart_2891605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891618 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2891618 : Nat := 118140960795 + 2891618 * 2 ^ 59
def prefixEnd_2891618 : Nat := 4983230072969 + 3 ^ 40 * 2891618 * 2
def baseEnd_2891618 : Nat := 1484789903192772764976697

theorem tailTrace_2891618 : CollatzResearch.WordTrace tailWord_2891618 prefixEnd_2891618 1484789903192772764976697 := by
  unfold tailWord_2891618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26366493209542327470544877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70310648558779539921453005 26366493209542327470544877)
  ·
    refine ⟨9887434953578372801454329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26366493209542327470544877 9887434953578372801454329)
    ·
      refine ⟨7415576215183779601090747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9887434953578372801454329 7415576215183779601090747)
      ·
        refine ⟨11123364322775669401636121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415576215183779601090747 11123364322775669401636121)
        ·
          refine ⟨8342523242081752051227091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11123364322775669401636121 8342523242081752051227091)
          ·
            refine ⟨12513784863122628076840637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8342523242081752051227091 12513784863122628076840637)
            ·
              refine ⟨4692669323670985528815239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12513784863122628076840637 4692669323670985528815239)
              ·
                refine ⟨7039003985506478293222859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692669323670985528815239 7039003985506478293222859)
                ·
                  refine ⟨10558505978259717439834289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7039003985506478293222859 10558505978259717439834289)
                  ·
                    refine ⟨7918879483694788079875717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10558505978259717439834289 7918879483694788079875717)
                    ·
                      refine ⟨1484789903192772764976697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7918879483694788079875717 1484789903192772764976697)
                      ·
                        rfl

theorem cell23_2891618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2891618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891618 prefixEnd_2891618 := by exact prefixLift 2891618
  have htrace : WordTrace (prefixWord ++ tailWord_2891618) baseStart_2891618 baseEnd_2891618 := by
    simpa [prefixWord, tailWord_2891618, baseEnd_2891618] using wordTrace_append hprefix tailTrace_2891618
  have hstable : (prefixWord ++ tailWord_2891618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891618).length < 2 ^ (prefixWord ++ tailWord_2891618).sum := by decide
  have hdescent : baseEnd_2891618 < baseStart_2891618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891644 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2891644 : Nat := 118140960795 + 2891644 * 2 ^ 59
def prefixEnd_2891644 : Nat := 4983230072969 + 3 ^ 40 * 2891644 * 2
def baseEnd_2891644 : Nat := 1484803253689789663251577

theorem tailTrace_2891644 : CollatzResearch.WordTrace tailWord_2891644 prefixEnd_2891644 1484803253689789663251577 := by
  unfold tailWord_2891644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52733460568037558161312993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70311280757383410881750657 52733460568037558161312993)
  ·
    refine ⟨39550095426028168620984745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52733460568037558161312993 39550095426028168620984745)
    ·
      refine ⟨29662571569521126465738559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39550095426028168620984745 29662571569521126465738559)
      ·
        refine ⟨44493857354281689698607839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29662571569521126465738559 44493857354281689698607839)
        ·
          refine ⟨66740786031422534547911759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44493857354281689698607839 66740786031422534547911759)
          ·
            refine ⟨100111179047133801821867639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66740786031422534547911759 100111179047133801821867639)
            ·
              refine ⟨150166768570700702732801459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100111179047133801821867639 150166768570700702732801459)
              ·
                refine ⟨225250152856051054099202189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150166768570700702732801459 225250152856051054099202189)
                ·
                  refine ⟨84468807321019145287200821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225250152856051054099202189 84468807321019145287200821)
                  ·
                    refine ⟨7918950686345544870675077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84468807321019145287200821 7918950686345544870675077)
                    ·
                      refine ⟨1484803253689789663251577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7918950686345544870675077 1484803253689789663251577)
                      ·
                        rfl

theorem cell23_2891644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2891644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891644 prefixEnd_2891644 := by exact prefixLift 2891644
  have htrace : WordTrace (prefixWord ++ tailWord_2891644) baseStart_2891644 baseEnd_2891644 := by
    simpa [prefixWord, tailWord_2891644, baseEnd_2891644] using wordTrace_append hprefix tailTrace_2891644
  have hstable : (prefixWord ++ tailWord_2891644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891644).length < 2 ^ (prefixWord ++ tailWord_2891644).sum := by decide
  have hdescent : baseEnd_2891644 < baseStart_2891644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891648 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 1, 3, 2]
def baseStart_2891648 : Nat := 118140960795 + 2891648 * 2 ^ 59
def prefixEnd_2891648 : Nat := 4983230072969 + 3 ^ 40 * 2891648 * 2
def baseEnd_2891648 : Nat := 1484805307612407647601559

theorem tailTrace_2891648 : CollatzResearch.WordTrace tailWord_2891648 prefixEnd_2891648 1484805307612407647601559 := by
  unfold tailWord_2891648
  simp only [CollatzResearch.WordTrace]
  refine ⟨52733533514030312502885799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70311378018707083337181065 52733533514030312502885799)
  ·
    refine ⟨79100300271045468754328699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52733533514030312502885799 79100300271045468754328699)
    ·
      refine ⟨118650450406568203131493049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79100300271045468754328699 118650450406568203131493049)
      ·
        refine ⟨88987837804926152348619787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118650450406568203131493049 88987837804926152348619787)
        ·
          refine ⟨133481756707389228522929681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88987837804926152348619787 133481756707389228522929681)
          ·
            refine ⟨100111317530541921392197261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133481756707389228522929681 100111317530541921392197261)
            ·
              refine ⟨37541744073953220522073973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100111317530541921392197261 37541744073953220522073973)
              ·
                refine ⟨3519538506933114423944435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37541744073953220522073973 3519538506933114423944435)
                ·
                  refine ⟨5279307760399671635916653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519538506933114423944435 5279307760399671635916653)
                  ·
                    refine ⟨1979740410149876863468745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5279307760399671635916653 1979740410149876863468745)
                    ·
                      refine ⟨1484805307612407647601559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979740410149876863468745 1484805307612407647601559)
                      ·
                        rfl

theorem cell23_2891648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_2891648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891648 prefixEnd_2891648 := by exact prefixLift 2891648
  have htrace : WordTrace (prefixWord ++ tailWord_2891648) baseStart_2891648 baseEnd_2891648 := by
    simpa [prefixWord, tailWord_2891648, baseEnd_2891648] using wordTrace_append hprefix tailTrace_2891648
  have hstable : (prefixWord ++ tailWord_2891648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891648).length < 2 ^ (prefixWord ++ tailWord_2891648).sum := by decide
  have hdescent : baseEnd_2891648 < baseStart_2891648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891664 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_2891664 : Nat := 118140960795 + 2891664 * 2 ^ 59
def prefixEnd_2891664 : Nat := 4983230072969 + 3 ^ 40 * 2891664 * 2
def baseEnd_2891664 : Nat := 1484813523302879585001485

theorem tailTrace_2891664 : CollatzResearch.WordTrace tailWord_2891664 prefixEnd_2891664 1484813523302879585001485 := by
  unfold tailWord_2891664
  simp only [CollatzResearch.WordTrace]
  refine ⟨52733825298001329869177023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70311767064001773158902697 52733825298001329869177023)
  ·
    refine ⟨79100737947001994803765535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52733825298001329869177023 79100737947001994803765535)
    ·
      refine ⟨118651106920502992205648303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79100737947001994803765535 118651106920502992205648303)
      ·
        refine ⟨177976660380754488308472455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118651106920502992205648303 177976660380754488308472455)
        ·
          refine ⟨266964990571131732462708683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177976660380754488308472455 266964990571131732462708683)
          ·
            refine ⟨400447485856697598694063025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266964990571131732462708683 400447485856697598694063025)
            ·
              refine ⟨300335614392523199020547269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400447485856697598694063025 300335614392523199020547269)
              ·
                refine ⟨56312927698598099816352613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 300335614392523199020547269 56312927698598099816352613)
                ·
                  refine ⟨10558673943487143715566115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56312927698598099816352613 10558673943487143715566115)
                  ·
                    refine ⟨15838010915230715573349173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10558673943487143715566115 15838010915230715573349173)
                    ·
                      refine ⟨1484813523302879585001485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15838010915230715573349173 1484813523302879585001485)
                      ·
                        rfl

theorem cell23_2891664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_2891664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891664 prefixEnd_2891664 := by exact prefixLift 2891664
  have htrace : WordTrace (prefixWord ++ tailWord_2891664) baseStart_2891664 baseEnd_2891664 := by
    simpa [prefixWord, tailWord_2891664, baseEnd_2891664] using wordTrace_append hprefix tailTrace_2891664
  have hstable : (prefixWord ++ tailWord_2891664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891664).length < 2 ^ (prefixWord ++ tailWord_2891664).sum := by decide
  have hdescent : baseEnd_2891664 < baseStart_2891664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891672 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2891672 : Nat := 118140960795 + 2891672 * 2 ^ 59
def prefixEnd_2891672 : Nat := 4983230072969 + 3 ^ 40 * 2891672 * 2
def baseEnd_2891672 : Nat := 1484817631148115553701449

theorem tailTrace_2891672 : CollatzResearch.WordTrace tailWord_2891672 prefixEnd_2891672 1484817631148115553701449 := by
  unfold tailWord_2891672
  simp only [CollatzResearch.WordTrace]
  refine ⟨52733971189986838552322635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70311961586649118069763513 52733971189986838552322635)
  ·
    refine ⟨79100956784980257828483953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52733971189986838552322635 79100956784980257828483953)
    ·
      refine ⟨59325717588735193371362965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79100956784980257828483953 59325717588735193371362965)
      ·
        refine ⟨2780893011971962189282639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59325717588735193371362965 2780893011971962189282639)
        ·
          refine ⟨4171339517957943283923959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780893011971962189282639 4171339517957943283923959)
          ·
            refine ⟨6257009276936914925885939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171339517957943283923959 6257009276936914925885939)
            ·
              refine ⟨9385513915405372388828909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257009276936914925885939 9385513915405372388828909)
              ·
                refine ⟨3519567718277014645810841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385513915405372388828909 3519567718277014645810841)
                ·
                  refine ⟨2639675788707760984358131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519567718277014645810841 2639675788707760984358131)
                  ·
                    refine ⟨3959513683061641476537197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639675788707760984358131 3959513683061641476537197)
                    ·
                      refine ⟨1484817631148115553701449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959513683061641476537197 1484817631148115553701449)
                      ·
                        rfl

theorem cell23_2891672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2891672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891672 prefixEnd_2891672 := by exact prefixLift 2891672
  have htrace : WordTrace (prefixWord ++ tailWord_2891672) baseStart_2891672 baseEnd_2891672 := by
    simpa [prefixWord, tailWord_2891672, baseEnd_2891672] using wordTrace_append hprefix tailTrace_2891672
  have hstable : (prefixWord ++ tailWord_2891672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891672).length < 2 ^ (prefixWord ++ tailWord_2891672).sum := by decide
  have hdescent : baseEnd_2891672 < baseStart_2891672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891711 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_2891711 : Nat := 118140960795 + 2891711 * 2 ^ 59
def prefixEnd_2891711 : Nat := 4983230072969 + 3 ^ 40 * 2891711 * 2
def baseEnd_2891711 : Nat := 1484837656893640901113769

theorem tailTrace_2891711 : CollatzResearch.WordTrace tailWord_2891711 prefixEnd_2891711 1484837656893640901113769 := by
  unfold tailWord_2891711
  simp only [CollatzResearch.WordTrace]
  refine ⟨105469364826832386765314987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70312909884554924510209991 105469364826832386765314987)
  ·
    refine ⟨158204047240248580147972481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105469364826832386765314987 158204047240248580147972481)
    ·
      refine ⟨118653035430186435110979361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158204047240248580147972481 118653035430186435110979361)
      ·
        refine ⟨88989776572639826333234521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118653035430186435110979361 88989776572639826333234521)
        ·
          refine ⟨66742332429479869749925891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88989776572639826333234521 66742332429479869749925891)
          ·
            refine ⟨100113498644219804624888837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66742332429479869749925891 100113498644219804624888837)
            ·
              refine ⟨18771280995791213367166657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100113498644219804624888837 18771280995791213367166657)
              ·
                refine ⟨14078460746843410025374993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18771280995791213367166657 14078460746843410025374993)
                ·
                  refine ⟨10558845560132557519031245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14078460746843410025374993 10558845560132557519031245)
                  ·
                    refine ⟨3959567085049709069636717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10558845560132557519031245 3959567085049709069636717)
                    ·
                      refine ⟨1484837656893640901113769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959567085049709069636717 1484837656893640901113769)
                      ·
                        rfl

theorem cell23_2891711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_2891711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891711 prefixEnd_2891711 := by exact prefixLift 2891711
  have htrace : WordTrace (prefixWord ++ tailWord_2891711) baseStart_2891711 baseEnd_2891711 := by
    simpa [prefixWord, tailWord_2891711, baseEnd_2891711] using wordTrace_append hprefix tailTrace_2891711
  have hstable : (prefixWord ++ tailWord_2891711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891711).length < 2 ^ (prefixWord ++ tailWord_2891711).sum := by decide
  have hdescent : baseEnd_2891711 < baseStart_2891711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891768 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 2, 4, 2]
def baseStart_2891768 : Nat := 118140960795 + 2891768 * 2 ^ 59
def prefixEnd_2891768 : Nat := 4983230072969 + 3 ^ 40 * 2891768 * 2
def baseEnd_2891768 : Nat := 1484866925290947178101007

theorem tailTrace_2891768 : CollatzResearch.WordTrace tailWord_2891768 prefixEnd_2891768 1484866925290947178101007 := by
  unfold tailWord_2891768
  simp only [CollatzResearch.WordTrace]
  refine ⟨52735721893812942750069979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70314295858417257000093305 52735721893812942750069979)
  ·
    refine ⟨79103582840719414125104969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52735721893812942750069979 79103582840719414125104969)
    ·
      refine ⟨59327687130539560593828727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79103582840719414125104969 59327687130539560593828727)
      ·
        refine ⟨88991530695809340890743091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59327687130539560593828727 88991530695809340890743091)
        ·
          refine ⟨133487296043714011336114637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88991530695809340890743091 133487296043714011336114637)
          ·
            refine ⟨50057736016392754251042989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133487296043714011336114637 50057736016392754251042989)
            ·
              refine ⟨18771651006147282844141121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50057736016392754251042989 18771651006147282844141121)
              ·
                refine ⟨14078738254610462133105841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18771651006147282844141121 14078738254610462133105841)
                ·
                  refine ⟨10559053690957846599829381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14078738254610462133105841 10559053690957846599829381)
                  ·
                    refine ⟨1979822567054596237468009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10559053690957846599829381 1979822567054596237468009)
                    ·
                      refine ⟨1484866925290947178101007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979822567054596237468009 1484866925290947178101007)
                      ·
                        rfl

theorem cell23_2891768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 4, 2].length) (baseStart_2891768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891768 prefixEnd_2891768 := by exact prefixLift 2891768
  have htrace : WordTrace (prefixWord ++ tailWord_2891768) baseStart_2891768 baseEnd_2891768 := by
    simpa [prefixWord, tailWord_2891768, baseEnd_2891768] using wordTrace_append hprefix tailTrace_2891768
  have hstable : (prefixWord ++ tailWord_2891768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891768).length < 2 ^ (prefixWord ++ tailWord_2891768).sum := by decide
  have hdescent : baseEnd_2891768 < baseStart_2891768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891801 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_2891801 : Nat := 118140960795 + 2891801 * 2 ^ 59
def prefixEnd_2891801 : Nat := 4983230072969 + 3 ^ 40 * 2891801 * 2
def baseEnd_2891801 : Nat := 1484883870152545548988355

theorem tailTrace_2891801 : CollatzResearch.WordTrace tailWord_2891801 prefixEnd_2891801 1484883870152545548988355 := by
  unfold tailWord_2891801
  simp only [CollatzResearch.WordTrace]
  refine ⟨105472647396506332136091257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70315098264337554757394171 105472647396506332136091257)
  ·
    refine ⟨79104485547379749102068443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105472647396506332136091257 79104485547379749102068443)
    ·
      refine ⟨118656728321069623653102665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79104485547379749102068443 118656728321069623653102665)
      ·
        refine ⟨88992546240802217739826999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118656728321069623653102665 88992546240802217739826999)
        ·
          refine ⟨133488819361203326609740499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88992546240802217739826999 133488819361203326609740499)
          ·
            refine ⟨200233229041804989914610749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133488819361203326609740499 200233229041804989914610749)
            ·
              refine ⟨75087460890676871217979031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200233229041804989914610749 75087460890676871217979031)
              ·
                refine ⟨112631191336015306826968547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75087460890676871217979031 112631191336015306826968547)
                ·
                  refine ⟨168946787004022960240452821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112631191336015306826968547 168946787004022960240452821)
                  ·
                    refine ⟨3959690320406788130635613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168946787004022960240452821 3959690320406788130635613)
                    ·
                      refine ⟨1484883870152545548988355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959690320406788130635613 1484883870152545548988355)
                      ·
                        rfl

theorem cell23_2891801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_2891801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891801 prefixEnd_2891801 := by exact prefixLift 2891801
  have htrace : WordTrace (prefixWord ++ tailWord_2891801) baseStart_2891801 baseEnd_2891801 := by
    simpa [prefixWord, tailWord_2891801, baseEnd_2891801] using wordTrace_append hprefix tailTrace_2891801
  have hstable : (prefixWord ++ tailWord_2891801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891801).length < 2 ^ (prefixWord ++ tailWord_2891801).sum := by decide
  have hdescent : baseEnd_2891801 < baseStart_2891801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891868 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2891868 : Nat := 118140960795 + 2891868 * 2 ^ 59
def prefixEnd_2891868 : Nat := 4983230072969 + 3 ^ 40 * 2891868 * 2
def baseEnd_2891868 : Nat := 494972757785465595616849

theorem tailTrace_2891868 : CollatzResearch.WordTrace tailWord_2891868 prefixEnd_2891868 494972757785465595616849 := by
  unfold tailWord_2891868
  simp only [CollatzResearch.WordTrace]
  refine ⟨52737545543631801289390129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70316727391509068385853505 52737545543631801289390129)
  ·
    refine ⟨39553159157723850967042597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52737545543631801289390129 39553159157723850967042597)
    ·
      refine ⟨7416217342073222056320487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39553159157723850967042597 7416217342073222056320487)
      ·
        refine ⟨11124326013109833084480731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7416217342073222056320487 11124326013109833084480731)
        ·
          refine ⟨16686489019664749626721097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11124326013109833084480731 16686489019664749626721097)
          ·
            refine ⟨12514866764748562220040823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16686489019664749626721097 12514866764748562220040823)
            ·
              refine ⟨18772300147122843330061235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12514866764748562220040823 18772300147122843330061235)
              ·
                refine ⟨28158450220684264995091853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18772300147122843330061235 28158450220684264995091853)
                ·
                  refine ⟨10559418832756599373159445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28158450220684264995091853 10559418832756599373159445)
                  ·
                    refine ⟨494972757785465595616849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10559418832756599373159445 494972757785465595616849)
                    ·
                      rfl

theorem cell23_2891868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2891868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891868 prefixEnd_2891868 := by exact prefixLift 2891868
  have htrace : WordTrace (prefixWord ++ tailWord_2891868) baseStart_2891868 baseEnd_2891868 := by
    simpa [prefixWord, tailWord_2891868, baseEnd_2891868] using wordTrace_append hprefix tailTrace_2891868
  have hstable : (prefixWord ++ tailWord_2891868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891868).length < 2 ^ (prefixWord ++ tailWord_2891868).sum := by decide
  have hdescent : baseEnd_2891868 < baseStart_2891868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891871 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_2891871 : Nat := 118140960795 + 2891871 * 2 ^ 59
def prefixEnd_2891871 : Nat := 4983230072969 + 3 ^ 40 * 2891871 * 2
def baseEnd_2891871 : Nat := 1484919813798360275113033

theorem tailTrace_2891871 : CollatzResearch.WordTrace tailWord_2891871 prefixEnd_2891871 1484919813798360275113033 := by
  unfold tailWord_2891871
  simp only [CollatzResearch.WordTrace]
  refine ⟨105475200506252734091139467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70316800337501822727426311 105475200506252734091139467)
  ·
    refine ⟨158212800759379101136709201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105475200506252734091139467 158212800759379101136709201)
    ·
      refine ⟨118659600569534325852531901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158212800759379101136709201 118659600569534325852531901)
      ·
        refine ⟨44497350213575372194699463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118659600569534325852531901 44497350213575372194699463)
        ·
          refine ⟨66746025320363058292049195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44497350213575372194699463 66746025320363058292049195)
          ·
            refine ⟨100119037980544587438073793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66746025320363058292049195 100119037980544587438073793)
            ·
              refine ⟨75089278485408440578555345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100119037980544587438073793 75089278485408440578555345)
              ·
                refine ⟨56316958864056330433916509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75089278485408440578555345 56316958864056330433916509)
                ·
                  refine ⟨21118859574021123912718691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56316958864056330433916509 21118859574021123912718691)
                  ·
                    refine ⟨31678289361031685869078037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21118859574021123912718691 31678289361031685869078037)
                    ·
                      refine ⟨1484919813798360275113033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31678289361031685869078037 1484919813798360275113033)
                      ·
                        rfl

theorem cell23_2891871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_2891871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891871 prefixEnd_2891871 := by exact prefixLift 2891871
  have htrace : WordTrace (prefixWord ++ tailWord_2891871) baseStart_2891871 baseEnd_2891871 := by
    simpa [prefixWord, tailWord_2891871, baseEnd_2891871] using wordTrace_append hprefix tailTrace_2891871
  have hstable : (prefixWord ++ tailWord_2891871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891871).length < 2 ^ (prefixWord ++ tailWord_2891871).sum := by decide
  have hdescent : baseEnd_2891871 < baseStart_2891871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891925 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_2891925 : Nat := 118140960795 + 2891925 * 2 ^ 59
def prefixEnd_2891925 : Nat := 4983230072969 + 3 ^ 40 * 2891925 * 2
def baseEnd_2891925 : Nat := 1484947541753703063837785

theorem tailTrace_2891925 : CollatzResearch.WordTrace tailWord_2891925 prefixEnd_2891925 1484947541753703063837785 := by
  unfold tailWord_2891925
  simp only [CollatzResearch.WordTrace]
  refine ⟨105477170048057101313605229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70318113365371400875736819 105477170048057101313605229)
  ·
    refine ⟨39553938768021412992601961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105477170048057101313605229 39553938768021412992601961)
    ·
      refine ⟨29665454076016059744451471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39553938768021412992601961 29665454076016059744451471)
      ·
        refine ⟨44498181114024089616677207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29665454076016059744451471 44498181114024089616677207)
        ·
          refine ⟨66747271671036134425015811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44498181114024089616677207 66747271671036134425015811)
          ·
            refine ⟨100120907506554201637523717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66747271671036134425015811 100120907506554201637523717)
            ·
              refine ⟨18772670157478912807035697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100120907506554201637523717 18772670157478912807035697)
              ·
                refine ⟨14079502618109184605276773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18772670157478912807035697 14079502618109184605276773)
                ·
                  refine ⟨2639906740895472113489395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14079502618109184605276773 2639906740895472113489395)
                  ·
                    refine ⟨3959860111343208170234093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639906740895472113489395 3959860111343208170234093)
                    ·
                      refine ⟨1484947541753703063837785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959860111343208170234093 1484947541753703063837785)
                      ·
                        rfl

theorem cell23_2891925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_2891925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891925 prefixEnd_2891925 := by exact prefixLift 2891925
  have htrace : WordTrace (prefixWord ++ tailWord_2891925) baseStart_2891925 baseEnd_2891925 := by
    simpa [prefixWord, tailWord_2891925, baseEnd_2891925] using wordTrace_append hprefix tailTrace_2891925
  have hstable : (prefixWord ++ tailWord_2891925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891925).length < 2 ^ (prefixWord ++ tailWord_2891925).sum := by decide
  have hdescent : baseEnd_2891925 < baseStart_2891925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891931 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_2891931 : Nat := 118140960795 + 2891931 * 2 ^ 59
def prefixEnd_2891931 : Nat := 4983230072969 + 3 ^ 40 * 2891931 * 2
def baseEnd_2891931 : Nat := 1484950622637630040362757

theorem tailTrace_2891931 : CollatzResearch.WordTrace tailWord_2891931 prefixEnd_2891931 1484950622637630040362757 := by
  unfold tailWord_2891931
  simp only [CollatzResearch.WordTrace]
  refine ⟨105477388886035364338323647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70318259257356909558882431 105477388886035364338323647)
  ·
    refine ⟨158216083329053046507485471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105477388886035364338323647 158216083329053046507485471)
    ·
      refine ⟨237324124993579569761228207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158216083329053046507485471 237324124993579569761228207)
      ·
        refine ⟨355986187490369354641842311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237324124993579569761228207 355986187490369354641842311)
        ·
          refine ⟨533979281235554031962763467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355986187490369354641842311 533979281235554031962763467)
          ·
            refine ⟨800968921853331047944145201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533979281235554031962763467 800968921853331047944145201)
            ·
              refine ⟨600726691389998285958108901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800968921853331047944145201 600726691389998285958108901)
              ·
                refine ⟨112636254635624678617145419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600726691389998285958108901 112636254635624678617145419)
                ·
                  refine ⟨168954381953437017925718129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112636254635624678617145419 168954381953437017925718129)
                  ·
                    refine ⟨126715786465077763444288597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168954381953437017925718129 126715786465077763444288597)
                    ·
                      refine ⟨1484950622637630040362757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 126715786465077763444288597 1484950622637630040362757)
                      ·
                        rfl

theorem cell23_2891931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_2891931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891931 prefixEnd_2891931 := by exact prefixLift 2891931
  have htrace : WordTrace (prefixWord ++ tailWord_2891931) baseStart_2891931 baseEnd_2891931 := by
    simpa [prefixWord, tailWord_2891931, baseEnd_2891931] using wordTrace_append hprefix tailTrace_2891931
  have hstable : (prefixWord ++ tailWord_2891931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891931).length < 2 ^ (prefixWord ++ tailWord_2891931).sum := by decide
  have hdescent : baseEnd_2891931 < baseStart_2891931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891959 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 2, 1, 3]
def baseStart_2891959 : Nat := 118140960795 + 2891959 * 2 ^ 59
def prefixEnd_2891959 : Nat := 4983230072969 + 3 ^ 40 * 2891959 * 2
def baseEnd_2891959 : Nat := 1484965000095955930812629

theorem tailTrace_2891959 : CollatzResearch.WordTrace tailWord_2891959 prefixEnd_2891959 1484965000095955930812629 := by
  unfold tailWord_2891959
  simp only [CollatzResearch.WordTrace]
  refine ⟨105478410129933925120342931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70318940086622616746895287 105478410129933925120342931)
  ·
    refine ⟨158217615194900887680514397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105478410129933925120342931 158217615194900887680514397)
    ·
      refine ⟨59331605698087832880192899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158217615194900887680514397 59331605698087832880192899)
      ·
        refine ⟨88997408547131749320289349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59331605698087832880192899 88997408547131749320289349)
        ·
          refine ⟨16687014102587202997554253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88997408547131749320289349 16687014102587202997554253)
          ·
            refine ⟨6257630288470201124082845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16687014102587202997554253 6257630288470201124082845)
            ·
              refine ⟨2346611358176325421531067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6257630288470201124082845 2346611358176325421531067)
              ·
                refine ⟨3519917037264488132296601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346611358176325421531067 3519917037264488132296601)
                ·
                  refine ⟨2639937777948366099222451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519917037264488132296601 2639937777948366099222451)
                  ·
                    refine ⟨3959906666922549148833677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2639937777948366099222451 3959906666922549148833677)
                    ·
                      refine ⟨1484965000095955930812629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3959906666922549148833677 1484965000095955930812629)
                      ·
                        rfl

theorem cell23_2891959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_2891959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2891959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2891959 prefixEnd_2891959 := by exact prefixLift 2891959
  have htrace : WordTrace (prefixWord ++ tailWord_2891959) baseStart_2891959 baseEnd_2891959 := by
    simpa [prefixWord, tailWord_2891959, baseEnd_2891959] using wordTrace_append hprefix tailTrace_2891959
  have hstable : (prefixWord ++ tailWord_2891959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891959).length < 2 ^ (prefixWord ++ tailWord_2891959).sum := by decide
  have hdescent : baseEnd_2891959 < baseStart_2891959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892005 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 7]
def baseStart_2892005 : Nat := 118140960795 + 2892005 * 2 ^ 59
def prefixEnd_2892005 : Nat := 4983230072969 + 3 ^ 40 * 2892005 * 2
def baseEnd_2892005 : Nat := 164998735578451416759713

theorem tailTrace_2892005 : CollatzResearch.WordTrace tailWord_2892005 prefixEnd_2892005 164998735578451416759713 := by
  unfold tailWord_2892005
  simp only [CollatzResearch.WordTrace]
  refine ⟨105480087887767274976517469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70320058591844849984344979 105480087887767274976517469)
  ·
    refine ⟨39555032957912728116194051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105480087887767274976517469 39555032957912728116194051)
    ·
      refine ⟨59332549436869092174291077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39555032957912728116194051 59332549436869092174291077)
      ·
        refine ⟨11124853019412954782679577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59332549436869092174291077 11124853019412954782679577)
        ·
          refine ⟨8343639764559716087009683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11124853019412954782679577 8343639764559716087009683)
          ·
            refine ⟨12515459646839574130514525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343639764559716087009683 12515459646839574130514525)
            ·
              refine ⟨4693297367564840298942947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12515459646839574130514525 4693297367564840298942947)
              ·
                refine ⟨7039946051347260448414421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693297367564840298942947 7039946051347260448414421)
                ·
                  refine ⟨164998735578451416759713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7039946051347260448414421 164998735578451416759713)
                  ·
                    rfl

theorem cell23_2892005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_2892005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892005 prefixEnd_2892005 := by exact prefixLift 2892005
  have htrace : WordTrace (prefixWord ++ tailWord_2892005) baseStart_2892005 baseEnd_2892005 := by
    simpa [prefixWord, tailWord_2892005, baseEnd_2892005] using wordTrace_append hprefix tailTrace_2892005
  have hstable : (prefixWord ++ tailWord_2892005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892005).length < 2 ^ (prefixWord ++ tailWord_2892005).sum := by decide
  have hdescent : baseEnd_2892005 < baseStart_2892005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892025 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 4, 5, 2]
def baseStart_2892025 : Nat := 118140960795 + 2892025 * 2 ^ 59
def prefixEnd_2892025 : Nat := 4983230072969 + 3 ^ 40 * 2892025 * 2
def baseEnd_2892025 : Nat := 1484998889819152672587325

theorem tailTrace_2892025 : CollatzResearch.WordTrace tailWord_2892025 prefixEnd_2892025 1484998889819152672587325 := by
  unfold tailWord_2892025
  simp only [CollatzResearch.WordTrace]
  refine ⟨105480817347694818392245529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70320544898463212261497019 105480817347694818392245529)
  ·
    refine ⟨79110613010771113794184147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105480817347694818392245529 79110613010771113794184147)
    ·
      refine ⟨118665919516156670691276221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79110613010771113794184147 118665919516156670691276221)
      ·
        refine ⟨44499719818558751509228583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118665919516156670691276221 44499719818558751509228583)
        ·
          refine ⟨66749579727838127263842875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44499719818558751509228583 66749579727838127263842875)
          ·
            refine ⟨100124369591757190895764313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66749579727838127263842875 100124369591757190895764313)
            ·
              refine ⟨75093277193817893171823235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100124369591757190895764313 75093277193817893171823235)
              ·
                refine ⟨112639915790726839757734853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75093277193817893171823235 112639915790726839757734853)
                ·
                  refine ⟨21119984210761282454575285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112639915790726839757734853 21119984210761282454575285)
                  ·
                    refine ⟨1979998519758870230116433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21119984210761282454575285 1979998519758870230116433)
                    ·
                      refine ⟨1484998889819152672587325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1979998519758870230116433 1484998889819152672587325)
                      ·
                        rfl

theorem cell23_2892025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_2892025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892025 prefixEnd_2892025 := by exact prefixLift 2892025
  have htrace : WordTrace (prefixWord ++ tailWord_2892025) baseStart_2892025 baseEnd_2892025 := by
    simpa [prefixWord, tailWord_2892025, baseEnd_2892025] using wordTrace_append hprefix tailTrace_2892025
  have hstable : (prefixWord ++ tailWord_2892025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892025).length < 2 ^ (prefixWord ++ tailWord_2892025).sum := by decide
  have hdescent : baseEnd_2892025 < baseStart_2892025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2892035 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 2, 5]
def baseStart_2892035 : Nat := 118140960795 + 2892035 * 2 ^ 59
def prefixEnd_2892035 : Nat := 4983230072969 + 3 ^ 40 * 2892035 * 2
def baseEnd_2892035 : Nat := 495001341541899211154093

theorem tailTrace_2892035 : CollatzResearch.WordTrace tailWord_2892035 prefixEnd_2892035 495001341541899211154093 := by
  unfold tailWord_2892035
  simp only [CollatzResearch.WordTrace]
  refine ⟨105481182077658590100109559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70320788051772393400073039 105481182077658590100109559)
  ·
    refine ⟨158221773116487885150164339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105481182077658590100109559 158221773116487885150164339)
    ·
      refine ⟨237332659674731827725246509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158221773116487885150164339 237332659674731827725246509)
      ·
        refine ⟨88999747378024435396967441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237332659674731827725246509 88999747378024435396967441)
        ·
          refine ⟨66749810533518326547725581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88999747378024435396967441 66749810533518326547725581)
          ·
            refine ⟨25031178950069372455397093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66749810533518326547725581 25031178950069372455397093)
            ·
              refine ⟨4693346053138007335386955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25031178950069372455397093 4693346053138007335386955)
              ·
                refine ⟨7040019079707011003080433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693346053138007335386955 7040019079707011003080433)
                ·
                  refine ⟨5280014309780258252310325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7040019079707011003080433 5280014309780258252310325)
                  ·
                    refine ⟨495001341541899211154093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5280014309780258252310325 495001341541899211154093)
                    ·
                      rfl

theorem cell23_2892035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 5].length) (baseStart_2892035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2892035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2892035 prefixEnd_2892035 := by exact prefixLift 2892035
  have htrace : WordTrace (prefixWord ++ tailWord_2892035) baseStart_2892035 baseEnd_2892035 := by
    simpa [prefixWord, tailWord_2892035, baseEnd_2892035] using wordTrace_append hprefix tailTrace_2892035
  have hstable : (prefixWord ++ tailWord_2892035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2892035).length < 2 ^ (prefixWord ++ tailWord_2892035).sum := by decide
  have hdescent : baseEnd_2892035 < baseStart_2892035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2892035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
